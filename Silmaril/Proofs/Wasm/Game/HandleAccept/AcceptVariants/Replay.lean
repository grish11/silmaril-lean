module

public import Silmaril.Wasm.Game.HandleAccept.AcceptVariants.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.Replay

/-!
# Writer acceptance with accept variants from a replayed export call

* `wxRunB W sent x σ D B t`: simulate the writer host (store semantics) along `t`, with the
  constructed trees `D` and the current batch `B` as lists: a write returning the sentinel
  `sent` fails (`WStep.writeFail`, for a valid call), any other write must return a fresh
  handle (`WStep.writeOk`); `accept` and `accept_err` answered `true` need a defined handle,
  `accept_err` answered `false` an undefined one; `acceptAll` accepts `D`, `acceptBatch keep`
  accepts `B` if `keep` and starts a new batch. `none` when stuck, else whether `x` is accepted.
  `run_of_wxRunB`: a simulated trace has a run of the writer host.
* `consXAsk`, `consXAns`: the decoders on recorded moves; **`mem_consXLang_of_replay`**.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Verify Silmaril.Wasm.Resource
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Writers Silmaril.Wasm.Game.HandleAccept.AcceptVariants
  Silmaril.Accept Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Proofs.Wasm.Game.HandleAccept.Replay
open Silmaril.Wasm.Numerics (Profile)

section Sim

variable {Op H X : Type} [DecidableEq H] [DecidableEq X]

/-- **Simulate the writer host with accept variants** (see the module docstring). -/
def wxRunB (W : Writer Op X) (sent : Option H) (x : X) :
    Env H X → List X → List X → List (WEv Op H) → Option Bool
  | _, _, _, [] => some false
  | σ, D, B, .write op args r :: es =>
    match W.built σ op args with
    | some t =>
      if sent = some r then wxRunB W sent x σ D B es
      else if σ r = none then wxRunB W sent x (Function.update σ r (some t)) (t :: D) (t :: B) es
      else none
    | none => none
  | σ, D, B, .accept h :: es =>
    match σ h with
    | some t => (wxRunB W sent x σ D B es).map fun b => decide (t = x) || b
    | none => none
  | σ, D, B, .acceptErr h true :: es =>
    match σ h with
    | some t => (wxRunB W sent x σ D B es).map fun b => decide (t = x) || b
    | none => none
  | σ, D, B, .acceptErr h false :: es =>
    match σ h with
    | some _ => none
    | none => wxRunB W sent x σ D B es
  | σ, D, B, .acceptAll :: es => (wxRunB W sent x σ D B es).map fun b => decide (x ∈ D) || b
  | σ, D, B, .acceptBatch k :: es =>
    (wxRunB W sent x σ D [] es).map fun b => (k && decide (x ∈ B)) || b
  | σ, D, B, .enter :: es => wxRunB W sent x σ D B es

theorem run_of_wxRunB (W : Writer Op X) {sent : Option H} {x : X} {pol : Policy H}
    (hsent : pol.sentinel = sent) :
    ∀ (t : List (WEv Op H)) (σ : Env H X) (D B : List X) (Bs : Set X) (b : Bool),
      (∀ y ∈ D, y ∈ σ.range) → (∀ y ∈ B, y ∈ Bs) → wxRunB W sent x σ D B t = some b →
      ∃ s S, (writer W pol).Run ⟨σ, Bs, .live⟩ t s S ∧ (b = true → x ∈ S)
  | [], _, _, _, _, b, _, _, h => by
    simp only [wxRunB, Option.some.injEq] at h
    subst h
    exact ⟨_, ∅, .nil _, by simp⟩
  | .write op args r :: es, σ, D, B, Bs, b, hD, hB, h => by
    simp only [wxRunB] at h
    split at h
    · rename_i t ht
      split at h
      · rename_i hs
        obtain ⟨s, S, hr, hS⟩ := run_of_wxRunB W hsent es σ D B Bs b hD hB h
        exact ⟨s, ∅ ∪ S, .cons (WStep.writeFail (hsent.trans hs) (.inl (by simp [ht]))) hr,
          fun hb => Or.inr (hS hb)⟩
      · split at h
        · rename_i hs hfr
          have hD' : ∀ y ∈ t :: D, y ∈ Env.range (Function.update σ r (some t)) := by
            intro y hy
            rcases List.mem_cons.1 hy with rfl | hy
            · exact ⟨r, by simp⟩
            · obtain ⟨h', hh'⟩ := hD y hy
              have hne : h' ≠ r := fun he => by rw [he, hfr] at hh'; cases hh'
              exact ⟨h', by simp [Function.update_of_ne hne, hh']⟩
          have hB' : ∀ y ∈ t :: B, y ∈ insert t Bs := by
            intro y hy
            rcases List.mem_cons.1 hy with rfl | hy
            · exact Set.mem_insert _ _
            · exact Set.mem_insert_of_mem _ (hB y hy)
          obtain ⟨s, S, hr, hS⟩ := run_of_wxRunB W hsent es _ _ _ _ b hD' hB' h
          have hne : pol.sentinel ≠ some r := by rw [hsent]; exact hs
          exact ⟨s, ∅ ∪ S, .cons (WStep.writeOk ht ⟨hne, Or.inl hfr⟩ fun _ h => by cases h) hr,
            fun hb => Or.inr (hS hb)⟩
        · cases h
    · cases h
  | .accept h' :: es, σ, D, B, Bs, b, hD, hB, h => by
    simp only [wxRunB] at h
    split at h
    · rename_i t ht
      obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨s, S, hr, hS⟩ := run_of_wxRunB W hsent es σ D B Bs b' hD hB hb'
      refine ⟨s, {t} ∪ S, .cons (WStep.acceptOk ht) hr, fun hb => ?_⟩
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hb
      rcases hb with rfl | hb
      · exact Or.inl rfl
      · exact Or.inr (hS hb)
    · cases h
  | .acceptErr h' true :: es, σ, D, B, Bs, b, hD, hB, h => by
    simp only [wxRunB] at h
    split at h
    · rename_i t ht
      obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨s, S, hr, hS⟩ := run_of_wxRunB W hsent es σ D B Bs b' hD hB hb'
      refine ⟨s, {t} ∪ S, .cons (WStep.acceptErrOk ht) hr, fun hb => ?_⟩
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hb
      rcases hb with rfl | hb
      · exact Or.inl rfl
      · exact Or.inr (hS hb)
    · cases h
  | .acceptErr h' false :: es, σ, D, B, Bs, b, hD, hB, h => by
    simp only [wxRunB] at h
    split at h
    · cases h
    · rename_i ht
      obtain ⟨s, S, hr, hS⟩ := run_of_wxRunB W hsent es σ D B Bs b hD hB h
      exact ⟨s, ∅ ∪ S, .cons (WStep.acceptErrBad ht) hr, fun hb => Or.inr (hS hb)⟩
  | .acceptAll :: es, σ, D, B, Bs, b, hD, hB, h => by
    simp only [wxRunB] at h
    obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨s, S, hr, hS⟩ := run_of_wxRunB W hsent es σ D B Bs b' hD hB hb'
    refine ⟨s, σ.range ∪ S, .cons WStep.acceptAll hr, fun hb => ?_⟩
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hb
    rcases hb with hb | hb
    · exact Or.inl (hD x hb)
    · exact Or.inr (hS hb)
  | .acceptBatch k :: es, σ, D, B, Bs, b, hD, hB, h => by
    simp only [wxRunB] at h
    obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨s, S, hr, hS⟩ := run_of_wxRunB W hsent es σ D [] ∅ b' hD (by simp) hb'
    refine ⟨s, (if k then Bs else ∅) ∪ S, .cons (WStep.acceptBatch k) hr, fun hb => ?_⟩
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hb
    rcases hb with ⟨rfl, hb⟩ | hb
    · exact Or.inl (by simpa using hB x hb)
    · exact Or.inr (hS hb)
  | .enter :: es, σ, D, B, Bs, b, hD, hB, h => by
    simp only [wxRunB] at h
    obtain ⟨s, S, hr, hS⟩ := run_of_wxRunB W hsent es σ D B Bs b hD hB h
    exact ⟨s, ∅ ∪ S, .cons WStep.enter hr, fun hb => Or.inr (hS hb)⟩

end Sim

/-! ## Recorded moves -/

/-- `consXDecAsk` on a recorded import call. -/
def consXAsk (ix : ConsXImports) (h : Nat) (args : List Val) : Option ConsWEv :=
  if ix.accept = some h then (i32Arg args).map .accept
  else if ix.acceptAll = some h then (if args = [] then some .acceptAll else none)
  else if ix.acceptBatch = some h then (i32Arg args).map fun b => .acceptBatch (b != 0)
  else none

/-- `consXDecAns` on a recorded answer. -/
def consXAns (ix : ConsXImports) (h : Nat) (args : List Val) (b : Behaviour Val) :
    Option ConsWEv := do
  let r ← (bValsG b).bind i32Res
  if ix.acceptErr = some h then return .acceptErr (← i32Arg args) (r == 0)
  else if h = ix.word then return .write (.atom (← i64Arg args)) [] r
  else if h = ix.nil then
    if args = [] then return .write .nil [] r else none
  else if h = ix.cons then return .write .cons (← i32Pair args) r
  else none

variable {I : ScalarInstance}

theorem consXDecAsk_eq (ix : ConsXImports) (e : I.E.Op) :
    consXDecAsk ix e = consXAsk ix e.1.val e.2.1 :=
  rfl

theorem consXDecAns_eq (ix : ConsXImports) (e : I.E.Op) (v : I.E.Ar e) :
    consXDecAns ix e v =
      consXAns ix e.1.val e.2.1 (Answer.toBehaviour (ft := I.imports.get e.1) v) := by
  cases v <;> rfl

/-- **Writer acceptance with accept variants from a replay**: if the simulation of the decoded
replay of an export call from the empty store accepts `x`, with the policy's sentinel `sent`,
then `x` is in the module's writer language, for every profile admitting the deterministic
steps of the replay interpreter. -/
theorem mem_consXLang_of_replay {m : Module} (hm : (instance? m).isSome = true) {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
    (ix : ConsXImports) {pol : Policy (BitVec 32)} (sc : Script) (fuel n : Nat)
    (j : Fin (instOf m).exports.length) (k : Nat) {x : SExp2 (BitVec 64)}
    (hrun : wxRunB (consW (BitVec 64)) pol.sentinel x Env.empty [] []
      (rdecG (some .enter) (consXAsk ix) (consXAns ix) []
        (replayExport (instOf m) sc fuel n j k)) = some true) :
    x ∈ moduleConsXLang P m ix pol := by
  have hT := rdecG_mem_handleTraces hm hP (some .enter) (consXDecAsk ix) (consXDecAns ix)
    (consXAsk ix) (consXAns ix) (consXDecAsk_eq ix) (consXDecAns_eq ix) sc fuel n j k
  obtain ⟨s, S, hr, hS⟩ := run_of_wxRunB (consW (BitVec 64)) rfl _ Env.empty [] [] ∅ true
    (by simp) (by simp) hrun
  exact Set.mem_biUnion hT ⟨s, S, hr, hS rfl⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants
