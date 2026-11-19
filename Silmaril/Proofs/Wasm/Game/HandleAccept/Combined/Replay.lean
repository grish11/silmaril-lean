module

public import Silmaril.Wasm.Game.HandleAccept.Combined.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.Replay

/-!
# Combined acceptance from a replayed export call

* `cRunB W okR bad x σ t`: simulate the combined host along `t` from the store `σ`: successful
  fresh writes whose handles are not `bad` (`WStep.writeOk`), reads passing the Boolean check
  `okR σ q a` of the **current** store (`CStep.read`), accepts of defined handles and export
  calls; `none` when stuck, else whether `x` is accepted. `run_of_cRunB`: with a sound check,
  a simulated trace has a run of the combined host (trapping reads).
* `consOkB`: the Boolean check of cons reader answers, sound for `consR` (`consOkB_sound`).
* `combAsk`, `combAns`: the combined cons decoders on recorded moves;
  **`mem_combLang_of_replay`**.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Combined

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Verify Silmaril.Wasm.Resource
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Writers Silmaril.Wasm.Game.HandleAccept.Combined
  Silmaril.Accept Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Proofs.Wasm.Game.HandleAccept.Replay
open Silmaril.Wasm.Numerics (Profile)

/-! ## Simulating the combined host -/

section Sim

variable {Op Q A H X : Type} [DecidableEq H] [DecidableEq X]

/-- **Simulate the combined host** (see the module docstring). -/
def cRunB (W : Writer Op X) (okR : Env H X → Q → A → Bool) (bad : H → Bool) (x : X) :
    Env H X → List (CEv Op H Q A) → Option Bool
  | _, [] => some false
  | σ, .w (.write op args r) :: es =>
    match W.built σ op args with
    | some t =>
      if bad r = false ∧ σ r = none then cRunB W okR bad x (Function.update σ r (some t)) es
      else none
    | none => none
  | σ, .w (.accept h) :: es =>
    match σ h with
    | some t => (cRunB W okR bad x σ es).map fun b => decide (t = x) || b
    | none => none
  | σ, .w .enter :: es => cRunB W okR bad x σ es
  | σ, .r q a :: es => if okR σ q a then cRunB W okR bad x σ es else none
  | _, _ :: _ => none

theorem run_of_cRunB (W : Writer Op X) (R : Reader Q A H X) {okR : Env H X → Q → A → Bool}
    (hR : ∀ σ q a, okR σ q a = true → R.valid σ q ∧ R.ok σ q a) {bad : H → Bool} {x : X}
    {pol : Policy H} (hbad : ∀ r, pol.sentinel = some r → bad r = true) :
    ∀ (t : List (CEv Op H Q A)) (σ : Env H X) (B : Set X) (b : Bool),
      cRunB W okR bad x σ t = some b →
      ∃ s S, (combined W R pol .trap).Run ⟨σ, B, .live⟩ t s S ∧ (b = true → x ∈ S)
  | [], _, _, b, h => by
    simp only [cRunB, Option.some.injEq] at h
    subst h
    exact ⟨_, ∅, .nil _, by simp⟩
  | .w (.write op args r) :: es, σ, B, b, h => by
    simp only [cRunB] at h
    split at h
    · rename_i t ht
      split at h
      · rename_i hfr
        obtain ⟨s, S, hr, hS⟩ := run_of_cRunB W R hR hbad es _ (insert t B) b h
        have hne : pol.sentinel ≠ some r := fun hs => by
          have := hbad r hs
          rw [hfr.1] at this
          cases this
        refine ⟨s, ∅ ∪ S, .cons (CStep.w (WStep.writeOk ht ⟨hne, Or.inl hfr.2⟩
          fun _ h => by cases h)) hr, fun hb => Or.inr (hS hb)⟩
      · cases h
    · cases h
  | .w (.accept h') :: es, σ, B, b, h => by
    simp only [cRunB] at h
    split at h
    · rename_i t ht
      obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨s, S, hr, hS⟩ := run_of_cRunB W R hR hbad es σ B b' hb'
      refine ⟨s, {t} ∪ S, .cons (CStep.w (WStep.acceptOk ht)) hr, ?_⟩
      intro hb
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hb
      rcases hb with rfl | hb
      · exact Or.inl rfl
      · exact Or.inr (hS hb)
    · cases h
  | .w .enter :: es, σ, B, b, h => by
    simp only [cRunB] at h
    obtain ⟨s, S, hr, hS⟩ := run_of_cRunB W R hR hbad es σ B b h
    exact ⟨s, ∅ ∪ S, .cons (CStep.w WStep.enter) hr, fun hb => Or.inr (hS hb)⟩
  | .r q a :: es, σ, B, b, h => by
    simp only [cRunB] at h
    split at h
    · rename_i hok
      obtain ⟨hv, ha⟩ := hR σ q a hok
      obtain ⟨s, S, hr, hS⟩ := run_of_cRunB W R hR hbad es σ B b h
      have hans : answers R .trap σ q = some {a | R.ok σ q a} := by
        unfold answers
        split
        · rfl
        · contradiction
      exact ⟨s, ∅ ∪ S, .cons (CStep.read hans ha) hr, fun hb => Or.inr (hS hb)⟩
    · cases h
  | .w (.acceptErr _ _) :: _, _, _, _, h => by cases h
  | .w .acceptAll :: _, _, _, _, h => by cases h
  | .w (.acceptBatch _) :: _, _, _, _, h => by cases h

end Sim

/-! ## Cons reader answers -/

/-- The Boolean check of a cons reader answer in the store `σ`. -/
def consOkB (σ : Env (BitVec 32) (SExp2 (BitVec 64))) :
    ConsQ (BitVec 32) → ConsA (BitVec 64) (BitVec 32) → Bool
  | .kind h, .kind k => match σ h with
    | some x => decide (k = consKind x)
    | none => false
  | .atom h, .atom a => decide (σ h = some (.atom a))
  | .car h, .handle h' => match σ h with
    | some (.cons x _) => decide (σ h' = some x)
    | _ => false
  | .cdr h, .handle h' => match σ h with
    | some (.cons _ y) => decide (σ h' = some y)
    | _ => false
  | _, _ => false

theorem consOkB_sound (σ : Env (BitVec 32) (SExp2 (BitVec 64))) (q : ConsQ (BitVec 32))
    (a : ConsA (BitVec 64) (BitVec 32)) (h : consOkB σ q a = true) :
    (consR (BitVec 64) (BitVec 32)).valid σ q ∧ (consR (BitVec 64) (BitVec 32)).ok σ q a := by
  cases q <;> cases a <;> simp only [consOkB] at h <;> try cases h
  all_goals first
    | (rename_i h₀ k; split at h
       · rename_i x hx
         exact ⟨⟨x, hx⟩, ⟨x, hx, of_decide_eq_true h⟩⟩
       · cases h)
    | (have h' := of_decide_eq_true h; exact ⟨⟨_, h'⟩, h'⟩)
    | (split at h
       · rename_i x y hx
         exact ⟨⟨x, y, hx⟩, ⟨x, y, hx, of_decide_eq_true h⟩⟩
       · cases h)

/-! ## Recorded moves -/

/-- `combDecAsk` on a recorded import call. -/
def combAsk (ix : CombImports) (h : Nat) (args : List Val) : Option ConsCEv :=
  if h = ix.accept then (i32Arg args).map fun a => .w (.accept a) else none

/-- `combDecAns` on a recorded answer. -/
def combAns (ix : CombImports) (h : Nat) (args : List Val) (b : Behaviour Val) :
    Option ConsCEv := do
  let r ← (bValsG b).bind i32Res
  if h = ix.word then return .w (.write (.atom (← i64Arg args)) [] r)
  else if h = ix.nil then
    if args = [] then return .w (.write .nil [] r) else none
  else if h = ix.cons then return .w (.write .cons (← i32Pair args) r)
  else if h = ix.kind then return .r (.kind (← i32Arg args)) (kindAns r)
  else if h = ix.car then return .r (.car (← i32Arg args)) (.handle r)
  else if h = ix.cdr then return .r (.cdr (← i32Arg args)) (.handle r)
  else none

variable {I : ScalarInstance}

theorem combDecAsk_eq (ix : CombImports) (e : I.E.Op) :
    combDecAsk ix e = combAsk ix e.1.val e.2.1 :=
  rfl

theorem combDecAns_eq (ix : CombImports) (e : I.E.Op) (v : I.E.Ar e) :
    combDecAns ix e v =
      combAns ix e.1.val e.2.1 (Answer.toBehaviour (ft := I.imports.get e.1) v) := by
  cases v <;> rfl

/-- **Combined acceptance from a replay**: if the simulation of the decoded replay of an export
call from the empty store (fresh handles never `bad`, reads checked against the current store)
accepts `x`, and the policy's sentinel (if any) is `bad`, then `x` is in the module's combined
language, for every profile admitting the deterministic steps of the replay interpreter. -/
theorem mem_combLang_of_replay {m : Module} (hm : (instance? m).isSome = true) {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
    (ix : CombImports) {pol : Policy (BitVec 32)} {bad : BitVec 32 → Bool}
    (hbad : ∀ r, pol.sentinel = some r → bad r = true) (sc : Script) (fuel n : Nat)
    (j : Fin (instOf m).exports.length) (k : Nat) {x : SExp2 (BitVec 64)}
    (hrun : cRunB (consW (BitVec 64)) consOkB bad x Env.empty
      (rdecG (some (.w .enter)) (combAsk ix) (combAns ix) []
        (replayExport (instOf m) sc fuel n j k)) = some true) :
    x ∈ moduleCombLang P m ix pol := by
  have hT := rdecG_mem_handleTraces hm hP (some (.w .enter)) (combDecAsk ix) (combDecAns ix)
    (combAsk ix) (combAns ix) (combDecAsk_eq ix) (combDecAns_eq ix) sc fuel n j k
  obtain ⟨s, S, hr, hS⟩ := run_of_cRunB (consW (BitVec 64)) (consR (BitVec 64) (BitVec 32))
    consOkB_sound hbad _ Env.empty ∅ true hrun
  exact Set.mem_biUnion hT ⟨s, S, hr, hS rfl⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Combined
