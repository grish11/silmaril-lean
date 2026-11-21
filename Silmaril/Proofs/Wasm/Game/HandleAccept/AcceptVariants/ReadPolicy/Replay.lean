module

public import Silmaril.Wasm.Game.HandleAccept.AcceptVariants.ReadPolicy.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.Replay

/-!
# Reader acceptance under a read policy from a replayed export call

`run_of_revOkPol`: a trace whose reads pass a Boolean check of **allowed** answers under the
read policy `pol` (`answers R pol ρ`: correct answers of valid queries, the policy's answers
of invalid ones) has a reader run in `ρ`; `mem_errLang_of_replay` for the cons reader with
error codes.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.ReadPolicy

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Verify Silmaril.Wasm.Resource
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.ReadPolicy Silmaril.Accept Silmaril.Accept.Handle
  Silmaril.Formats Silmaril.Formats.Api Silmaril.Proofs.Wasm.Game.HandleAccept.Replay
open Silmaril.Wasm.Numerics (Profile)

variable {Q A H X : Type}

theorem allowed_of_ok {R : Reader Q A H X} {pol : OnBadRead Q A} {ρ : Env H X} {q : Q} {a : A}
    (hv : R.valid ρ q) (hok : R.ok ρ q a) : ∃ S, answers R pol ρ q = some S ∧ a ∈ S :=
  ⟨{a | R.ok ρ q a}, by unfold answers; simp [hv], hok⟩

theorem allowed_of_bad {R : Reader Q A H X} {pol : OnBadRead Q A} {ρ : Env H X} {q : Q}
    {a : A} {S : Set A} (hv : ¬ R.valid ρ q) (hb : badAnswers pol q = some S) (ha : a ∈ S) :
    ∃ S, answers R pol ρ q = some S ∧ a ∈ S :=
  ⟨S, by unfold answers; simp [hv, hb], ha⟩

theorem run_of_revOkPol [DecidableEq H] (R : Reader Q A H X) {ρ : Env H X}
    {pol : OnBadRead Q A} {okR : Q → A → Bool} {okA : H → Bool}
    (hR : ∀ q a, okR q a = true → ∃ S, answers R pol ρ q = some S ∧ a ∈ S)
    (hA : ∀ h, okA h = true → (ρ h).isSome = true) {oa : OnInvalid} :
    ∀ t : List (REv Q A H), t.all (revOkB okR okA) = true →
      ∃ B, (reader R pol oa ρ).Run .live t .live B ∧
        ∀ h x, t.any (revAcc h) = true → ρ h = some x → x ∈ B
  | [], _ => ⟨∅, .nil _, fun _ _ h => by simp at h⟩
  | e :: t, hall => by
    simp only [List.all_cons, Bool.and_eq_true] at hall
    obtain ⟨B, hr, hB⟩ := run_of_revOkPol R hR hA t hall.2
    cases e with
    | read q a =>
      obtain ⟨S, hS, ha⟩ := hR q a hall.1
      refine ⟨∅ ∪ B, .cons (RStep.read hS ha) hr, fun h x hh hx => ?_⟩
      simp only [List.any_cons, revAcc, Bool.false_or] at hh
      exact Or.inr (hB h x hh hx)
    | accept h' =>
      obtain ⟨t₀, ht₀⟩ := Option.isSome_iff_exists.1 (hA h' hall.1)
      refine ⟨{t₀} ∪ B, .cons (RStep.acceptOk ht₀) hr, fun h x hh hx => ?_⟩
      simp only [List.any_cons, revAcc, Bool.or_eq_true, decide_eq_true_eq] at hh
      rcases hh with rfl | hh
      · rw [ht₀] at hx
        cases hx
        exact Or.inl rfl
      · exact Or.inr (hB h x hh hx)
    | enter =>
      refine ⟨∅ ∪ B, .cons RStep.enter hr, fun h x hh hx => ?_⟩
      simp only [List.any_cons, revAcc, Bool.false_or] at hh
      exact Or.inr (hB h x hh hx)

/-- `consDecAsk` on a recorded import call. -/
def cAsk (ix : ConsImports) (h : Nat) (args : List Val) : Option ConsEv :=
  if h = ix.accept then (i32Arg args).map .accept else none

/-- `errDecAns` on a recorded answer. -/
def errAns (ix : ConsImports) (h : Nat) (args : List Val) (b : Behaviour Val) :
    Option ConsEv := do
  let a ← i32Arg args
  let vs ← bValsG b
  if h = ix.kind then return .read (.kind a) (kindAns (← i32Res vs))
  else if h = ix.car then return .read (.car a) (carAns (← i32Res vs))
  else if h = ix.cdr then return .read (.cdr a) (carAns (← i32Res vs))
  else if h = ix.word then return .read (.atom a) (.atom (← i64Res vs))
  else none

theorem errDecAns_eq {I : ScalarInstance} (ix : ConsImports) (e : I.E.Op) (v : I.E.Ar e) :
    errDecAns ix e v = errAns ix e.1.val e.2.1 (Answer.toBehaviour (ft := I.imports.get e.1) v) := by
  cases v <;> rfl

/-- **Reader acceptance under a read policy from a replay.** -/
theorem mem_errLang_of_replay {m : Module} (hm : (instance? m).isSome = true) {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
    (ix : ConsImports) (pol : OnBadRead (ConsQ (BitVec 32)) (ConsA (BitVec 64) (BitVec 32)))
    (oa : OnInvalid) {Envs : Set (Env (BitVec 32) (SExp2 (BitVec 64)))}
    {ρ : Env (BitVec 32) (SExp2 (BitVec 64))} (hρ : ρ ∈ Envs)
    {okR : ConsQ (BitVec 32) → ConsA (BitVec 64) (BitVec 32) → Bool} {okA : BitVec 32 → Bool}
    (hR : ∀ q a, okR q a = true →
      ∃ S, answers (consR (BitVec 64) (BitVec 32)) pol ρ q = some S ∧ a ∈ S)
    (hA : ∀ h, okA h = true → (ρ h).isSome = true)
    (sc : Script) (fuel n : Nat) (j : Fin (instOf m).exports.length) (k : Nat) (h : BitVec 32)
    {x : SExp2 (BitVec 64)} (hx : ρ h = some x)
    (hall : (rdecG (some .enter) (cAsk ix) (errAns ix) [] (replayExport (instOf m) sc fuel n j k)).all
      (revOkB okR okA) = true)
    (hacc : (rdecG (some .enter) (cAsk ix) (errAns ix) [] (replayExport (instOf m) sc fuel n j k)).any
      (revAcc h) = true) :
    x ∈ moduleErrLang P m ix pol oa Envs := by
  have hT := rdecG_mem_handleTraces hm hP (some .enter) (consDecAsk ix) (errDecAns ix)
    (cAsk ix) (errAns ix) (fun _ => rfl) (errDecAns_eq ix) sc fuel n j k
  obtain ⟨B, hrun, hB⟩ := run_of_revOkPol (consR (BitVec 64) (BitVec 32)) hR hA (oa := oa) _ hall
  exact Set.mem_iUnion.2 ⟨⟨ρ, hρ⟩, Set.mem_biUnion hT ⟨.live, B, hrun, hB h x hacc hx⟩⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.ReadPolicy
