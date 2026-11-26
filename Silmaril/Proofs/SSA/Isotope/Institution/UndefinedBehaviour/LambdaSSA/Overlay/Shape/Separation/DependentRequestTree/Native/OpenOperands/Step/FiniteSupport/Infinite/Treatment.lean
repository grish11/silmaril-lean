module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Infinite.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Infinite.Replay

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Infinite

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open CFG.Dependent (Packet)
open Syntax (Payload StatePrimitives)

universe u v w

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ}
  {A : Syntax.Ty} {R T : List Syntax.Ty} {σ : Type v} {τ : Type w}
  {g : Table S R} {h : Table S T} {a : Payload (R.get g.entry)} {b : Payload (T.get h.entry)}
  {prim : StatePrimitives Φ σ} {p : Packet R} {q : Packet T} {s : σ}
  {rows : List (RunRow Φ σ)} {stop : RunStop σ}

variable [DecidableEq Φ] [DecidableEq σ]

private theorem missing_reply (support : RunSupport σ s) (input : Payload A)
    (incoming : ∀ row ∈ rows, row.incoming ∈ support.values)
    (f : Φ) (arg : Payload (instrSrc f)) (t : σ) (covered : t ∈ support.values)
    (absent : ¬ ∃ reply, (⟨f, arg, t, reply⟩ : RunRow Φ σ) ∈ rows) :
    (support.witness input rows).interpreter f arg (support.code t) = .diverge := by
  let query : InterpreterScript.Query Φ support.values.length := ⟨f, arg, support.code t⟩
  change ((rows.map (RunRow.encode support)).findSome? (InterpreterScript.Row.lookup query)).getD .diverge = _
  have noneFound : (rows.map (RunRow.encode support)).findSome? (InterpreterScript.Row.lookup query) = none := by
    apply List.findSome?_eq_none_iff.mpr
    intro row mem
    obtain ⟨original, listed, rfl⟩ := List.mem_map.mp mem
    have different : (original.encode support).1 ≠ query := by
      intro same
      have keys := congrArg InterpreterScript.Query.key same
      have supported := incoming original listed
      obtain ⟨op, value, store, reply⟩ := original
      change (op, value.val, support.code store) = (f, arg.val, support.code t) at keys
      obtain ⟨rfl, rest⟩ := Prod.mk.inj keys
      obtain ⟨arguments, codes⟩ := Prod.mk.inj rest
      have sameArg : value = arg := Subtype.ext arguments
      have sameStore : store = t := (support.embed_code supported).symm.trans
        ((congrArg support.embed codes).trans (support.embed_code covered))
      subst value
      subst store
      exact absent ⟨reply, listed⟩
    simp [InterpreterScript.Row.lookup, different]
  rw [noneFound]
  rfl

theorem treatment (finite : FiniteRun h b prim q s rows stop)
    (run : GuardedReplay g a prim p s) (input : Payload A) :
    let support := RunSupport.ofRows s rows
    run.Treatment rows support (support.witness input rows).interpreter := by
  classical
  let support := RunSupport.ofRows s rows
  let w := support.witness input rows
  have returned := RunSupport.returned_ofRows s rows
  have incoming := (finite.supported support support.initial_mem returned).1
  have sameScript := (finite.reconstructs input).2
  have recorded (i : Nat) (known : run.listed rows i) :
      (run.point (i + 1)).2 ∈ support.values ∧ run.mappedStep support.code w.interpreter i := by
    obtain ⟨f, arg, next, value, head, answer, dest⟩ := request_view run i
    obtain ⟨reply, mem⟩ := show ∃ reply, (⟨f, arg, (run.point i).2, reply⟩ : RunRow Φ σ) ∈ rows from
      by simpa only [GuardedReplay.listed, head] using known
    have equal : reply = .ret value (run.point (i + 1)).2 :=
      (finite.records _ mem).symm.trans answer
    subst reply
    refine ⟨returned (List.mem_filterMap.mpr ⟨_, mem, rfl⟩), ?_⟩
    have onScript := sameScript _ mem
    unfold GuardedReplay.mappedStep
    rw [head, Head.execute, onScript]
    exact congrArg (fun packet => StateTransition.repeat packet (support.code (run.point (i + 1)).2)) dest
  have supported (i : Nat) (earlier : ∀ j < i, run.listed rows j) : (run.point i).2 ∈ support.values := by
    cases i with
    | zero => rw [run.start]; exact support.initial_mem
    | succ j => exact (recorded j (earlier j (Nat.lt_succ_self j))).1
  by_cases outside : ∃ i, ¬ run.listed rows i
  · let cut := Nat.find outside
    have prior (i : Nat) (before : i < cut) : run.listed rows i := by
      by_contra absent
      exact (Nat.not_le_of_lt before) (Nat.find_min' outside absent)
    have absent : ¬ run.listed rows cut := Nat.find_spec outside
    have covered (i : Nat) (before : i ≤ cut) : (run.point i).2 ∈ support.values :=
      supported i (fun j lt => prior j (lt.trans_le before))
    refine .truncate cut (fun i lt => ⟨prior i lt, (recorded i (prior i lt)).2⟩) absent covered ?_
    obtain ⟨f, arg, next, _, head, _, _⟩ := request_view run cut
    have missing := missing_reply support input incoming f arg (run.point cut).2 (covered cut le_rfl)
      (by simpa only [GuardedReplay.listed, head] using absent)
    rw [head, Head.execute, missing]
  · have inside (i : Nat) : run.listed rows i := by
      by_contra absent
      exact outside ⟨i, absent⟩
    exact .retain inside (fun i => supported i (fun j _ => inside j)) (fun i => (recorded i (inside i)).2)

omit [DecidableEq Φ] [DecidableEq σ] in
private theorem observe_prefix (run : GuardedReplay g a prim p s) (code : σ → τ) (other : StatePrimitives Φ τ)
    (k : Nat) (steps : ∀ j < k, run.mappedStep code other j) :
    g.observeAt a other p (code s) = g.observeAt a other (run.point k).1 (code (run.point k).2) := by
  induction k with
  | zero => rw [run.start]
  | succ k ih =>
    refine (ih (fun i lt => steps i (lt.trans (Nat.lt_succ_self k)))).trans ?_
    rw [g.observe_state_step, show _ = _ from steps k (Nat.lt_succ_self k)]

omit [DecidableEq Φ] [DecidableEq σ] in
theorem no_infinite_after_cut (run : GuardedReplay g a prim p s) (code : σ → τ)
    (other : StatePrimitives Φ τ) (cut : Nat)
    (steps : ∀ j < cut, run.mappedStep code other j)
    (terminal : (g.head a (run.point cut).1).execute other (code (run.point cut).2) = .diverge) :
    ¬ Feedback.Infinite (g.feedback a other) (blockPoint p (code s)) := by
  intro infinite
  obtain ⟨lifted⟩ := of_infinite infinite
  have matchesAt (i : Nat) (bound : i ≤ cut) : lifted.point i = ((run.point i).1, code (run.point i).2) := by
    induction i with
    | zero => rw [lifted.start, run.start]
    | succ i ih =>
      have step := lifted.step i
      rw [ih (Nat.le_of_succ_le bound)] at step
      have eq := StateTransition.repeat.inj (step.symm.trans (steps i (Nat.lt_of_succ_le bound)))
      exact Prod.ext eq.1 eq.2
  have impossible := lifted.step cut
  rw [matchesAt cut le_rfl, terminal] at impossible
  cases impossible

omit [DecidableEq Φ] in
theorem treated_observation (run : GuardedReplay g a prim p s) (support : RunSupport σ s)
    (other : Syntax.Primitives Φ support.values.length) (path : run.Treatment rows support other) :
    g.observeAt a other p (support.code s) = WithTop.some {Outcome.diverge} := by
  cases path with
  | truncate cut prior _ _ stop =>
    rw [observe_prefix run support.code other cut (fun j lt => (prior j lt).2), g.observe_state_step, stop]
  | retain _ _ steps => exact observes (mapped run support.code other steps)

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Infinite
