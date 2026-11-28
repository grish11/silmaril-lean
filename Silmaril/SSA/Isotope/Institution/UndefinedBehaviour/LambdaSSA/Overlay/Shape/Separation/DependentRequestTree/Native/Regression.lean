module

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.ExitUB.Defs

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction

open Category.FiniteIteration
open Category.FiniteIteration.CFG.Dependent.Native (withExitUB)
open LambdaSSA.Region (packedExitType)
open TwoRequest (Tag resultBehaviour)

private inductive Op where
  | choose
  | read
  deriving DecidableEq

private abbrev replies : Op → List Syntax.Ty
  | .choose => List.replicate 2 .unit
  | .read => List.replicate 1 .unit

private def argType : Op → Syntax.Ty
  | .choose => .unit
  | .read => .coprod .unit .unit

private instance : HasTy Op Syntax.Ty := ⟨argType, fun f => packedExitType (replies f)⟩

private abbrev sig : RequestSignature Op := ⟨replies, fun _ => rfl⟩

private theorem unit_at {n : Nat}
    (i : Fin (List.replicate n (.unit : Syntax.Ty)).length) :
    (List.replicate n (.unit : Syntax.Ty)).get i = .unit := by simp

private abbrev Packets : List Syntax.Ty := List.replicate 5 .unit

private def operand (right : Bool) : Syntax.Expr [] (instrSrc Op.read) :=
  if right then .inr .unit else .inl .unit

/-- Both arms reach the same written join, which calls the same key again.
The key's operand at the join is stored independently of the two arms. -/
private def diamond (right : Bool) (exit : Tag) : Table sig Packets where
  entry := (0 : Fin 5)
  input := .unit
  row i := match i.val with
    | 0 => .request .choose .unit (fun (j : Fin 2) => if j = 0 then (1 : Fin 5) else (2 : Fin 5))
        (fun j => (unit_at (n := 5) _).trans (unit_at (n := 2) j).symm)
    | 1 => .request .read (operand false) (fun _ => (3 : Fin 5))
        (fun j => (unit_at (n := 5) _).trans (unit_at (n := 1) j).symm)
    | 2 => .request .read (operand true) (fun _ => (3 : Fin 5))
        (fun j => (unit_at (n := 5) _).trans (unit_at (n := 1) j).symm)
    | 3 => .request .read (operand right) (fun _ => (4 : Fin 5))
        (fun j => (unit_at (n := 5) _).trans (unit_at (n := 1) j).symm)
    | _ => .exit exit
  selected i := i == (1 : Fin 2)

private abbrev source := diamond true 0
private abbrev target := diamond false 0
private abbrev marked := diamond true 1

private theorem source_checked : source.check source.native = true := rfl
private theorem target_checked : target.check target.native = true := rfl

example : (3 : Fin 5) ∈ source.targets (1 : Fin 5) ∧ (3 : Fin 5) ∈ source.targets (2 : Fin 5) := by
  decide

example : source.extract? target.native = none := rfl

private def read (right : Bool) (next : Tree sig.replies) : Tree sig.replies :=
  .ask .read (operand right) (fun _ => next)

private def terminal (exit : Tag) : Tree sig.replies :=
  .stop (if exit == (1 : Fin 2) then .ub else .ret exit)

private def expected (right : Bool) (exit : Tag) : Tree sig.replies :=
  .ask .choose .unit (fun (i : Fin 2) => read (i != 0) (read right (terminal exit)))

private theorem extract_eq (right : Bool) (exit : Tag) (ok : (diamond right exit).entryCheck = true) :
    (diamond right exit).extract ok = expected right exit := by
  let g := diamond right exit
  have lastRank : (g.ranks.get (4 : Fin 5)).isSome = true := rfl
  have joinRank : (g.ranks.get (3 : Fin 5)).isSome = true := rfl
  have leftRank : (g.ranks.get (1 : Fin 5)).isSome = true := rfl
  have rightRank : (g.ranks.get (2 : Fin 5)).isSome = true := rfl
  have last : g.extractAt (4 : Fin 5) lastRank = terminal exit := by
    rw [Table.extractAt.eq_def]
    rfl
  have join : g.extractAt (3 : Fin 5) joinRank = read right (terminal exit) := by
    rw [Table.extractAt.eq_def]
    change read right (g.extractAt (4 : Fin 5) lastRank) = _
    rw [last]
  have left : g.extractAt (1 : Fin 5) leftRank = read false (read right (terminal exit)) := by
    rw [Table.extractAt.eq_def]
    change read false (g.extractAt (3 : Fin 5) joinRank) = _
    rw [join]
  have rightArm : g.extractAt (2 : Fin 5) rightRank = read true (read right (terminal exit)) := by
    rw [Table.extractAt.eq_def]
    change read true (g.extractAt (3 : Fin 5) joinRank) = _
    rw [join]
  let dest (i : Fin 2) : Fin 5 := if i = 0 then 1 else 2
  have ranked (i : Fin 2) : (g.ranks.get (dest i)).isSome = true := by
    by_cases arm : i = 0
    · simpa only [dest, ite_eq_left arm] using leftRank
    · simpa only [dest, ite_eq_right arm] using rightRank
  rw [Table.extract, Table.extractAt.eq_def]
  change Tree.ask Op.choose .unit (fun i => g.extractAt (dest i) (ranked i)) = expected right exit
  unfold expected
  refine congrArg (Tree.ask Op.choose .unit) ?_
  funext i
  by_cases arm : i = (0 : Fin 2)
  · subst i
    exact left
  · have selected : (i != (0 : Fin 2)) = true := by simp [arm]
    simpa only [dest, ite_eq_right arm, selected] using rightArm

private theorem observes (right : Bool) (exit : Tag) {n : Nat} (h : Handler sig.replies n) (s : Fin n)
    (ok : (diamond right exit).check (diamond right exit).native = true) :
    Shape.denote (withExitUB (diamond right exit).native (diamond right exit).selected) (sig.model h) s =
      resultBehaviour ((expected right exit).execute h s) := by
  rw [← (diamond right exit).observe ok, extract_eq]
  exact finite_observe _ h Syntax.emptyBindings s

private def unitPayload : Syntax.Payload (.unit : Syntax.Ty) := ⟨.unit, .unit⟩

/-- The second occurrence of read needs the right injection, at its own
prefix state. The probe faults on that query before its continuation. -/
private def mismatch : Prefix sig.replies 2 :=
  .step .choose .unit (0 : Fin 2) unitPayload
    (.step .read (.inl .unit) (0 : Fin 1) unitPayload (.stop (some (.read, .inr .unit))))

private def succeeds : Prefix sig.replies 3 :=
  .step .choose .unit (0 : Fin 2) unitPayload
    (.step .read (.inl .unit) (0 : Fin 1) unitPayload
      (.step .read (.inr .unit) (0 : Fin 1) unitPayload (.stop none)))

example : Shape.denote (withExitUB source.native source.selected) (sig.model succeeds.handler) 0 =
    WithTop.some {Outcome.ret (0 : Fin 2) Value.unit (3 : Fin 4)} :=
  observes true 0 _ _ source_checked

example : Shape.denote (withExitUB marked.native marked.selected) (sig.model succeeds.handler) 0 = ⊤ :=
  observes true 1 _ _ rfl

private theorem source_faults :
    Shape.denote (withExitUB source.native source.selected) (sig.model mismatch.handler) 0 =
      WithTop.some {Outcome.fault (2 : Fin 3)} :=
  observes true 0 _ _ source_checked

private theorem target_diverges :
    Shape.denote (withExitUB target.native target.selected) (sig.model mismatch.handler) 0 =
      WithTop.some {Outcome.diverge} :=
  observes false 0 _ _ target_checked

example : ∃ (n : Nat) (probe : Prefix sig.replies n),
    n ≤ min (source.extract (source.checked_rank source_checked)).depth
      (target.extract (target.checked_rank target_checked)).depth ∧
    ¬ Shape.denote (withExitUB source.native source.selected) (sig.model probe.handler) 0 ≤
      Shape.denote (withExitUB target.native target.selected) (sig.model probe.handler) 0 := by
  apply exists_countermodel source_checked target_checked
  intro le
  have checked := (finite_refines_iff source_checked target_checked).mpr le 3 (sig.primitives mismatch.handler) 0
  change Shape.denote (withExitUB source.native source.selected) (sig.model mismatch.handler) 0 ≤
    Shape.denote (withExitUB target.native target.selected) (sig.model mismatch.handler) 0 at checked
  rw [source_faults, target_diverges] at checked
  have member := WithTop.coe_le_coe.mp checked (Set.mem_singleton (Outcome.fault (2 : Fin 3)))
  cases member

/-- info: 'Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.finite_refines_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms finite_refines_iff

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction
