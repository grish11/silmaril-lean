module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Numbered.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Prune.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Join.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Numbered.Proofs

open SeaOfNodes.Diamond (Model Ty Val ValueSort dataPorts)
open RVSDG (Locals Tuple Wires extend)
open RVSDG.NestedTheta (Term)
open Join (Block Opcode model)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond (thenBase_eval)
open Diamond.Prune (HeaderProjection lowerFlow_eval routeProjectedWith_eval)
open Nested.Numbered (outerSigs outerChoice routePorts outerArm_run branchBank_agrees)
open Blocks (Bank)
open Blocks.Prune (Mask)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
variable (p : Program src entry) (m : Model.{u, v, w} Op) {carry merge : Mask regs}

private theorem project_restore {F : Ty Data → Type w} (mask : Mask regs)
    (old : Tuple F (dataPorts regs)) (kept : Tuple F (dataPorts mask.kept)) :
    mask.project (restore mask old kept) = kept := by
  induction mask with
  | nil => cases old; cases kept; rfl
  | keep rest ih =>
    cases old with
    | cons _ old =>
      cases kept with
      | cons field kept => exact congrArg (Tuple.cons field) (ih old kept)
  | drop rest ih =>
    cases old with
    | cons _ old => exact ih old kept

private theorem projectResults_eval {args : List (Ty Data)} (fuel : Nat) (input : Tuple (Val m.value) args) :
    {past sigs : List (List (Ty Data))} → (region : Term (Opcode Op) args past sigs (dataPorts regs)) →
      (locals : Locals (Val m.value) past) →
      (projectResults merge region).eval (model m) fuel input locals =
        (region.eval (model m) fuel input locals).map merge.project
  | _, _, .ret wires, locals => congrArg some (merge.project_read m input locals wires)
  | _, _, .bind node children rest, locals => by
    simp only [projectResults, Term.eval]
    generalize node.kind.eval (model m) fuel
        (fun i bank => (children i).eval (model m) fuel (past := []) bank PUnit.unit)
        (node.inputs.read input locals) = selected
    cases selected with
    | none => rfl
    | some bank => exact projectResults_eval fuel input rest (locals.snoc bank)

private theorem arm_run (fuel : Nat) (bank : Bank (regs := regs) m) :
    (arm p merge ((outerChoice p).eval bank)).run (model m) fuel bank =
      some (merge.project (Nested.Numbered.branchBank p m bank)) :=
  (projectResults_eval (merge := merge) m fuel bank (past := []) _ PUnit.unit).trans
    (congrArg (Option.map merge.project) (outerArm_run p m fuel bank))

theorem afterOuter_eval {args results : List (Ty Data)}
    {past suffix : List (List (Ty Data))}
    (current : Wires args past (dataPorts regs))
    (finish : Wires args (extend past (splitSigs merge)) (dataPorts merge.kept) →
      Term (Opcode Op) args (extend past (splitSigs merge)) suffix results)
    (fuel : Nat) (input : Tuple (Val m.value) args) (locals : Locals (Val m.value) past)
    (observe : Bank (regs := merge.kept) m → Option (Tuple (Val m.value) results))
    (agrees : ∀ wires locals', (finish wires).eval (model m) fuel input locals' =
      observe (wires.read input locals')) :
    (Nested.Numbered.afterOuterWith p (arm p merge) current finish).eval (model m) fuel input locals =
      observe (merge.project (Nested.Numbered.branchBank p m (current.read input locals))) :=
  Nested.Numbered.afterOuterWith_eval p m (arm p merge) current finish fuel input locals _
    (arm_run p m fuel) observe agrees

variable (projected : HeaderProjection (src p.header).body carry)

theorem merge_run (fuel : Nat) (old : Bank (regs := regs) m) :
    (mergeRegion p projected merge).toGraph.run (model m) fuel (carry.project old) =
      some (incoming p merge m old (p.selected m old)) := by
  rw [← RVSDG.NestedTheta.Graph.run_toTerm, Term.toTerm_toGraph]
  unfold mergeRegion Term.run
  erw [thenBase_eval (observe := fun bank => some (merge.project (Nested.Numbered.branchBank p m bank)))]
  · erw [lowerFlow_eval]
    change some (merge.project (Nested.Numbered.branchBank p m (projected.headerBank m (carry.project old)))) = _
    rw [projected.header_agrees, branchBank_agrees]
    rfl
  · intro current locals
    exact afterOuter_eval p m current .ret fuel (carry.project old) locals some (fun _ _ => rfl)

/-- It is enough for the tested latch to observe the same condition and
carried bank on any two completions of the reduced input. -/
theorem activation_run_for
    (agrees : ∀ left right : Bank (regs := regs) m, merge.project left = merge.project right →
      latchPacket p carry m ((Nested.Numbered.tail p).eval m left) =
        latchPacket p carry m ((Nested.Numbered.tail p).eval m right))
    (fuel : Nat) (old : Bank (regs := regs) m) :
    (thetaBodyFor p projected merge).run (model m) fuel (carry.project old) =
      some (latchPacket p carry m (Nested.Numbered.nextBank p m old)) := by
  let packet (bank : Bank (regs := regs) m) := some (latchPacket p carry m bank)
  let finish (bank : Bank (regs := merge.kept) m) :=
    packet ((Nested.Numbered.tail p).eval m (restore merge old bank))
  unfold thetaBodyFor Term.run
  erw [thenBase_eval (observe := fun bank => finish (merge.project (Nested.Numbered.branchBank p m bank)))]
  · erw [lowerFlow_eval]
    change finish (merge.project (Nested.Numbered.branchBank p m (projected.headerBank m (carry.project old)))) = _
    rw [projected.header_agrees, branchBank_agrees]
    exact congrArg some (agrees _ _ (project_restore merge old _))
  · intro current locals
    apply afterOuter_eval p m current _ fuel (carry.project old) locals finish
    intro kept later
    erw [thenBase_eval (observe := packet), Block.lowerFrom_eval]
    · apply congrArg some
      apply agrees
      refine (merge.project_read m _ later _).symm.trans ?_
      exact (congrArg (fun wires => Wires.read wires (carry.project old) later)
        (project_restore merge _ kept)).trans (project_restore merge old _).symm
    · intro wires done
      exact routeProjectedWith_eval m p.again wires fuel (carry.project old) done

theorem activation_run (checked : Checked p merge) (fuel : Nat) (old : Bank (regs := regs) m) :
    (thetaBody p projected checked).run (model m) fuel (carry.project old) =
      let next := Nested.Numbered.nextBank p m old
      some (RVSDG.Theta.bodyResult (model m) (next.get p.again).down (carry.project next)) := by
  apply activation_run_for p m projected _ fuel old
  intro left right same
  have join : (src p.join).body.eval m left = (src p.join).body.eval m right :=
    (checked.header_agrees m left).symm.trans
      ((congrArg (checked.headerBank m) same).trans (checked.header_agrees m right))
  have afterMerge (bank : Bank (regs := regs) m) :
      (Nested.Numbered.tail p).eval m bank =
        (src p.latch).body.eval m ((src p.join).body.eval m bank) := List.foldl_append
  rw [afterMerge, afterMerge, join]

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Numbered.Proofs
