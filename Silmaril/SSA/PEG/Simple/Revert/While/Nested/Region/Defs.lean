module

public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Parameters.Defs
public import Silmaril.SSA.PEG.Simple.Revert.While.Nested.Defs
public import Silmaril.SSA.PEG.Rules.Defs

/-! # Graph-local schedules for one parent and one child loop -/

@[expose] public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Nested.Region

open RVSDG (Port Tuple)
open Simple.Revert.While.Region (Schedule appendScope nodeAt nodeEq allPorts)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {outer inner vars : List (Ty Data)} {result t : Ty Data} {n l : Nat}
variable {g : Graph P outer [result] n l}

/-- Addresses are supplied in typed store order, independent of the
compiler's numbering. The two boundaries share a negation opcode. -/
structure Descriptor (g : Graph P outer [result] n l) (inner : List (Ty Data)) where
  outerKey : Fin l
  childKey : Fin l
  outerTheta : Tuple (Ref g.sort) outer
  outerInit : Tuple (Ref g.sort) outer
  outerNext : Tuple (Ref g.sort) outer
  outerFlag : Ref g.sort .bool
  outerPass : Ref g.sort .count
  returnSlot : Port outer result
  childTheta : Tuple (Ref g.sort) inner
  childInit : Tuple (Ref g.sort) inner
  childNext : Tuple (Ref g.sort) inner
  childFlag : Ref g.sort .bool
  childPass : Ref g.sort .count
  childExit : Tuple (Ref g.sort) inner
  negate : P [.bool] .bool

variable (d : Descriptor g inner)

abbrev Descriptor.childScope := appendScope d.childTheta d.outerTheta
abbrev Descriptor.commitScope := appendScope d.childExit d.outerTheta
abbrev Descriptor.childTagged := Tuple.cons d.childFlag d.childScope
abbrev Descriptor.outerTagged := Tuple.cons d.outerFlag d.outerTheta

abbrev Descriptor.outerInitRow (p : Port outer t) : Prop :=
  nodeAt g (d.outerInit.get p) = .ofLabel (.param p) .nil

abbrev Descriptor.outerThetaRow (p : Port outer t) : Prop :=
  nodeAt g (d.outerTheta.get p) =
    .ofLabel (.theta d.outerKey) (.cons (d.outerInit.get p) (.cons (d.outerNext.get p) .nil))

abbrev Descriptor.childThetaRow (p : Port inner t) : Prop :=
  nodeAt g (d.childTheta.get p) =
    .ofLabel (.theta d.childKey) (.cons (d.childInit.get p) (.cons (d.childNext.get p) .nil))

abbrev Descriptor.childExitRow (p : Port inner t) : Prop :=
  nodeAt g (d.childExit.get p) =
    .ofLabel (.eval d.childKey) (.cons (d.childTheta.get p) (.cons d.childPass .nil))

structure Boundary (d : Descriptor g inner) : Prop where
  distinct : d.childKey ≠ d.outerKey
  parentless : g.forest.parent d.outerKey = none
  parent : g.forest.parent d.childKey = some d.outerKey
  outerInit : ∀ t (p : Port outer t), d.outerInitRow p
  outerTheta : ∀ t (p : Port outer t), d.outerThetaRow p
  outerPass : nodeAt g d.outerPass = .ofLabel (.pass d.outerKey) (.cons d.outerFlag .nil)
  outerExit : nodeAt g (g.roots.get .head) =
    .ofLabel (.eval d.outerKey) (.cons (d.outerTheta.get d.returnSlot) (.cons d.outerPass .nil))
  childTheta : ∀ t (p : Port inner t), d.childThetaRow p
  childPass : nodeAt g d.childPass = .ofLabel (.pass d.childKey) (.cons d.childFlag .nil)
  childExit : ∀ t (p : Port inner t), d.childExitRow p

structure Accepted (g : Graph P outer [result] n l) (inner : List (Ty Data)) where
  descriptor : Descriptor g inner
  boundary : Boundary descriptor
  rank : DemandRank n l
  ranked : rank.check g = true
  outerGuard : Schedule g false descriptor.outerTagged descriptor.outerTheta
  childStart : Schedule g false (appendScope descriptor.childInit descriptor.outerTheta)
    descriptor.outerTheta
  childGuard : Schedule g false descriptor.childTagged descriptor.childScope
  childStep : Schedule g false (appendScope descriptor.childNext descriptor.outerTheta)
    descriptor.childScope
  commit : Schedule g false descriptor.outerNext descriptor.commitScope

/-- Rebuild each primitive slice over just its named scope and replay it.
The child initializer sees the old outer store alone. The outer commit
sees that same old store and the checked child eval bundle. -/
def check [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (g : Graph P outer [result] n l) (d : Descriptor g inner) (rank : DemandRank n l) :
    Option {a : Accepted g inner // a.descriptor = d} := do
  letI : ∀ t, DecidableEq (Node P outer (Fin l) g.sort t) := fun _ => nodeEq
  letI : Decidable (∀ t (p : Port outer t), d.outerInitRow p) := allPorts outer _ (fun _ _ => nodeEq _ _)
  letI : Decidable (∀ t (p : Port outer t), d.outerThetaRow p) := allPorts outer _ (fun _ _ => nodeEq _ _)
  letI : Decidable (∀ t (p : Port inner t), d.childThetaRow p) := allPorts inner _ (fun _ _ => nodeEq _ _)
  letI : Decidable (∀ t (p : Port inner t), d.childExitRow p) := allPorts inner _ (fun _ _ => nodeEq _ _)
  if h : d.childKey ≠ d.outerKey ∧ g.forest.parent d.outerKey = none ∧
      g.forest.parent d.childKey = some d.outerKey ∧
      (∀ t (p : Port outer t), d.outerInitRow p) ∧
      (∀ t (p : Port outer t), d.outerThetaRow p) ∧
      nodeAt g d.outerPass = .ofLabel (.pass d.outerKey) (.cons d.outerFlag .nil) ∧
      nodeAt g (g.roots.get .head) =
        .ofLabel (.eval d.outerKey) (.cons (d.outerTheta.get d.returnSlot) (.cons d.outerPass .nil)) ∧
      (∀ t (p : Port inner t), d.childThetaRow p) ∧
      nodeAt g d.childPass = .ofLabel (.pass d.childKey) (.cons d.childFlag .nil) ∧
      (∀ t (p : Port inner t), d.childExitRow p) ∧ rank.check g = true then do
    let ⟨distinct, parentless, parent, outerInit, outerTheta, outerPass, outerExit,
      childTheta, childPass, childExit, ranked⟩ := h
    let outerGuard ← Schedule.inferPrimitive g d.outerTheta d.outerTagged
    let childStart ← Schedule.inferPrimitive g d.outerTheta (appendScope d.childInit d.outerTheta)
    let childGuard ← Schedule.inferPrimitive g d.childScope d.childTagged
    let childStep ← Schedule.inferPrimitive g d.childScope (appendScope d.childNext d.outerTheta)
    let commit ← Schedule.inferPrimitive g d.commitScope d.outerNext
    return ⟨⟨d, ⟨distinct, parentless, parent, outerInit, outerTheta, outerPass, outerExit,
      childTheta, childPass, childExit⟩, rank, ranked, outerGuard, childStart, childGuard, childStep, commit⟩,
      rfl⟩
  else none

variable (a : Accepted g inner)

def dropFlag (vars : List (Ty Data)) : Stmt P false (.bool :: vars) vars :=
  .project ((ports vars).map fun _ p => .tail p)

def continueTest (negate : P [.bool] .bool) : Expr P (.bool :: vars) .bool :=
  .op negate (.cons (.var .head) .nil)

def Accepted.childStartCode : Stmt P false outer (.bool :: (inner ++ outer)) :=
  .seq a.childStart.lower a.childGuard.lower

def Accepted.childBody : Stmt P false (.bool :: (inner ++ outer)) (.bool :: (inner ++ outer)) :=
  .seq (dropFlag (inner ++ outer)) (.seq a.childStep.lower a.childGuard.lower)

def Accepted.activate : Stmt P true outer (inner ++ outer) :=
  .seq a.childStartCode.enableWhile
    (.seq (.while rfl (continueTest a.descriptor.negate) a.childBody.enableWhile)
      (dropFlag (inner ++ outer)).enableWhile)

def Accepted.body : Stmt P true (.bool :: outer) (.bool :: outer) :=
  .seq (dropFlag outer).enableWhile
    (.seq a.activate (.seq a.commit.lower.enableWhile a.outerGuard.lower.enableWhile))

def Accepted.revert : Program P true outer result :=
  ⟨.bool :: outer, .seq a.outerGuard.lower.enableWhile
    (.while rfl (continueTest a.descriptor.negate) a.body), .tail a.descriptor.returnSlot⟩

variable (m : Interpretation.{u,v,w} P)

def Accepted.activateFuel (fuel : Nat) (old : Tuple m.Value outer) : Option (Tuple m.Value (inner ++ outer)) := do
  let start ← a.childStartCode.runLoopFree m old
  let final ← runWhile m (continueTest a.descriptor.negate) (a.childBody.runLoopFree m) fuel start
  (dropFlag (inner ++ outer)).runLoopFree m final

def Accepted.stepFuel (childFuel : Nat) (store : Tuple m.Value (.bool :: outer)) :
    Option (Tuple m.Value (.bool :: outer)) := do
  let old ← (dropFlag outer).runLoopFree m store
  let child ← a.activateFuel m childFuel old
  let next ← a.commit.lower.runLoopFree m child
  a.outerGuard.lower.runLoopFree m next

def Accepted.runFuel (outerFuel childFuel : Nat) (input : Tuple m.Value outer) :
    Option (m.Value result) :=
  ((a.outerGuard.lower.runLoopFree m input).bind
    (runWhile m (continueTest a.descriptor.negate) (a.stepFuel m childFuel) outerFuel)).map
    fun final => final.get (.tail a.descriptor.returnSlot)

/-- The same old outer tuple is visible at every child sample of this
activation. In the outer proof this follows from its iteration invariant. -/
def Accepted.Captures (values : g.Valuation m) (base : Index l) (old : Tuple m.Value outer) : Prop :=
  ∀ j t (p : Port outer t),
    Rules.readRef values (a.descriptor.outerTheta.get p) (base.set a.descriptor.childKey j) =
      some (old.get p)

/-- One least child pass and the typed store expected by the outer commit. -/
structure Accepted.ChildObservation (values : g.Valuation m) (base : Index l)
    (count : Nat) (store : Tuple m.Value (inner ++ outer)) : Prop where
  pass : Rules.readRef values a.descriptor.childPass base = some ⟨count⟩
  commit : ∀ t (p : Port (inner ++ outer) t),
    Rules.readRef values (a.descriptor.commitScope.get p) base = some (store.get p)

/-- The outer first pass and one finite child first pass per continuing
outer iteration. Child coordinates are reset by pass semantics. -/
structure Accepted.FirstExits (values : g.Valuation m) (base : Index l) (count : Nat) : Prop where
  outer : Rules.readRef values a.descriptor.outerPass base = some ⟨count⟩
  child : ∀ j < count, ∃ k, Rules.readRef values a.descriptor.childPass
    (base.set a.descriptor.outerKey j) = some ⟨k⟩

/-- Defined executions of the complete slices where their typed stores
realize the corresponding PEG scope. The update is required on a
continuing child store, and the commit on the whole child exit bundle. -/
structure Accepted.DefinedSlices (values : g.Valuation m) : Prop where
  outerGuard : ∀ idx store, Schedule.Realizes m values idx a.descriptor.outerTheta store →
    ∃ next, a.outerGuard.lower.runLoopFree m store = some next
  childStart : ∀ idx old, a.Captures m values idx old →
    ∃ next, a.childStart.lower.runLoopFree m old = some next
  childGuard : ∀ idx store, Schedule.Realizes m values idx a.descriptor.childScope store →
    ∃ next, a.childGuard.lower.runLoopFree m store = some next
  childStep : ∀ idx store, Schedule.Realizes m values idx a.descriptor.childScope store →
    Rules.readRef values a.descriptor.childFlag idx = some ⟨false⟩ →
    ∃ next, a.childStep.lower.runLoopFree m store = some next
  commit : ∀ idx trips store, a.ChildObservation m values idx trips store →
    ∃ next, a.commit.lower.runLoopFree m store = some next

end Silmaril.SSA.PEG.Simple.Revert.While.Nested.Region
