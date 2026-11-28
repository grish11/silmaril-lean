module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Traversal.Comparison.OrderedTables.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.RedundantTest.Thms

/-! # Guard facts in sequenced unit request operands -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay.OrderedTables.RequestOperands

open Silmaril
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy

/-- A bit used while computing the unit argument of a selected request. -/
inductive Choice {X : Ty Empty} (frame : ReplyFrame X) where
  | read (slot : ReplyFrame.Slot frame)
  | literal (tag : Bool)

def Choice.elaborate {X : Ty Empty} {frame : ReplyFrame X} :
    Choice frame → {a : Tm signature.Instr // Tm.HasType [X] a Bit}
  | .read slot => slot.term.elaborate
  | .literal false => ⟨.inl .unit, .inl .unit⟩
  | .literal true => ⟨.inr .unit, .inr .unit⟩

/-- A projection resolves only when its exact typed slot has a fact. -/
def Choice.resolve? {X : Ty Empty} {frame : ReplyFrame X} (known : CompactTerminal.Known frame) :
    Choice frame → Option Bool
  | .read slot => known slot
  | .literal tag => some tag

/-- The operand computation can emit before returning its unit value.
The request consumes that value once and keeps the original input in both reply arms. -/
structure UnitRequest (X : Ty Empty) (L : List (Ty Empty)) where
  label : Bool
  lowEmits : List Bool
  highEmits : List Bool
  onLeft : CaseTree signature.Instr (product X Bit) L
  onRight : CaseTree signature.Instr (product X Bit) L

def UnitRequest.argumentEmits {X : Ty Empty} {L : List (Ty Empty)} (p : UnitRequest X L) (b : Bool) :
    List Bool :=
  if b then p.highEmits else p.lowEmits

/-- The argument has its own native binder, and the primitive uses that binder
as its operand. The reply continuations keep the input and the new reply. -/
def UnitRequest.quote {X : Ty Empty} {L : List (Ty Empty)} (p : UnitRequest X L) (b : Bool) :
    ScopedTarget X L :=
  let left := (applyPacked_typed_exits p.onLeft.elaborate.property).renameVars ((Ren.wk [X] unit).lift Bit)
  let right := (applyPacked_typed_exits p.onRight.elaborate.property).renameVars ((Ren.wk [X] unit).lift Bit)
  let call : Tm.HasType [unit, X] (.op (show signature.Instr from Op.ask p.label) (.var 0)) Answer :=
    .op (.var (i := 0) rfl)
  ⟨_, prependEmits_typed (p.argumentEmits b) (.let₁ .unit (.case call left right))⟩

/-- The two native arms stage the unit computation before the call. The
selector's payload binder is unused, and the retained input stays available. -/
def UnitRequest.source {X : Ty Empty} {frame : ReplyFrame X} {L : List (Ty Empty)}
    (p : UnitRequest X L) (choice : Choice frame) : ScopedTarget X L :=
  ⟨_, .case choice.elaborate.property
    ((p.quote false).property.renameVars (Ren.wk [X] unit))
    ((p.quote true).property.renameVars (Ren.wk [X] unit))⟩

/-- A native guard introduces the frame in which the argument is computed. -/
structure Guarded {X : Ty Empty} (frame : ReplyFrame X) (L : List (Ty Empty)) where
  guard : ReplyFrame.Slot frame
  emits : List Bool
  firstLabel : Bool
  onFalse : UnitRequest (product (product X unit) Bit) L
  falseChoice : Choice (.bit (.unit frame))
  onTrue : UnitRequest (product (product X unit) Bit) L
  trueChoice : Choice (.bit (.unit frame))

/-- The tested tag survives the original unit payload and the first reply. -/
def Guarded.branchFacts {X : Ty Empty} {frame : ReplyFrame X} {L : List (Ty Empty)}
    (p : Guarded frame L) (tag : Bool) : CompactTerminal.Known (.bit (.unit frame)) :=
  guardFacts (fun _ => none) p.guard tag

/-- Both reply arms proceed with the same typed continuation. -/
def firstRequest {X : Ty Empty} {L : List (Ty Empty)} (label : Bool)
    (body : ScopedTarget (product X Bit) L) : ScopedTarget X L :=
  ⟨_, .case (KnownGuardTraversal.requestTerm [] label).elaborate.property
    (applyPacked_typed_exits body.property) (applyPacked_typed_exits body.property)⟩

def Guarded.withArms {X : Ty Empty} {frame : ReplyFrame X} {L : List (Ty Empty)}
    (p : Guarded frame L) (l r : ScopedTarget (product (product X unit) Bit) L) : ScopedTarget X L :=
  ⟨_, .case (emitPrefix p.emits p.guard.term).elaborate.property
    (applyPacked_typed_exits (firstRequest p.firstLabel l).property)
    (applyPacked_typed_exits (firstRequest (!p.firstLabel) r).property)⟩

def Guarded.source {X : Ty Empty} {frame : ReplyFrame X} {L : List (Ty Empty)}
    (p : Guarded frame L) : ScopedTarget X L :=
  p.withArms (p.onFalse.source p.falseChoice) (p.onTrue.source p.trueChoice)

def Guarded.quote {X : Ty Empty} {frame : ReplyFrame X} {L : List (Ty Empty)}
    (p : Guarded frame L) (tags : Bool × Bool) : ScopedTarget X L :=
  p.withArms (p.onFalse.quote tags.1) (p.onTrue.quote tags.2)

def Guarded.tags? {X : Ty Empty} {frame : ReplyFrame X} {L : List (Ty Empty)}
    (p : Guarded frame L) : Option (Bool × Bool) := do
  let l ← p.falseChoice.resolve? (p.branchFacts false)
  let r ← p.trueChoice.resolve? (p.branchFacts true)
  pure (l, r)

def Guarded.recover? {X : Ty Empty} {frame : ReplyFrame X} {L : List (Ty Empty)}
    (p : Guarded frame L) : Option (ScopedTarget X L) :=
  p.tags?.map p.quote

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay.OrderedTables.RequestOperands
