module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Traversal.Comparison.OrderedTables.RequestOperands.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedRequestOperands

/-! # Native operand replay and the unit query boundary -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay.OrderedTables.RequestOperands

open Silmaril
open Paper.WithCaseBind.SelectedTerminal (Seed)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy

/-- Replay a sequenced argument at any exact frame that satisfies its facts. -/
theorem UnitRequest.source_at {Γ : List (Ty Empty)} {X : Ty Empty} {frame : ReplyFrame X}
    {L : List (Ty Empty)} (p : UnitRequest X L) (choice : Choice frame)
    (known : CompactTerminal.Known frame) (b : Bool) (v : ReplyFrame.Value Γ frame)
    (valid : FactsHold known v) (found : choice.resolve? known = some b) :
    Paper.Extension.Eqv Seed Γ ((p.source choice).val.substVars (Tm.singleSubst v.elaborate.val))
      ((p.quote b).val.substVars (Tm.singleSubst v.elaborate.val)) L :=
  SelectedRequestOperands.source_at p choice known b v valid found

/-- Recovery is a native equality at the original typed packed endpoints. -/
theorem Guarded.packed_eq_of_recovered {X : Ty Empty} {frame : ReplyFrame X} {L : List (Ty Empty)}
    (p : Guarded frame L) (q : ScopedTarget X L) (found : p.recover? = some q) :
    p.source.packed = q.packed :=
  SelectedRequestOperands.packed_eq_of_recovered p q found

/-- The exact request profile admits a unit query. -/
theorem ask_source_unit (label : Bool) : instrSrc (τ := Ty Empty) (show signature.Instr from Op.ask label) =
    (unit : Ty Empty) := rfl

/-- Neither constructor literal of type Bit is a legal raw query here. -/
theorem ask_literal_untypable (Γ : List (Ty Empty)) (label b : Bool) :
    ¬ Tm.HasType Γ (.op (show signature.Instr from Op.ask label) (replyBitTag b .unit)) Answer := by
  cases b <;> intro typed <;> cases typed with
  | op arg => cases arg

/-- These are all the primitive observations after evaluating the unit
argument. The log records the opcode label, reply arm, and reply bit. -/
theorem ask_outcomes (label : Bool) (arg : Kleisli.value (unit : Ty Empty)) :
    (model.eval (show signature.Instr from Op.ask label) arg).outcomes =
      Set.range (fun reply : Bool × Bool => (.ok (answer reply.1 reply.2), replyLog label reply.1 reply.2)) := rfl

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay.OrderedTables.RequestOperands
