module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.TwoRequests.Defs

/-! # Selected Bit queries with a continuation at each first reply tag -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.TwoRequests.ByReplyTag

open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit bit answer)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite (Expr)

local notation "U" => (Ty.unit : Ty Empty)

/-- Slot zero is the first reply payload. Slot one is the guarded input Bit. -/
structure Arm where
  label : Bool
  query : Expr 2

structure Program where
  firstLabel : Bool
  left : Arm
  right : Arm

/-- The two coordinates are the guard bit and the selected reply payload. -/
structure ArmKey where
  label : Bool
  query : Bool → Bool → Bool

structure Key where
  firstLabel : Bool
  left : ArmKey
  right : ArmKey

def Arm.key (a : Arm) : ArmKey :=
  ⟨a.label, fun g r => a.query.eval (assignment g r)⟩

def Program.key (p : Program) : Key :=
  ⟨p.firstLabel, p.left.key, p.right.key⟩

def Key.arm (k : Key) (right : Bool) : ArmKey :=
  if right then k.right else k.left

/-- At one first-reply history, consult only the selected tag's continuation. -/
def Key.agreesAt (k l : Key) (guard : Bool) (firstReply : Reply) : Bool :=
  let a := k.arm firstReply.1
  let b := l.arm firstReply.1
  k.firstLabel == l.firstLabel && a.label == b.label &&
    a.query guard firstReply.2 == b.query guard firstReply.2

/-- Check the finite histories admitted by the all-replies model. -/
def Program.compare (p q : Program) : Bool :=
  decide (∀ tag (guard payload : Bool), p.key.agreesAt q.key guard (tag, payload) = true)

/-- Bind the real payload at either tag and enter that tag's continuation. -/
def firstBy (label guard : Bool) (left right : Region signature.Instr) : Region signature.Instr :=
  .case (.op (.ask label) (literal guard)) left right

theorem firstBy_typed (label guard : Bool) {Γ : VCtx (Ty Empty)} {l r : Region signature.Instr}
    (hl : ValueBranches (Bit :: Γ) l Exits) (hr : ValueBranches (Bit :: Γ) r Exits) :
    ValueBranches Γ (firstBy label guard l r) Exits :=
  .case (.op (constructorBit_value guard .unit).hasType) hl hr

def Arm.region (a : Arm) (guard : Bool) : Region signature.Instr :=
  compile a.label a.query (guardedSlots guard)

theorem Arm.typed (a : Arm) (guard : Bool) : ValueBranches [Bit, U, Bit] (a.region guard) Exits :=
  compile_typed _ _ (fun i => (guardedSlots_typed guard i).hasType)

/-- Fix the actual guard constructor, then quote the row over the live payload. -/
def ArmKey.region (k : ArmKey) (guard : Bool) : Region signature.Instr :=
  compile k.label (Expr.quote 1 (fun env => k.query guard (env 0))) replySlot

theorem ArmKey.typed (k : ArmKey) (guard : Bool) : ValueBranches [Bit, U, Bit] (k.region guard) Exits :=
  compile_typed _ _ (fun _ => .var (i := 0) rfl)

def Program.region (p : Program) : Region signature.Instr :=
  .case (.var 0)
    (firstBy p.firstLabel false (p.left.region false) (p.right.region false))
    (firstBy p.firstLabel true (p.left.region true) (p.right.region true))

theorem Program.typed (p : Program) : ValueBranches [Bit] p.region Exits :=
  .case (.var (i := 0) rfl) (firstBy_typed _ _ (p.left.typed false) (p.right.typed false))
    (firstBy_typed _ _ (p.left.typed true) (p.right.typed true))

def Key.region (k : Key) : Region signature.Instr :=
  .case (.var 0)
    (firstBy k.firstLabel false (k.left.region false) (k.right.region false))
    (firstBy k.firstLabel true (k.left.region true) (k.right.region true))

theorem Key.typed (k : Key) : ValueBranches [Bit] k.region Exits :=
  .case (.var (i := 0) rfl) (firstBy_typed _ _ (k.left.typed false) (k.right.typed false))
    (firstBy_typed _ _ (k.left.typed true) (k.right.typed true))

def Program.packed (p : Program) :=
  Extension.Singleton.ofRegion Seed p.typed.packExits

def Key.packed (k : Key) :=
  Extension.Singleton.ofRegion Seed k.typed.packExits

abbrev Observation := Except Bool (value (packedExitType Exits)) × FreeMonoid Event

def Key.firstEvent (k : Key) (guard : Bool) (reply : Reply) : Event :=
  ⟨k.firstLabel, guard, reply.1, reply.2⟩

def Key.secondEvent (k : Key) (guard : Bool) (firstReply secondReply : Reply) : Event :=
  let a := k.arm firstReply.1
  ⟨a.label, a.query guard firstReply.2, secondReply.1, secondReply.2⟩

def Key.observe (k : Key) (guard : Bool) (firstReply secondReply : Reply) : Observation :=
  (.ok (atExit (answer secondReply.1 secondReply.2)),
    FreeMonoid.of (k.firstEvent guard firstReply) * FreeMonoid.of (k.secondEvent guard firstReply secondReply))

/-- The model admits all reply pairs. The second event uses only the
continuation selected by the first event's actual reply tag and payload. -/
def Key.outcomes (k : Key) (guard : Bool) : Set Observation :=
  Set.range fun pair : Reply × Reply => k.observe guard pair.1 pair.2

noncomputable def Program.observations (p : Program) (guard : Bool) :=
  ((denote.map p.packed).of (bit guard)).outcomes

/-- A shared deterministic policy sees the ordered history, request label and query. -/
abbrev Policy := List Event → Bool → Bool → Reply

/-- Collect the replies selected by one policy at the actual queries. -/
def Key.policyReplies (k : Key) (policy : Policy) (guard : Bool) : Reply × Reply :=
  let firstReply := policy [] k.firstLabel guard
  let a := k.arm firstReply.1
  let secondReply := policy [k.firstEvent guard firstReply] a.label (a.query guard firstReply.2)
  (firstReply, secondReply)

def Key.runPolicy (k : Key) (policy : Policy) (guard : Bool) : Observation :=
  let pair := k.policyReplies policy guard
  k.observe guard pair.1 pair.2

namespace Example

def left : Arm := ⟨true, .read 0⟩

def reference : Program :=
  ⟨true, left, ⟨false, .split (.read 0) (.split (.literal true) (.literal false))⟩⟩

def changed : Program :=
  ⟨true, left, ⟨false, .split (.literal false) (.split (.literal true) (.literal false))⟩⟩

def keepLeft : Policy := fun _ _ _ => (false, false)

end Example
end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.TwoRequests.ByReplyTag
