module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Exits.Defs

/-! # Witnessed arms reading a structural binary reply payload -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

open Kleisli (value)
open LambdaSSA (At)
open LambdaSSA.Acyclic (Operand FiniteExit)
open LambdaSSA.Acyclic.Positional.Capture.Reverse (Program)
open LambdaSSA.Region (packedExitType)
open LambdaSSA.Semantics.Categorical (labelAt_get)
open LetIter.Semantics.Categorical (boundEnv)
open Silmaril.Semantics.NondeterministicTrace (Tagged)

abbrev Bit : Sorts := .coprod .unit .unit
abbrev Answer : Sorts := .coprod Bit Bit

def bit : Bool → value Bit
  | false => .inl PUnit.unit
  | true => .inr PUnit.unit

inductive Op where
  | emit (label : Bool)
  | ask (request : Bool)

def signature : InstrSig Sorts Bool where
  Instr := Op
  hasTy := ⟨fun _ => .unit, fun op => match op with
    | .emit _ => .unit
    | .ask _ => Answer⟩
  hasEff := ⟨fun _ => true⟩

/-- The typed slot of an arm's result in the shared ordered interface. -/
abbrev Position (L : List Sorts) := {i : Fin L.length // L.get i = Bit}

theorem Position.typed {L : List Sorts} (p : Position L) : At L p.1 Bit := by
  have h := labelAt_get L p.1
  rwa [p.2] at h

def Position.result {L : List Sorts} (p : Position L) (b : Bool) : Exits.Exit L :=
  ⟨p.1, p.2.symm ▸ bit b⟩

/-- Return the bound payload directly, or case-analyze it to return one of
two literal bits. The identity table and the variable have distinct syntax. -/
inductive Expr where
  | payload
  | table (whenFalse whenTrue : Bool)

def Expr.evaluate : Expr → Bool → Bool
  | .payload, b => b
  | .table l r, b => if b then r else l

def bitOperand {n : Nat} (β : BoundCtx Sorts n) : Bool → Operand signature.Instr β Bit
  | false => ⟨.inl .unit, .inl .unit⟩
  | true => ⟨.inr .unit, .inr .unit⟩

def readPayload {n : Nat} (β : BoundCtx Sorts n) (i : Fin n) (h : β.get i = Bit) :
    Operand signature.Instr β Bit :=
  ⟨.bv i, h ▸ .bv⟩

def Expr.operand {n : Nat} (β : BoundCtx Sorts n) (i : Fin n) (h : β.get i = Bit) :
    Expr → Operand signature.Instr β Bit
  | .payload => readPayload β i h
  | .table l r =>
    let d := readPayload β i h
    let lhs := bitOperand (β.snoc Ty.unit) l
    let rhs := bitOperand (β.snoc Ty.unit) r
    ⟨.case d.1 lhs.1 rhs.1, .case d.2 lhs.2 rhs.2⟩

structure Arm (L : List Sorts) where
  emits : List Bool
  position : Position L
  result : Expr

structure ArmNormal (L : List Sorts) where
  emits : List Bool
  position : Position L
  whenFalse : Bool
  whenTrue : Bool

def Arm.normal {L : List Sorts} (a : Arm L) : ArmNormal L :=
  ⟨a.emits, a.position, a.result.evaluate false, a.result.evaluate true⟩

def ArmNormal.render {L : List Sorts} (a : ArmNormal L) : Arm L :=
  ⟨a.emits, a.position, .table a.whenFalse a.whenTrue⟩

def ArmNormal.result {L : List Sorts} (a : ArmNormal L) (b : Bool) : Exits.Exit L :=
  a.position.result (if b then a.whenTrue else a.whenFalse)

/-- Effects push unit slots above the live payload. Lookup keeps using
the original slot as these binders are added. -/
def Arm.renderPrefix {L : List Sorts} (a : Arm L) :
    List Bool → {n : Nat} → (β : BoundCtx Sorts n) → (i : Fin n) →
      β.get i = Bit → Operand signature.Instr β (packedExitType L)
  | [], _, β, i, h => FiniteExit.tag L a.position.1 a.position.typed (a.result.operand β i h)
  | b :: bs, _, β, i, h =>
    let k := a.renderPrefix bs (β.snoc Ty.unit) i.succ h
    ⟨.let₁ (.op (.emit b) .unit) k.1, .let₁ (.op .unit) k.2⟩

def Arm.operand {L : List Sorts} {n : Nat} (β : BoundCtx Sorts n) (a : Arm L) :
    Operand signature.Instr (β.snoc Bit) (packedExitType L) :=
  a.renderPrefix a.emits (β.snoc Bit) 0 rfl

structure ProgramBody (L : List Sorts) where
  request : Bool
  bound : Bool
  left : Arm L
  right : Arm L

structure Normal (L : List Sorts) where
  request : Bool
  left : ArmNormal L
  right : ArmNormal L

def ProgramBody.normal {L : List Sorts} (p : ProgramBody L) : Normal L :=
  ⟨p.request, p.left.normal, p.right.normal⟩

def Normal.render {L : List Sorts} (p : Normal L) : ProgramBody L :=
  ⟨p.request, false, p.left.render, p.right.render⟩

/-- Both forms perform the request once. The bound form inserts the
answer binder below the branch payload, weakening the open arms. -/
def requestOperand {n : Nat} {β : BoundCtx Sorts n} {A : Sorts} (req bound : Bool)
    (l r : Operand signature.Instr (β.snoc Bit) A) : Operand signature.Instr β A :=
  if bound then
    ⟨.let₁ (.op (.ask req) .unit) (.case (.bv 0) l.1.underBinder r.1.underBinder),
      .let₁ (.op .unit) (.case .bv l.2.underBinder r.2.underBinder)⟩
  else
    ⟨.case (.op (.ask req) .unit) l.1 r.1, .case (.op .unit) l.2 r.2⟩

def ProgramBody.entry {L : List Sorts} (p : ProgramBody L) :
    Operand signature.Instr .nil (packedExitType L) :=
  requestOperand p.request p.bound (p.left.operand .nil) (p.right.operand .nil)

def program (H : Sorts) (L : List Sorts) (p : ProgramBody (H :: L)) :
    Program signature.Instr .nil (H :: L) :=
  ⟨packedExitType (H :: L), p.entry,
    Exits.router (rfl : At (H :: L) 0 H) (H :: L) (LambdaSSA.Ren.id (H :: L))⟩

def equation (H : Sorts) (L : List Sorts) (p q : ProgramBody (H :: L)) : GrammarEquation signature :=
  ⟨⟨0, .nil, H :: L⟩, program H L p, program H L q⟩

def answer (right b : Bool) : value Answer :=
  if right then .inr (bit b) else .inl (bit b)

/-- A single request records both fields of its reply in the existing trace
alphabet. The first field is the arm tag and the second is its payload. -/
def replyLog (req right b : Bool) : Log :=
  FreeMonoid.of (.answer req right) * FreeMonoid.of (.answer req b)

def model : Isotope.Semantics.InstructionModel value signature.Instr Trace where
  eval
    | .emit b => Reply.model.eval (.emit b)
    | .ask req => fun _ => Tagged.ofOutcomes
        (Set.range fun reply : Bool × Bool =>
          (.ok (answer reply.1 reply.2), replyLog req reply.1 reply.2))

/-- The enumerated execution after a particular payload has entered an arm. -/
def ArmNormal.traceTree {L : List Sorts} (a : ArmNormal L) (b : Bool) :
    Reply.Normal (Exits.Exit L) :=
  a.emits.foldr Reply.Normal.emit (.ret (a.result b))

/-- Two consecutive observations describe the reply to one request. -/
def requestTree {R : Type} (req : Bool) (l r : Bool → Reply.Normal R) : Reply.Normal R :=
  .ask req (.ask req (l false) (l true)) (.ask req (r false) (r true))

def Normal.traceTree {L : List Sorts} (p : Normal L) : Reply.Normal (Exits.Exit L) :=
  requestTree p.request p.left.traceTree p.right.traceTree

def Normal.outcomes {L : List Sorts} (p : Normal L) : Set (Outcome (value (packedExitType L))) :=
  p.traceTree.outcomesWith Exits.Exit.packed

/-- Select both fields of the request's reply and remove them from the trace. -/
def afterPayload {A : Type} (req right b : Bool) (s : Set (Outcome A)) : Set (Outcome A) :=
  afterReply req b (afterReply req right s)

noncomputable def programOutcomes (H : Sorts) (L : List Sorts) (p : ProgramBody (H :: L)) :
    Set (Outcome (value (packedExitType (H :: L)))) :=
  (Kleisli.run model (program H L p).toLetCase.2
    (boundEnv value (β := .nil) PUnit.unit)).outcomes

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
