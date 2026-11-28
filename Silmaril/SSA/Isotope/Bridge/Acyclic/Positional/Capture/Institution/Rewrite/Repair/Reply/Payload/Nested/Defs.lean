module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Defs

/-! # Witnessed nested requests with a retained outer payload -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Nested

open Kleisli (value)
open LambdaSSA (At)
open LambdaSSA.Acyclic (Operand)
open LambdaSSA.Acyclic.Positional.Capture.Reverse (Program)
open LambdaSSA.Region (packedExitType)
open LetIter.Semantics.Categorical (boundEnv)

local notation "U" => (Ty.unit : Sorts)

/-- Dispatch on the inner bit. Each continuation has its own effects and
typed exit, and can return a function of the retained outer bit. -/
structure Inner (L : List Sorts) where
  whenFalse : Arm L
  whenTrue : Arm L

structure InnerNormal (L : List Sorts) where
  whenFalse : ArmNormal L
  whenTrue : ArmNormal L

def Inner.normal {L : List Sorts} (a : Inner L) : InnerNormal L :=
  ⟨a.whenFalse.normal, a.whenTrue.normal⟩

def InnerNormal.render {L : List Sorts} (a : InnerNormal L) : Inner L :=
  ⟨a.whenFalse.render, a.whenTrue.render⟩

def Inner.operand {L : List Sorts} (a : Inner L) {n : Nat}
    (β : BoundCtx Sorts n) (outer : Fin n) (h : β.get outer = Bit) :
    Operand signature.Instr (β.snoc Bit) (packedExitType L) :=
  let γ := (β.snoc Bit).snoc U
  let low := a.whenFalse.renderPrefix a.whenFalse.emits γ outer.succ.succ h
  let high := a.whenTrue.renderPrefix a.whenTrue.emits γ outer.succ.succ h
  ⟨.case (.bv 0) low.1 high.1, .case .bv low.2 high.2⟩

/-- The outer arm either finishes immediately or issues one further
effectful request, optionally after an ordered emit prefix. -/
inductive Outer (L : List Sorts) where
  | finish (arm : Arm L)
  | request (emits : List Bool) (label bound : Bool) (left right : Inner L)

inductive OuterNormal (L : List Sorts) where
  | finish (arm : ArmNormal L)
  | request (emits : List Bool) (label : Bool) (left right : InnerNormal L)

def Outer.normal {L : List Sorts} : Outer L → OuterNormal L
  | .finish a => .finish a.normal
  | .request es req _ l r => .request es req l.normal r.normal

def OuterNormal.render {L : List Sorts} : OuterNormal L → Outer L
  | .finish a => .finish a.render
  | .request es req l r => .request es req false l.render r.render

def requestWithPrefix {L : List Sorts} (req bound : Bool) (l r : Inner L) :
    List Bool → {n : Nat} → (β : BoundCtx Sorts n) → (outer : Fin n) →
      β.get outer = Bit → Operand signature.Instr β (packedExitType L)
  | [], _, β, i, h => requestOperand req bound (l.operand β i h) (r.operand β i h)
  | e :: es, _, β, i, h =>
    let k := requestWithPrefix req bound l r es (β.snoc U) i.succ h
    ⟨.let₁ (.op (.emit e) .unit) k.1, .let₁ (.op .unit) k.2⟩

def Outer.operand {L : List Sorts} (a : Outer L) :
    Operand signature.Instr (.snoc .nil Bit) (packedExitType L) :=
  match a with
  | .finish arm => arm.operand .nil
  | .request es req bound l r => requestWithPrefix req bound l r es (.snoc .nil Bit) 0 rfl

structure ProgramBody (L : List Sorts) where
  request : Bool
  bound : Bool
  left : Outer L
  right : Outer L

structure Normal (L : List Sorts) where
  request : Bool
  left : OuterNormal L
  right : OuterNormal L

def ProgramBody.normal {L : List Sorts} (p : ProgramBody L) : Normal L :=
  ⟨p.request, p.left.normal, p.right.normal⟩

def Normal.render {L : List Sorts} (p : Normal L) : ProgramBody L :=
  ⟨p.request, false, p.left.render, p.right.render⟩

def ProgramBody.entry {L : List Sorts} (p : ProgramBody L) :
    Operand signature.Instr .nil (packedExitType L) :=
  requestOperand p.request p.bound p.left.operand p.right.operand

def program (H : Sorts) (L : List Sorts) (p : ProgramBody (H :: L)) :
    Program signature.Instr .nil (H :: L) :=
  ⟨packedExitType (H :: L), p.entry,
    Exits.router (rfl : At (H :: L) 0 H) (H :: L) (LambdaSSA.Ren.id (H :: L))⟩

def equation (H : Sorts) (L : List Sorts) (p q : ProgramBody (H :: L)) : GrammarEquation signature :=
  ⟨⟨0, .nil, H :: L⟩, program H L p, program H L q⟩

def InnerNormal.traceTree {L : List Sorts} (a : InnerNormal L) (outer inner : Bool) :
    Reply.Normal (Exits.Exit L) :=
  (if inner then a.whenTrue else a.whenFalse).traceTree outer

def OuterNormal.traceTree {L : List Sorts} (a : OuterNormal L) (outer : Bool) :
    Reply.Normal (Exits.Exit L) :=
  match a with
  | .finish arm => arm.traceTree outer
  | .request es req l r =>
    es.foldr Reply.Normal.emit (requestTree req (l.traceTree outer) (r.traceTree outer))

def Normal.traceTree {L : List Sorts} (p : Normal L) : Reply.Normal (Exits.Exit L) :=
  requestTree p.request p.left.traceTree p.right.traceTree

def Normal.outcomes {L : List Sorts} (p : Normal L) : Set (Outcome (value (packedExitType L))) :=
  p.traceTree.outcomesWith Exits.Exit.packed

noncomputable def programOutcomes (H : Sorts) (L : List Sorts) (p : ProgramBody (H :: L)) :
    Set (Outcome (value (packedExitType (H :: L)))) :=
  (Kleisli.run model (program H L p).toLetCase.2
    (boundEnv value (β := .nil) PUnit.unit)).outcomes

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Nested
