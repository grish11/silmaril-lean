module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.ExitUB.Defs

/-! # One-request native CFGs with ordered exits and literal UB -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.SingleRequest

open Category.FiniteIteration.Syntax (Primitives Program)
open Category.FiniteIteration.CFG.Dependent

abbrev U : Silmaril.Ty Empty := .unit
abbrev Exits : List (Silmaril.Ty Empty) := List.replicate 2 U

inductive Instr where
  | request

instance : HasTy Instr (Silmaril.Ty Empty) := ⟨fun _ => U, fun _ => U⟩

/-- A closed request followed by one native block. On reply, the block can
forward the reply or return literal unit to either ordered exit. -/
structure Endpoint where
  exit : Fin 2
  forward : Bool
  ub : Bool

def request : Native.Typed Instr [] [U] :=
  Program.requestRegion .request .unit

theorem exit_type (i : Fin Exits.length) : Exits.get i = U := by simp

def Endpoint.router (p : Endpoint) : Native.Typed Instr [U] Exits :=
  Native.jump p.exit (exit_type p.exit) (if p.forward then .var 0 else .unit)

def Endpoint.native (p : Endpoint) : Native.Typed Instr [] Exits :=
  Native.bind request p.router

/-- The unused exit always has a literal UB continuation. The router can
also designate its actual exit as UB. -/
def Endpoint.selected (p : Endpoint) (i : Fin Exits.length) : Bool :=
  if i = p.exit then p.ub else true

def Endpoint.region (p : Endpoint) : Overlay.Region Instr [] Exits :=
  Native.withExitUB p.native p.selected

universe v w

/-- The response continuation at a raw reply. The shared request can also
fault or diverge before reaching this continuation. -/
def Endpoint.afterReply {α : Type v} {σ : Type w} (p : Endpoint) (a : Value α) (s : σ) :
    Behaviour Exits.length α σ :=
  if p.ub then ⊤ else WithTop.some {Outcome.ret p.exit (if p.forward then a else .unit) s}

/-- The candidate order on shaped response normal forms. A successful unit
reply is unique, and an ordinary return retains its exit position. -/
def ReplyRefines (p q : Endpoint) : Prop :=
  q.ub = true ∨ (p.ub = false ∧ p.exit = q.exit)

/-- In the unrestricted model, forwarding the raw reply is observable. -/
def RawReplyRefines (p q : Endpoint) : Prop :=
  q.ub = true ∨ (p.ub = false ∧ p.exit = q.exit ∧ p.forward = q.forward)

/-- One finite test replies with unit and can change the state. -/
def unitInterpreter {states : Nat} (final : Fin states) : Primitives Instr states :=
  fun _ _ _ => .ret ⟨.unit, .unit⟩ final

/-- A finite raw model whose successful unit-typed opcode reply has sum shape. -/
abbrev rawProbe : Institution.Observational.Model Instr 0 where
  α := Unit
  σ := Fin 2
  instr := fun _ _ _ b t => b = .inl .unit ∧ t = 1
  faults := fun _ _ _ _ => False
  prim := fun _ _ _ => False
  bound := fun i => i.elim0

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.SingleRequest
