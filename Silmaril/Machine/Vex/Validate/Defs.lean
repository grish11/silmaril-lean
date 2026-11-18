module

public import Silmaril.Machine.Vex.X86.Defs
public import Silmaril.Machine.CBackend.Behaviour.Refinement.Defs

/-! # One-boundary translation validation -/

@[expose] public section

namespace Silmaril.Machine.Vex

/-- Shared contract for terminating segments. Final relations can express
representation invariants separately from externally compared observations. -/
def BoundaryAgreement {srcInit tgtInit srcFinal tgtFinal observation : Type}
    (source : srcInit → srcFinal) (target : tgtInit → tgtFinal)
    (initial : srcInit → tgtInit → Prop) (final : srcFinal → tgtFinal → Prop)
    (srcObs : srcFinal → observation) (tgtObs : tgtFinal → observation) : Prop :=
  ∀ src tgt, initial src tgt → final (source src) (target tgt) ∧ srcObs (source src) = tgtObs (target tgt)

/-- Lift a total boundary evaluator to the existing strict behavior framework.
It has exactly one returned outcome, no steps, and cannot exhibit UB, fault,
or divergence. Only use this for already accepted, total segments. -/
def boundarySem {input output : Type} (run : input → output) :
    Behaviour.Semantics input output Empty Empty where
  step := fun _ _ => False
  final := fun state outcome => outcome = .returned (run state)

namespace AMD64Scalar

inductive ValidationError where
  | vex (error : Error)
  | x86 (error : X86.DecodeError)
  | observation (error : ObservationError)
  | address
  | marks
  | differentPlan
  deriving DecidableEq, Repr

structure Pair where
  source : X86.Block
  target : Block

def Initial (pc : Word) (source target : Input) : Prop := source = target ∧ source.rip = pc

def Final (source : Input) (target : Except ObservationError Input) : Prop :=
  ∃ result, target = .ok result ∧ result.rip = source.rip

def observe (state : Input) : Word × Word × Word × Bool :=
  (state.rax, state.rdi, state.rsi, state.zf)

/-- A sound, deliberately incomplete test: both artifacts must produce the
same residual observation plan. No input enumeration or UB assumption. -/
def validate (pc : Word) (bytes : List UInt8) (raw : Raw.Block) : Except ValidationError Pair :=
  match X86.decode pc bytes with
  | .error error => .error (.x86 error)
  | .ok source => match check raw with
    | .error error => .error (.vex error)
    | .ok target =>
      if target.address ≠ pc then .error .address
      else if source.marks ≠ target.code.marks then .error .marks
      else match target.lower with
        | .error error => .error (.observation error)
        | .ok plan =>
          if source.lower pc ≠ plan then .error .differentPlan else .ok ⟨source, target⟩

end AMD64Scalar
end Silmaril.Machine.Vex
