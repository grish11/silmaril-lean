module

public import Silmaril.Machine.Vex.Validate.Defs
import Silmaril.Proofs.Machine.Vex.Validate.Sound

public section

namespace Silmaril.Machine.Vex

theorem boundary_beh {input output : Type} (run : input → output) (entry : input)
    (outcome : Behaviour.Outcome output Empty Empty) :
    (boundarySem run).Beh entry outcome ↔ outcome = .returned (run entry) :=
  Proofs.boundaryBeh run entry outcome

theorem boundary_refines {srcInit tgtInit observation : Type}
    (source : srcInit → observation) (target : tgtInit → observation)
    (initial : srcInit → tgtInit → Prop)
    (agree : ∀ src tgt, initial src tgt → source src = target tgt) :
    Behaviour.Refines .strict (boundarySem target) (boundarySem source)
      (fun tgt src => initial src tgt) (fun _ _ => Behaviour.Obs.id) :=
  Proofs.boundaryRefines source target initial agree

end Silmaril.Machine.Vex

namespace Silmaril.Machine.Vex.AMD64Scalar

theorem Term.selectBit_sound (input : Input) (index : Nat) (term : Term) :
    (term.selectBit index).eval input = flagWord ((term.eval input).getLsbD index) :=
  Proofs.selectBit input index term

theorem X86.Block.lower_sound (block : X86.Block) (input : Input) :
    (block.lower input.rip).eval input = block.run input := Proofs.x86Lower block input

theorem validate_artifacts {pc : Word} {bytes : List UInt8} {raw : Raw.Block} {pair : Pair}
    (accepted : validate pc bytes raw = .ok pair) :
    X86.decode pc bytes = .ok pair.source ∧ check raw = .ok pair.target ∧
    pair.target.address = pc ∧ pair.target.code.marks = pair.source.marks ∧
    pair.target.lower = .ok (pair.source.lower pc) := Proofs.artifacts accepted

/-- All register values and both incoming ZF values, at the common entry PC. -/
theorem validate_sound {pc : Word} {bytes : List UInt8} {raw : Raw.Block} {pair : Pair}
    (accepted : validate pc bytes raw = .ok pair) (input : Input) (entry : input.rip = pc) :
    pair.target.run input = .ok (pair.source.run input) := Proofs.validateSound accepted input entry

theorem validate_boundary {pc : Word} {bytes : List UInt8} {raw : Raw.Block} {pair : Pair}
    (accepted : validate pc bytes raw = .ok pair) :
    BoundaryAgreement pair.source.run pair.target.run (Initial pc) Final
      (fun state => some (observe state)) (fun result => result.toOption.map observe) :=
  Proofs.validateBoundary accepted

theorem validate_refines {pc : Word} {bytes : List UInt8} {raw : Raw.Block} {pair : Pair}
    (accepted : validate pc bytes raw = .ok pair) :
    ∃ plan, pair.target.lower = .ok plan ∧
      Behaviour.Refines .strict (boundarySem (fun input => plan.eval input))
        (boundarySem pair.source.run) (fun tgt src => Initial pc src tgt)
        (fun _ _ => Behaviour.Obs.id) :=
  Proofs.validateRefines accepted

theorem check_word_erase {ctx : Scope} (value : Word) :
    checkExpr ctx ((Expr.word (ctx := ctx) value).erase) = .ok ⟨.i64, Expr.word value⟩ :=
  Proofs.wordErasure value

end Silmaril.Machine.Vex.AMD64Scalar
