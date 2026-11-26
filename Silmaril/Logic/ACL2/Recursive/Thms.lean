module

public import Silmaril.Logic.ACL2.Recursive.Certificate
import Silmaril.Proofs.Logic.ACL2.Recursive.Admission
import Silmaril.Proofs.Logic.ACL2.Recursive.Certificate

@[expose] public section

namespace Silmaril.Logic.ACL2.Recursive

variable {S : Signature} {B : Block S} {M : Model S} {rank : Rank M B.members}

theorem Block.model_reduct (h : B.Terminates M rank) :
    (B.model M rank h).reduct B.inclusion = M :=
  Proofs.Logic.ACL2.Recursive.model_reduct B M rank h

theorem Block.eval_map (h : B.Terminates M rank) {n : Nat} (env : Env M n) (term : Term S n) :
    (term.map B.inclusion).eval (B.model M rank h) env = term.eval M env :=
  Proofs.Logic.ACL2.Recursive.eval_map B M rank h env term

theorem Block.model_interpret (h : B.Terminates M rank)
    (state : Call B.members M.primitives.Value) :
    (B.model M rank h).interpret (B.symbol state.symbol) state.args = B.interpret M rank h state :=
  Proofs.Logic.ACL2.Recursive.model_interpret B M rank h state

theorem Block.interpret_unfold (h : B.Terminates M rank) (state : Call B.members M.primitives.Value) :
    B.interpret M rank h state =
      (B.body state.symbol).eval M rank (rank state) state.args
        (fun next _ => B.interpret M rank h next) (h state) :=
  Proofs.Logic.ACL2.Recursive.interpret_unfold B M rank h state

theorem Block.equation_holds (h : B.Terminates M rank) {k : Nat} (f : B.members.Symbol k) :
    (B.equation f).Holds (B.model M rank h) :=
  Proofs.Logic.ACL2.Recursive.equation B M rank h f

/-- The induction hypotheses are for exactly the recursive call positions on the chosen paths. -/
theorem Block.callInduction (h : B.Terminates M rank) (p : Call B.members M.primitives.Value → Prop)
    (step : ∀ state, (B.body state.symbol).CallsSatisfy M state.args p → p state) :
    ∀ state, p state :=
  Proofs.Logic.ACL2.Recursive.callInduction B M rank h p step

theorem BlockCertificate.terminates (size : CdrSize M.primitives)
    (arg : MeasureArgument B.members) (cert : BlockCertificate B)
    (accepted : cert.Accepted B arg) : B.Terminates M (size.rank arg) :=
  Proofs.Logic.ACL2.Recursive.accepted_terminates B size arg cert accepted

end Silmaril.Logic.ACL2.Recursive
