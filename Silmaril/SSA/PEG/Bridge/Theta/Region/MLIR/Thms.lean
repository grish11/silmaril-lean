module

public import Silmaril.SSA.PEG.Bridge.Theta.Region.MLIR.Defs
public import Silmaril.SSA.PEG.Bridge.Theta.Region.Tuple.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Theta.Operational.Thms
public import Silmaril.SSA.MLIR.SCF.While.Thms
import Silmaril.Proofs.SSA.PEG.Bridge.Theta.Region.MLIR.Correctness

public section

namespace Silmaril.SSA.PEG.Bridge.Theta.Region.MLIR

open Silmaril.MLIR.Arith (Env)
open Silmaril.MLIR.Pure (Eval)
open RVSDG (Port Tuple)
open RVSDG.LambdaSSA.Theta
open Silmaril.SSA.PEG.Bridge.Theta.Region.Ordered (Bundle)

variable {Data : Type} {P : InstructionSet.{0,0} Data}
variable {carried : List (Ty Data)} {t : Ty Data} {n : Nat}
variable {g : Graph P carried carried n 1} {slot : Port carried t} {invariants : Bool}
variable (profile : Profile Data) (evalOp : Eval (Opcode profile P)) (b : Bundle g slot invariants)

theorem Profile.encode_decode (ts : List (Ty Data)) (env : Env (profile.widths ts)) :
    profile.encode (profile.decode ts env) = env :=
  Proofs.encode_decode profile ts env

/-- Each SCF tick matches one numbered θ activation, including the final
stopping tick. Target results decode to numbered RVSDG packets in order. -/
theorem run_eq (fuel : Nat) (input : Env (profile.widths carried)) :
    let m := model profile evalOp
    ((lower profile b).run evalOp fuel input).map (fun result => encode m (profile.decode carried result)) =
      Operational.runFuel (Region.model m) b.compile fuel (encode m (profile.decode carried input)) :=
  Proofs.run_eq profile evalOp b fuel input

theorem returns_iff_numbered (input output : Env (profile.widths carried)) :
    let m := model profile evalOp
    (∃ fuel, (lower profile b).run evalOp fuel input = some output) ↔
      b.compile.Returns (Region.model m) (encode m (profile.decode carried input))
        (encode m (profile.decode carried output)) :=
  Proofs.returns_iff_numbered profile evalOp b input output

variable (neg : ∀ flag : Bool,
  (model profile evalOp).run b.scalar.descriptor.negate (.cons ⟨flag⟩ .nil) = ⟨!flag⟩)

include neg

/-- An actual finite structured MLIR return agrees exactly with the fully
defined ordered Figure 11 observation in the induced primitive model. -/
theorem returns_iff_observe (input output : Env (profile.widths carried)) (idx : Index 1) :
    let m := model profile evalOp
    (∃ fuel, (lower profile b).run evalOp fuel input = some output) ↔
      g.observe m.toPEG (g.denote m.toPEG (profile.decode carried input) b.demandWellFounded) idx =
        (profile.decode carried output).map (fun _ => some) :=
  (returns_iff_numbered profile evalOp b input output).trans
    (b.returns_iff_observe (model profile evalOp) (profile.decode carried input) neg idx
      (profile.decode carried output))

/-- The existing SCF-to-CF lowering gives the same complete observation
with a real typed backedge from the after region to before. -/
theorem cf_returns_iff_observe (input output : Env (profile.widths carried)) (idx : Index 1) :
    let m := model profile evalOp
    (∃ fuel, (lower profile b).lower.run evalOp fuel input = some output) ↔
      g.observe m.toPEG (g.denote m.toPEG (profile.decode carried input) b.demandWellFounded) idx =
        (profile.decode carried output).map (fun _ => some) :=
  ((lower profile b).lower_returns_iff evalOp input output).trans
    (returns_iff_observe profile evalOp b neg input output idx)

/-- A finite MLIR return witnesses a common first pass and the defined
Figure 11 eval prefix at every carried slot. -/
theorem firstExit_of_run (input output : Env (profile.widths carried)) (idx : Index 1)
    (fuel : Nat) (ran : (lower profile b).run evalOp fuel input = some output) :
    let m := model profile evalOp
    ∃ (k : Nat) (final : Tuple m.toPEG.Value (.bool :: carried)),
      carriedValues final = profile.decode carried output ∧
        b.scalar.TraceObservation m.toPEG
          (g.denote m.toPEG (profile.decode carried input) b.demandWellFounded) idx k final :=
  Proofs.firstExit_of_run profile evalOp b neg input output idx fuel ran

end Silmaril.SSA.PEG.Bridge.Theta.Region.MLIR
