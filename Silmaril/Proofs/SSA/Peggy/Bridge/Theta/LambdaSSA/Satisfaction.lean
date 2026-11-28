module

public import Silmaril.SSA.Peggy.Bridge.Theta.LambdaSSA.Defs
import Silmaril.SSA.PEG.Bridge.RVSDG.Thms

public section

namespace Silmaril.SSA.Peggy.Bridge.Theta.LambdaSSA.Proofs

open PEG.Bridge (fromPorts from_toPorts)
open PEG.Bridge.Theta.Region (encode)
open PEG.Bridge.Theta.Region.LambdaSSA (lower_eval_iff)
open RVSDG (Tuple)
open RVSDG.LambdaSSA.Theta

set_option backward.isDefEq.respectTransparency false

variable {Data : Type} {S : Signature Data} {carried : List (PEG.Ty Data)}

private theorem side_returns (r : Side S carried) (m : Model S)
    (input output : Tuple m.val.toPEG.Value carried) (idx : PEG.Index 1) :
    r.native.Returns m input output ↔
      r.peg.val.peg.observe m.val.toPEG (r.peg.val.peg.denote m.val.toPEG input r.peg.wf) idx =
        output.map (fun _ => some) := by
  obtain ⟨_, _, _, b, marked, _, native⟩ := r.checked
  have neg (flag : Bool) : m.val.run b.scalar.descriptor.negate (.cons ⟨flag⟩ .nil) = ⟨!flag⟩ := by
    rw [marked]
    exact m.property flag
  unfold Native.Code.Returns
  rw [← native]
  refine (lower_eval_iff b m.val input neg idx () () 0 _).trans ?_
  constructor
  · rintro ⟨other, observed, _, packetEq, _⟩
    have ports := Operational.pack_injective (thetaModel m) packetEq
    have values := congrArg (fromPorts (F := (thetaModel m).Val) carried) ports
    have ordered : output = other :=
      (from_toPorts (F := (thetaModel m).Val) output).symm.trans
        (values.trans (from_toPorts (F := (thetaModel m).Val) other))
    exact observed.trans (congrArg (Tuple.map fun _ => some) ordered.symm)
  · intro observed
    exact ⟨output, observed, rfl, rfl, rfl⟩

theorem checked_satisfaction (e : CheckedEquation S) (m : Model S) :
    e.native.Holds m ↔ e.peg.Holds m := by
  constructor
  · intro holds input idx output
    exact (side_returns e.lhs m input output idx).symm.trans
      ((holds input output).trans (side_returns e.rhs m input output idx))
  · intro holds input output
    let idx : PEG.Index 1 := fun _ => 0
    exact (side_returns e.lhs m input output idx).trans
      ((holds input idx output).trans (side_returns e.rhs m input output idx).symm)

theorem image_satisfaction (e : ThetaImage S) (m : Model S) :
    e.val.2.Holds m ↔ e.val.1.Holds (thetaModel m) := by
  obtain ⟨source, same⟩ := e.property
  rw [← same]
  exact (checked_satisfaction source m).trans (source.peg.satisfaction m).symm

end Silmaril.SSA.Peggy.Bridge.Theta.LambdaSSA.Proofs
