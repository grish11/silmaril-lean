module

public import Silmaril.SSA.Peggy.Bridge.Theta.Defs
public import Silmaril.SSA.RVSDG.Theta.Categorical.Thms
public import Silmaril.SSA.RVSDG.Categorical.Thms
import Silmaril.SSA.PEG.Bridge.RVSDG.Thms

public section

namespace Silmaril.SSA.Peggy.Bridge.Theta.Proofs

open PEG.Bridge (valuePorts fromPorts to_fromPorts)
open PEG.Bridge.Theta.Region (encode)
open RVSDG (Tuple)

set_option backward.isDefEq.respectTransparency false

variable {Data : Type} {S : Signature Data} {carried : List (PEG.Ty Data)}
variable (m : Model S)

private theorem side_returns (s : Side S carried)
    (input output : Tuple m.val.toPEG.Value carried) (idx : PEG.Index 1) :
    s.val.code.2.Returns (thetaModel m) (encode m.val input) (encode m.val output) ↔
      s.val.peg.observe m.val.toPEG (s.val.peg.denote m.val.toPEG input s.wf) idx =
        output.map (fun _ => some) := by
  obtain ⟨_, _, _, b, marked, compiled⟩ := s.property
  rw [← compiled]
  have neg (flag : Bool) : m.val.run b.scalar.descriptor.negate (.cons ⟨flag⟩ .nil) = ⟨!flag⟩ := by
    rw [marked]
    exact m.property flag
  exact b.returns_iff_observe m.val input neg idx output

private theorem diverges_iff {sigs : List (List (PEG.Bridge.ValuePort Data))}
    (g : RVSDG.Theta.Graph (PEG.Bridge.Theta.Region.Opcode S.dialect.ops) (valuePorts carried) sigs)
    (input : Tuple (thetaModel m).Val (valuePorts carried)) :
    g.Diverges (thetaModel m) input ↔ ∀ output, ¬ g.Returns (thetaModel m) input output := by
  rw [← g.denotePart_eq_none, _root_.Part.eq_none_iff]
  constructor
  · intro none output returned
    exact none _ ((g.mem_denotePart _ _ _).mpr returned)
  · intro none value mem
    let output := RVSDG.Categorical.unpack (valuePorts carried) value
    have packed : RVSDG.Categorical.pack output = value := RVSDG.Categorical.pack_unpack _ _
    exact none output ((g.mem_denotePart _ _ _).mp (packed ▸ mem))

/-- The genuine θ institution observes divergence as well as finite tuples.
For these total deterministic bodies, the divergence clause follows from
agreement of the finite-return relations. -/
theorem satisfaction (e : Equation S) :
    e.translate.Holds (thetaModel m) ↔ e.Holds m := by
  constructor
  · intro holds input idx output
    exact (side_returns m e.lhs input output idx).symm.trans
      (((holds (encode m.val input)).1 (encode m.val output)).trans
        (side_returns m e.rhs input output idx))
  · intro holds input
    have agree (output : Tuple (thetaModel m).Val (valuePorts e.carried)) :
        e.translate.lhs.Returns (thetaModel m) input output ↔
        e.translate.rhs.Returns (thetaModel m) input output := by
      let entry := fromPorts (F := (thetaModel m).Val) e.carried input
      let result := fromPorts (F := (thetaModel m).Val) e.carried output
      let idx : PEG.Index 1 := fun _ => 0
      have related := (side_returns m e.lhs entry result idx).trans
        ((holds entry idx result).trans (side_returns m e.rhs entry result idx).symm)
      simpa only [entry, result, encode, to_fromPorts, Equation.translate] using related
    refine ⟨agree, ?_⟩
    rw [diverges_iff, diverges_iff]
    exact ⟨fun h out ran => h out ((agree out).mpr ran), fun h out ran => h out ((agree out).mp ran)⟩

end Silmaril.SSA.Peggy.Bridge.Theta.Proofs
