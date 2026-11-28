module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Defs
import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Model.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Syntactic.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseAndUnaryReturns.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Thms

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native

open Region (ValueBranches)
open Region.Paper
open LetCase.Structural.Finite (Types Context StructuralContext)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ] {n : Nat} {β : Context n} {A : Types}

theorem Endpoint.joined_sound_proof {p q : Endpoint Φ β A} (h : p.JoinedEqv q) : p.Valid q := by
  intro V C vcat ccat cart sym prem symPrem sumV sumC distV distC iter elgot J freyd central
    M instr regionCoherent _ shared
  exact WithCaseAndUnaryReturns.joined_eqv_sound false J M shared h p.typed q.typed

theorem Endpoint.joined_roundTrip_at_proof (p : Endpoint Φ β A) (c : Code Φ β A)
    (written : c.toSSA 0 = p.region) (admitted : c.Admitted) (guarded : ValueBranches β.toList p.region [A]) :
    Extension.Eqv (WithCaseAndUnaryReturns.JoinedStep false) β.toList
      p.region ((Code.ofLetCase c.toLetCase.2).guardedSSA 0) [A] := by
  rw [← written] at guarded
  have replay := c.syntactic_roundTrip_of_valueBranches false admitted rfl guarded
  have lifted := WithProjectionReturnsAndUnitEta.WithBranchBinding.mapSeed
    (Target := WithCaseAndUnaryReturns.JoinedStep false) (fun h => Or.inr h) replay
  rw [written] at lifted
  exact lifted

theorem Endpoint.joined_iff_valid_of_replay_proof (input : StructuralContext β)
    (p q : Endpoint Φ β A) (hp : p.code.Admitted) (hq : q.code.Admitted)
    (gp : ValueBranches β.toList p.region [A]) (gq : ValueBranches β.toList q.region [A])
    (replay : p.ReificationReplay q) : p.JoinedEqv q ↔ p.Valid q := by
  refine ⟨Endpoint.joined_sound_proof, fun h => ?_⟩
  exact (p.joined_roundTrip_at_proof p.code p.code_exact hp gp).trans
    ((replay ((p.valid_iff_compiled input q).mp h)).trans (q.joined_roundTrip_at_proof q.code q.code_exact hq gq).symm)

end Silmaril.Isotope.LambdaSSA.Acyclic.Native
