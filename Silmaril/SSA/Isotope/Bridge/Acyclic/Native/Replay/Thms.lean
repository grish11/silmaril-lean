module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Model.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Native.Replay

/-! # Soundness and the exact replay premise for native completeness -/

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native

open Region (ValueBranches)
open Region.Paper
open LetCase.Structural.Finite (Types Context StructuralContext)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ] {n : Nat} {β : Context n} {A : Types}

/-- The existing opt-in native relation preserves the original region arrows. -/
theorem Endpoint.joined_sound {p q : Endpoint Φ β A} (h : p.JoinedEqv q) : p.Valid q :=
  joined_sound_proof h

/-- Replay the existing syntactic round trip at a specified exact code
witness of the original guarded endpoint. -/
theorem Endpoint.joined_roundTrip_at (p : Endpoint Φ β A) (c : Code Φ β A)
    (written : c.toSSA 0 = p.region) (admitted : c.Admitted) (guarded : ValueBranches β.toList p.region [A]) :
    Extension.Eqv (WithCaseAndUnaryReturns.JoinedStep false) β.toList
      p.region ((Code.ofLetCase c.toLetCase.2).guardedSSA 0) [A] :=
  joined_roundTrip_at_proof p c written admitted guarded

/-- The checked syntactic round trip applies at original constructor-branch
endpoints when their selected code meets the existing operand restriction. -/
theorem Endpoint.joined_roundTrip (p : Endpoint Φ β A) (admitted : p.code.Admitted)
    (guarded : ValueBranches β.toList p.region [A]) :
    Extension.Eqv (WithCaseAndUnaryReturns.JoinedStep false) β.toList
      p.region ((Code.ofLetCase p.compile.2).guardedSSA 0) [A] :=
  p.joined_roundTrip_at p.code p.code_exact admitted guarded

/-- On the admitted guarded subfragment only the replay of the exact
compiled LetCase equation is needed after the two checked round trips. -/
theorem Endpoint.joined_iff_valid_of_replay (input : StructuralContext β)
    (p q : Endpoint Φ β A) (hp : p.code.Admitted) (hq : q.code.Admitted)
    (gp : ValueBranches β.toList p.region [A]) (gq : ValueBranches β.toList q.region [A])
    (replay : p.ReificationReplay q) : p.JoinedEqv q ↔ p.Valid q :=
  joined_iff_valid_of_replay_proof input p q hp hq gp gq replay

end Silmaril.Isotope.LambdaSSA.Acyclic.Native
