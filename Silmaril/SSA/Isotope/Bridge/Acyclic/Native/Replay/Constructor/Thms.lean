module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Constructor.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Native.Replay.Constructor

/-! # Sound native replay for the constructor-sequencing join -/

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native

open Region (ValueBranches)
open Region.Paper
open UnaryReturn.Beta.Constructors (Normalizes)
open Morphism.CaseSSA (erase)
open LetCase.Structural.Finite (Context Types StructuralContext)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

section Operands

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε) {n : Nat} {β : BoundCtx τ n} {A : τ}

/-- The known operand round trip embeds in the combined relation. -/
theorem operand_roundTrip_constructor (a : Operand Φ β A) (h : a.Admitted) :
    WithConstructorSequencing.Joined.Eqv pe β.toList ((Code.br a).guardedSSA 0)
      ((Code.ofLetCase a.2).guardedSSA 0) [A] :=
  operand_roundTrip_proof pe a h

/-- Every exact constructor-and-unary-let operand replays its native
normalization at the reified guarded endpoint. The constructor can still
refer to the original open slots. -/
theorem constructor_replay (a : Operand Φ β A) (h : ConstructorOnly (erase a.1)) :
    ∃ v, Normalizes β.toList (erase a.1) v A ∧
      WithConstructorSequencing.Joined.Eqv pe β.toList ((Code.ofLetCase a.2).guardedSSA 0) (.br 0 v) [A] :=
  constructor_replay_proof pe a h

end Operands

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ] {n : Nat} {β : Context n} {A : Types}

/-- At the original guarded endpoint a constructor-only compilation
suffices for native normalization, including captured variables. Its syntax
already satisfies the operand restrictions of the guarded round trip. -/
theorem Endpoint.constructor_normalizes (p : Endpoint Φ β A)
    (guarded : ValueBranches β.toList p.region [A]) (shape : ConstructorOnly (erase p.compile.1)) :
    ∃ v, Normalizes β.toList (erase p.compile.1) v A ∧
      WithConstructorSequencing.Joined.Eqv false β.toList p.region (.br 0 v) [A] :=
  constructor_normalizes_proof p guarded shape

/-- Soundness at all original outward endpoints, including arbitrary typed operands. -/
theorem Endpoint.constructor_sound {p q : Endpoint Φ β A} (h : p.ConstructorEqv q) : p.Valid q :=
  constructor_sound_proof h

/-- If the two exact compiled operands admit replay, the original guarded
round trips discharge the remaining translation steps. -/
theorem Endpoint.constructor_iff_valid_of_replay (input : StructuralContext β)
    (p q : Endpoint Φ β A) (hp : p.code.Admitted) (hq : q.code.Admitted)
    (gp : ValueBranches β.toList p.region [A]) (gq : ValueBranches β.toList q.region [A])
    (replay : ConstructorReplay p.compile q.compile) : p.ConstructorEqv q ↔ p.Valid q :=
  constructor_iff_valid_of_replay_proof input p q hp hq gp gq replay

end Silmaril.Isotope.LambdaSSA.Acyclic.Native
