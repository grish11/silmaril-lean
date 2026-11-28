module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Constructor.Defs
import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Syntactic.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.Joined.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Thms

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native

open Region (ValueBranches)
open Region.Paper
open WithConstructorSequencing (returnOnce_eq_branch)
open UnaryReturn.Beta.Constructors (Normalizes)
open Morphism.CaseSSA (erase)
open LetCase.LocallyNameless (Derivation)
open LetCase.Structural.Finite (Context Types StructuralContext)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

set_option backward.isDefEq.respectTransparency false

section ConstructorReplay

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

private theorem constructor_normalizes {n : Nat} {β : BoundCtx τ n} {A : τ}
    {t : LetCase.LocallyNameless.Tm Empty Φ n}
    (d : Derivation Φ (.nil : Ctx Empty τ) β t A) (shape : ConstructorOnly (erase t)) :
    Operand.admittedDerivation d ∧ ∃ v, Normalizes β.toList (erase t) v A := by
  induction d with
  | @fv _ _ x _ _ => exact x.elim
  | bv =>
    exact ⟨trivial, _, .value (.var (BoundCtx.getElem?_toList _ _))⟩
  | unit => exact ⟨trivial, _, .value .unit⟩
  | let₁ _ _ iha ihb =>
    obtain ⟨oka, _, ha⟩ := iha shape.1
    obtain ⟨okb, _, hb⟩ := ihb shape.2
    exact ⟨⟨oka, okb⟩, _, .let₁ ha hb⟩
  | pair _ _ iha ihb =>
    obtain ⟨_, _, ha⟩ := iha shape.1
    obtain ⟨_, _, hb⟩ := ihb shape.2
    exact ⟨trivial, _, .pair ha hb⟩
  | inl _ ih =>
    obtain ⟨_, _, h⟩ := ih shape
    exact ⟨trivial, _, .inl h⟩
  | inr _ ih =>
    obtain ⟨_, _, h⟩ := ih shape
    exact ⟨trivial, _, .inr h⟩
  | op | let₂ | case | abort => exact shape.elim

private theorem code_admitted_of_constructorOnly {n : Nat} {β : BoundCtx τ n} {A : τ}
    (c : Code Φ β A) (shape : ConstructorOnly (erase c.toLetCase.1)) : c.Admitted := by
  induction c with
  | br a => exact (constructor_normalizes a.2 shape).1
  | let₁ a _ ih => exact ⟨(constructor_normalizes a.2 shape.1).1, ih shape.2⟩
  | join _ _ iha ihb => exact ⟨iha shape.1, ihb shape.2⟩
  | let₂ | case => exact shape.elim

/-- The operand round trip uses the existing unary-return and case seeds. -/
theorem operand_roundTrip_proof {n : Nat} {β : BoundCtx τ n} {A : τ}
    {ε : Type w} [HasEff Φ ε] (pe : ε) (a : Operand Φ β A) (ha : a.Admitted) :
    WithConstructorSequencing.Joined.Eqv pe β.toList
      ((Code.br a).guardedSSA 0) ((Code.ofLetCase a.2).guardedSSA 0) [A] :=
  WithProjectionReturnsAndUnitEta.WithBranchBinding.mapSeed
    (fun h => Or.inl (Or.inr h)) (a.syntactic_roundTrip pe ha rfl)

theorem constructor_replay_proof {n : Nat} {β : BoundCtx τ n} {A : τ}
    {ε : Type w} [HasEff Φ ε] (pe : ε) (a : Operand Φ β A) (shape : ConstructorOnly (erase a.1)) :
    ∃ v, Normalizes β.toList (erase a.1) v A ∧
      WithConstructorSequencing.Joined.Eqv pe β.toList ((Code.ofLetCase a.2).guardedSSA 0) (.br 0 v) [A] := by
  obtain ⟨admitted, v, normalizes⟩ := constructor_normalizes a.2 shape
  exact ⟨v, normalizes, (operand_roundTrip_proof pe a admitted).symm.trans
    (WithConstructorSequencing.Joined.ofConstructor (returnOnce_eq_branch normalizes))⟩

end ConstructorReplay

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ] {n : Nat} {β : Context n} {A : Types}

theorem Endpoint.constructor_normalizes_proof (p : Endpoint Φ β A)
    (guarded : ValueBranches β.toList p.region [A]) (shape : ConstructorOnly (erase p.compile.1)) :
    ∃ v, Normalizes β.toList (erase p.compile.1) v A ∧
      WithConstructorSequencing.Joined.Eqv false β.toList p.region (.br 0 v) [A] := by
  obtain ⟨v, normal, replay⟩ := constructor_replay_proof false p.compile shape
  have roundTrip := p.joined_roundTrip (code_admitted_of_constructorOnly p.code shape) guarded
  exact ⟨v, normal, (WithConstructorSequencing.Joined.ofJoined roundTrip).trans replay⟩

theorem Endpoint.constructor_sound_proof {p q : Endpoint Φ β A} (h : p.ConstructorEqv q) : p.Valid q := by
  intro V C vcat ccat cart sym prem symPrem sumV sumC distV distC iter elgot J freyd central
    M instr regionCoherent _ shared
  exact WithConstructorSequencing.Joined.sound J M shared h p.typed q.typed

theorem Endpoint.constructor_iff_valid_of_replay_proof (input : StructuralContext β)
    (p q : Endpoint Φ β A) (hp : p.code.Admitted) (hq : q.code.Admitted)
    (gp : ValueBranches β.toList p.region [A]) (gq : ValueBranches β.toList q.region [A])
    (replay : ConstructorReplay p.compile q.compile) : p.ConstructorEqv q ↔ p.Valid q := by
  refine ⟨Endpoint.constructor_sound_proof, fun h => ?_⟩
  exact (WithConstructorSequencing.Joined.ofJoined (p.joined_roundTrip hp gp)).trans
    ((replay ((p.valid_iff_compiled input q).mp h)).trans
      (WithConstructorSequencing.Joined.ofJoined (q.joined_roundTrip hq gq)).symm)

end Silmaril.Isotope.LambdaSSA.Acyclic.Native
