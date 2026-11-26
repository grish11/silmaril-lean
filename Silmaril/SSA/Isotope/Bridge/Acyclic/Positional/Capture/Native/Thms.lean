module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Native.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Native.Graph
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Native.Packed

/-! # Native round trips at the original ordered graph interfaces -/

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture

open Region.Paper

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {d n : Nat} {β : BoundCtx τ d} {L : LCtx τ}

/-- Unfold a checked table at its actual entry by once-bound CFG η and local
branch β. Each ambient capture and outward label retains its type and position. -/
theorem Table.toFiniteExit_replay (p : Table Φ β L n) (ok : p.check = true)
    (i : Fin (n + 1)) (a : Operand Φ β (p.types i)) :
    WithBoundEntryEta.Eqv β.toList (p.toSSA i a) (p.toFiniteExit ok i a).toSSA L :=
  toFiniteExit_replay_proof p ok i a

/-- The actual LetCase result supplies its own grammar witness via the rank.
The numbered reconstruction returns the same packed term and is natively
equivalent to the original graph at its ordered exits. -/
theorem Table.native_roundTrip (p : Table Φ β L n) (ok : p.check = true)
    (i : Fin (n + 1)) (a : Operand Φ β (p.types i)) :
    WithBoundEntryEta.Eqv β.toList (p.toSSA i a) (Reverse.tableGrammar p ok i a).toTable.toSSA L ∧
      (Reverse.tableGrammar p ok i a).toTable.toLetCase = p.toLetCase ok i a :=
  ⟨native_roundTrip_proof p ok i a, (Reverse.tableGrammar p ok i a).toTable_toLetCase⟩

/-- Packing both graphs keeps the ordered tags at the same singleton result. -/
theorem Table.native_roundTrip_packed (p : Table Φ β L n) (ok : p.check = true)
    (i : Fin (n + 1)) (a : Operand Φ β (p.types i)) :
    WithBoundEntryEta.Eqv β.toList (p.toSSA i a).bindBranchArguments.packExits
      (Reverse.tableGrammar p ok i a).toTable.toSSA.bindBranchArguments.packExits [Region.packedExitType L] :=
  bind_pack_eq_proof (p.native_roundTrip ok i a).1

section Packed

universe w

variable {α : Type u} {Ψ : Type v} [HasTy Ψ (Ty α)] {ε : Type w} [HasEff Ψ ε] {pe : ε}
  {d n : Nat} {γ : BoundCtx (Ty α) d} {K : LCtx (Ty α)}

/-- Native replay from the original checked positional graph, with its ordered
exits packed, to the actual structured SSA reifier of its emitted LetCase term.
The rank and recursive operand derivations supply all replay witnesses. -/
theorem Table.toLetCase_reify (p : Table Ψ γ K n) (ok : p.check = true)
    (i : Fin (n + 1)) (a : Operand Ψ γ (p.types i)) :
    ReplayEqv pe γ.toList (p.toSSA i a).bindBranchArguments.packExits
      ((Code.ofLetCase (p.toLetCase ok i a).2).guardedSSA 0) [Region.packedExitType K] :=
  packed_reify_proof p ok i a

/-- Complete the packed syntactic round trip through the structured reifier
and the existing numbered inverse, using the actual emitted LetCase term. -/
theorem Table.native_recompile (p : Table Ψ γ K n) (ok : p.check = true)
    (i : Fin (n + 1)) (a : Operand Ψ γ (p.types i)) :
    ReplayEqv pe γ.toList (p.toSSA i a).bindBranchArguments.packExits
        ((Code.ofLetCase (p.toLetCase ok i a).2).guardedSSA 0) [Region.packedExitType K] ∧
      ReplayEqv pe γ.toList ((Code.ofLetCase (p.toLetCase ok i a).2).guardedSSA 0)
        (Reverse.tableGrammar p ok i a).toTable.toSSA.bindBranchArguments.packExits [Region.packedExitType K] ∧
      (Reverse.tableGrammar p ok i a).toTable.toLetCase = p.toLetCase ok i a :=
  ⟨p.toLetCase_reify ok i a, packed_recompile_proof p ok i a,
    (Reverse.tableGrammar p ok i a).toTable_toLetCase⟩

open CategoryTheory CategoryTheory.Limits
open LambdaSSA.Semantics.Categorical (RegionTypingCoherent denoteRegion)
open LetIter.Semantics.Categorical (TypeModel InstructionModel)
open scoped MonoidalCategory

universe u₁ u₂ v₁ v₂

/-- The combined closure uses the existing coherent shared-tensor model class. -/
theorem ReplayEqv.sound {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
    [CartesianMonoidalCategory V] [SymmetricCategory V]
    [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
    [HasFiniteCoproducts V] [HasFiniteCoproducts C]
    [DistributiveTensor V] [DistributivePremonoidalCategory C]
    [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] (M : TypeModel (Ty α) V) [InstructionModel J M Ψ]
    [RegionTypingCoherent (Φ := Ψ) J M]
    (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
      Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)
    {Γ : VCtx (Ty α)} {r s : Region Ψ}
    (h : ReplayEqv pe Γ r s K) (hr : Region.HasType Γ r K) (hs : Region.HasType Γ s K) :
    denoteRegion J M hr = denoteRegion J M hs :=
  replay_sound_proof J M shared h hr hs

end Packed

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture
