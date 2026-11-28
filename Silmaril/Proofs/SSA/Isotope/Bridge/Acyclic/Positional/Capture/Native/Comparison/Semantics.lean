module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Native.Comparison.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Categorical.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Substitution.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Model.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Native.Thms
public import Silmaril.SSA.Isotope.LetCase.Structural.Finite.Thms

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture

open CategoryTheory CategoryTheory.Limits
open LambdaSSA.Semantics.Categorical
open SingletonDispatcher (labelInject_payload)
open LetIter.Semantics.Categorical (TypeModel InstructionModel)
open scoped MonoidalCategory

universe u v x y h k

section Model

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type x} {C : Type y} [Category.{h} V] [Category.{k} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] (M : TypeModel τ V) [InstructionModel J M Φ]
  [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
    Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)
  {d n m : Nat} {β : BoundCtx τ d} {L : LCtx τ}
  (p : Table Φ β L n) (q : Table Φ β L m) (hp : p.check = true) (hq : q.check = true)
  (i : Fin (n + 1)) (j : Fin (m + 1)) (a : Operand Φ β (p.types i)) (b : Operand Φ β (q.types j))

include shared

theorem packed_denote_proof :
    denoteRegion J M (p.packedSSA_hasType i a) =
      J.map (contextMap M β) ≫ LetCase.Semantics.Categorical.denote J M (p.toLetCase hp i a).2 ≫
        J.map (labelInject M (L := [Region.packedExitType L]) 0 rfl) := by
  let hu := FreydCategory.CentralUnit.unit_central (J := J)
  let entry := p.toSSA_hasType i a
  change denoteRegion J M entry.bindBranchArguments.hasType.packExits = _
  rw [denoteRegion_packExits_valueBranches J M shared entry.bindBranchArguments, ← Region.denoteRegion_bindBranchArguments J M hu entry,
    p.toLetCase_denote J M hp i a]
  simp only [Category.assoc, ← J.map_comp, unpackLabelExit_packLabelExit, Category.comp_id]

theorem packed_denote_iff_proof :
    denoteRegion J M (p.packedSSA_hasType i a) = denoteRegion J M (q.packedSSA_hasType j b) ↔
      LetCase.Semantics.Categorical.denote J M (p.toLetCase hp i a).2 =
        LetCase.Semantics.Categorical.denote J M (q.toLetCase hq j b).2 := by
  rw [packed_denote_proof J M shared p hp i a, packed_denote_proof J M shared q hq j b]
  have := contextMap_isIso M β
  constructor
  · intro eq
    have out := congrArg (fun f => f ≫ J.map (singletonLabelPayload M (Region.packedExitType L))) eq
    simp only [Category.assoc, ← J.map_comp, labelInject_payload, J.map_id, Category.comp_id] at out
    exact (cancel_epi (J.map (contextMap M β))).mp out
  · intro eq
    rw [eq]

end Model

section Trace

open LetCase.Structural.Finite (StructuralContext Context Types)
open LetCase.Structural.Reply (Γ₀ traceArrow)
open LetCase.LocallyNameless (Equiv)
open LetSeq.StraightLine.Structural.Categorical (traceJ traceTypes traceInstructions)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ] {d n m : Nat} {β : Context d} {L : List Types}
  (p : Table Φ β L n) (q : Table Φ β L m) (hp : p.check = true) (hq : q.check = true)
  (i : Fin (n + 1)) (j : Fin (m + 1)) (a : Operand Φ β (p.types i)) (b : Operand Φ β (q.types j))

theorem packed_trace_iff_proof (input : StructuralContext β) :
    (let := traceInstructions (α := Empty) (Φ := Φ)
     denoteRegion (traceJ (α := Empty) (Φ := Φ)) (traceTypes Empty) (p.packedSSA_hasType i a) =
       denoteRegion (traceJ (α := Empty) (Φ := Φ)) (traceTypes Empty) (q.packedSSA_hasType j b)) ↔
      Equiv false Γ₀ β (p.toLetCase hp i a).1 (q.toLetCase hq j b).1 (Region.packedExitType L) := by
  let := traceInstructions (α := Empty) (Φ := Φ)
  let := Native.trace_region_coherent (Φ := Φ)
  let J := traceJ (α := Empty) (Φ := Φ)
  let M := traceTypes Empty
  let left := p.toLetCase hp i a
  let right := q.toLetCase hq j b
  have comparison := packed_denote_iff_proof J M (fun _ _ => ⟨rfl, rfl⟩) p q hp hq i j a b
  have finite := LetCase.Structural.Finite.equiv_iff_traceArrow_eq input left.2 right.2
  unfold traceArrow LetIter.Semantics.Categorical.denoteOfType at finite
  rw [Native.denote_caseIter J M, Native.denote_caseIter J M] at finite
  exact comparison.trans finite.symm

theorem packed_replay_implies_equiv_proof (input : StructuralContext β)
    (h : ReplayEqv false β.toList (p.packedSSA i a) (q.packedSSA j b) [Region.packedExitType L]) :
    Equiv false Γ₀ β (p.toLetCase hp i a).1 (q.toLetCase hq j b).1 (Region.packedExitType L) := by
  let := traceInstructions (α := Empty) (Φ := Φ)
  let := Native.trace_region_coherent (Φ := Φ)
  exact (packed_trace_iff_proof p q hp hq i j a b input).mp
    (ReplayEqv.sound (traceJ (α := Empty) (Φ := Φ)) (traceTypes Empty) (fun _ _ => ⟨rfl, rfl⟩)
      h (p.packedSSA_hasType i a) (q.packedSSA_hasType j b))

end Trace

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture
