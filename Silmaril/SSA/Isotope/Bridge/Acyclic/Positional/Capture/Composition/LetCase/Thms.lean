module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Defs
public import Mathlib.CategoryTheory.Equivalence

/-! # The native captured LetCase category and its checked SSA equivalence

Homs are the native LetCase equation classes of `Case.Hom`, with the typed
input variable as identity and the typed let as composition. Every hom keeps
the same older context below its literal packed input. The laws are
transported along the emission and checked readback squares of the written
category, whose objects have nonempty ordered interfaces.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition

open CategoryTheory
open Region (packedExitType)
open LetCase.Structural.Finite (Context StructuralContext)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ] {d : Nat}
  {β : Context d} {I J K L : LCtx (Ty Empty)}

/-- Native sequencing at representatives is the literal typed let. -/
@[simp] theorem Case.seqClass_mk (p : Operand Φ (β.snoc (packedExitType I)) (packedExitType J))
    (q : Operand Φ (β.snoc (packedExitType J)) (packedExitType K)) :
    Case.seqClass (Quotient.mk _ p) (Quotient.mk _ q) = Quotient.mk _ (Case.seq p q) :=
  rfl

/-- Binding the input variable before a native class preserves the class. -/
theorem Case.identity_seq (input : StructuralContext β) (hI : I ≠ []) (hK : K ≠ [])
    (q : Case.Hom Φ β I K) : Case.seqClass Case.identity q = q := by
  rw [← emit_readback input hK q, ← emit_identity input hI, ← emit_comp, left_identity]

/-- Returning the bound result of a native class preserves the class. -/
theorem Case.seq_identity (input : StructuralContext β) (hJ : J ≠ [])
    (p : Case.Hom Φ β I J) : Case.seqClass p Case.identity = p := by
  rw [← emit_readback input hJ p, ← emit_identity input hJ, ← emit_comp, right_identity]

/-- Native let is associative on the equation classes. -/
theorem Case.seq_assoc (input : StructuralContext β) (hJ : J ≠ []) (hK : K ≠ []) (hL : L ≠ [])
    (p : Case.Hom Φ β I J) (q : Case.Hom Φ β J K) (r : Case.Hom Φ β K L) :
    Case.seqClass (Case.seqClass p q) r = Case.seqClass p (Case.seqClass q r) := by
  rw [← emit_readback input hJ p, ← emit_readback input hK q, ← emit_readback input hL r]
  simp only [← emit_comp, associative]

/-- The native captured category. Its homs are exactly the native LetCase
equation classes at the literal packed input and output types. -/
instance Case.category (input : StructuralContext β) : Category (Case.Interface Φ β input) where
  Hom X Y := Case.Hom Φ β X.exits Y.exits
  id _ := Case.identity
  comp p q := Case.seqClass p q
  id_comp {X Y} q := Case.identity_seq input X.nonempty Y.nonempty q
  comp_id {_ Y} p := Case.seq_identity input Y.nonempty p
  assoc {_ X Y Z} p q r := Case.seq_assoc input X.nonempty Y.nonempty Z.nonempty p q r

/-- The actual ranked SSA emitter, from written checked graphs to native
LetCase classes. It keeps each ordered interface. -/
def emitFunctor (input : StructuralContext β) : Interface Φ β input ⥤ Case.Interface Φ β input where
  obj X := ⟨X.exits, X.nonempty⟩
  map p := emitClass input p
  map_id X := emit_identity input X.nonempty
  map_comp p q := emit_comp input p q

/-- Checked readback of every typed representative, from native LetCase
classes to written checked graphs. -/
def readbackFunctor (input : StructuralContext β) :
    Case.Interface Φ β input ⥤ Interface Φ β input where
  obj X := ⟨X.exits, X.nonempty⟩
  map {_ Y} p := Case.readbackClass Y.nonempty p
  map_id X := readback_identity input X.nonempty
  map_comp {_ Y Z} p q := readback_comp input Y.nonempty Z.nonempty p q

@[simp] theorem readbackFunctor_map_emitFunctor_map (input : StructuralContext β)
    {X Y : Interface Φ β input} (p : X ⟶ Y) :
    (readbackFunctor input).map ((emitFunctor input).map p) = p :=
  readback_emit input Y.nonempty p

@[simp] theorem emitFunctor_map_readbackFunctor_map (input : StructuralContext β)
    {X Y : Case.Interface Φ β input} (p : X ⟶ Y) :
    (emitFunctor input).map ((readbackFunctor input).map p) = p :=
  emit_readback input Y.nonempty p

/-- Emission followed by checked readback is the identity functor on the
written category. -/
theorem emitFunctor_comp_readbackFunctor (input : StructuralContext β) :
    emitFunctor input ⋙ readbackFunctor input = 𝟭 (Interface Φ β input) :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun X Y p => by
    change Case.readbackClass Y.nonempty (emitClass input p) = 𝟙 X ≫ p ≫ 𝟙 Y
    rw [Category.comp_id, Category.id_comp, readback_emit]

/-- Checked readback followed by emission is the identity functor on the
native category. -/
theorem readbackFunctor_comp_emitFunctor (input : StructuralContext β) :
    readbackFunctor input ⋙ emitFunctor input = 𝟭 (Case.Interface Φ β input) :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun X Y p => by
    change emitClass input (Case.readbackClass Y.nonempty p) = 𝟙 X ≫ p ≫ 𝟙 Y
    rw [Category.comp_id, Category.id_comp, emit_readback]

/-- The written and native captured categories are equivalent. The unit
and counit are identities at every interface. -/
def categoryEquivalence (input : StructuralContext β) :
    Interface Φ β input ≌ Case.Interface Φ β input where
  functor := emitFunctor input
  inverse := readbackFunctor input
  unitIso := eqToIso (emitFunctor_comp_readbackFunctor input).symm
  counitIso := eqToIso (readbackFunctor_comp_emitFunctor input)
  functor_unitIso_comp X := by
    simp only [eqToIso.hom, eqToHom_app, eqToHom_map, eqToHom_trans, eqToHom_refl]

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition
