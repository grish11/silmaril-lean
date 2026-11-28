module

public import Silmaril.SSA.Isotope.LetCase.Structural.Finite.Defs
import Silmaril.Proofs.SSA.Isotope.LetCase.Structural.Finite.Extensional
import Silmaril.Proofs.SSA.Isotope.LetCase.Structural.Finite.Normalize
import Silmaril.Proofs.SSA.Isotope.LetCase.Structural.Finite.Reflection
import Silmaril.Proofs.SSA.Isotope.LetCase.Structural.Finite.Trace

/-! # Native LetCase reflection for inhabited finite structural interfaces

Primitive argument and reply types are built from unit, products and sums.
Generators are arbitrary and each denotes a typed effect. The completeness
statement uses the same coherent, central-unit, shared-tensor class as
`Reply.Valid`. The native relation is the existing unrepaired `Equiv false`.
-/

public section

namespace Silmaril.Isotope.LetCase.Structural.Finite

open LocallyNameless (Derivation Equiv HasType Tm)
open Reply (Γ₀ specialize)
open scoped Silmaril.Isotope.LetCase.Structural.Finite LetSeq.StraightLine.Structural

/-- Every interface type has finitely many constructor values. -/
theorem Shape.finite_constructors (s : Shape) : _root_.Finite (Constructor s.ty) :=
  s.finite_constructors_proof

variable {Φ : Type} [Signature Φ]

/-- Push a typed continuation through a head by native bind associativity,
using one recursive normal form for each constructor reply. -/
theorem bind_replay {A B : Types} {t : Term Φ 0} {k : Term Φ 1}
    (p : Head A t) (dk : HasType Φ Γ₀ (.snoc .nil A) k B)
    (cont : ∀ x : Constructor A, Normalizes B (Tm.instantiate k x.term)) :
    Normalizes B (.let₁ t k) :=
  bind_replay_proof p dk cont

/-- Every native exact typing at a constructor assignment replays to a
constructor return or one typed request with a smaller head for every reply. -/
theorem normalize {n : Nat} {β : Context n} {t : Term Φ n} {A : Types}
    (d : Derivation Φ Γ₀ β t A) (ρ : Assignment β) : Normalizes A (t.bsubst ρ.terms) :=
  normalize_proof d ρ

/-- Equality on all constructor instantiations of one slot suffices for
native equality under that binder, including for effectful bodies. -/
theorem constructor_ext (shape : Shape) {n : Nat} {β : Context n} {D : Types}
    {t u : Term Φ (n + 1)}
    (dt : HasType Φ Γ₀ (β.snoc shape.ty) t D) (du : HasType Φ Γ₀ (β.snoc shape.ty) u D)
    (h : ∀ v : Constructor shape.ty,
      Equiv false Γ₀ β (Tm.instantiate t v.term) (Tm.instantiate u v.term) D) :
    Equiv false Γ₀ (β.snoc shape.ty) t u D :=
  constructor_ext_type_proof shape.ty dt du h

/-- Precomposition by the left injection determines a body on
`X + 0`. The omitted right specialization is a native empty-slot equation. -/
theorem equiv_coprod_empty_iff {n : Nat} {β : Context n} {X D : Types} {t u : Term Φ (n + 1)}
    (dt : HasType Φ Γ₀ (β.snoc (.coprod X .empty)) t D)
    (du : HasType Φ Γ₀ (β.snoc (.coprod X .empty)) u D) :
    Equiv false Γ₀ (β.snoc (.coprod X .empty)) t u D ↔
      Equiv false Γ₀ (β.snoc X) (specialize t (.inl (.bv 0))) (specialize u (.inl (.bv 0))) D :=
  (Reply.equiv_iff_specializations dt du).trans
    ⟨And.left, fun h => ⟨h, empty_slot_proof
      (dt.bsubst (Fin.cases (.inr .bv) (fun _ => .bv))) (du.bsubst (Fin.cases (.inr .bv) (fun _ => .bv)))⟩⟩

/-- The ordered typed trace arrow separates inequivalent exact native terms
at an open inhabited structural input. -/
theorem equiv_iff_traceArrow_eq {n : Nat} {β : Context n} {t u : Term Φ n} {A : Types}
    (input : StructuralContext β) (d : Derivation Φ Γ₀ β t A) (e : Derivation Φ Γ₀ β u A) :
    Equiv false Γ₀ β t u A ↔ Reply.traceArrow d = Reply.traceArrow e :=
  ⟨fun h => Reply.traceArrow_of_valid (Reply.valid_of_equiv d e h),
    fun h => reflect_open_proof input d e ((Reply.traceArrow_eq_iff_run d e).mp h)⟩

/-- The latest slot may be any atom-free type. Empty summands and empty
products use native vacuity, so nested ordered sums retain their literal type. -/
theorem equiv_iff_traceArrow_eq_snoc {n : Nat} {β : Context n} {t u : Term Φ (n + 1)} {X D : Types}
    (input : StructuralContext β) (d : Derivation Φ Γ₀ (β.snoc X) t D)
    (e : Derivation Φ Γ₀ (β.snoc X) u D) :
    Equiv false Γ₀ (β.snoc X) t u D ↔ Reply.traceArrow d = Reply.traceArrow e :=
  ⟨fun h => Reply.traceArrow_of_valid (Reply.valid_of_equiv d e h),
    fun h => reflect_snoc_proof input d e ((Reply.traceArrow_eq_iff_run d e).mp h)⟩

/-- Native derivability coincides with validity in the existing compatible
Freyd class on the inhabited finite structural signature and input interface. -/
theorem equiv_iff_valid {n : Nat} {β : Context n} {t u : Term Φ n} {A : Types}
    (input : StructuralContext β) (d : Derivation Φ Γ₀ β t A) (e : Derivation Φ Γ₀ β u A) :
    Equiv false Γ₀ β t u A ↔ Reply.Valid d e :=
  ⟨Reply.valid_of_equiv d e, fun h => (equiv_iff_traceArrow_eq input d e).mpr (Reply.traceArrow_of_valid h)⟩

end Silmaril.Isotope.LetCase.Structural.Finite
