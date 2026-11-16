module

public import Silmaril.Logic.Algebraic.Initial.Matching.FiniteSorted.Thms

set_option backward.isDefEq.respectTransparency false

/-! Literal ambient postcomposition. Original coordinates, operation order,
equations and signed ground witnesses never change. Heterogeneous intermediate
equalities expose the mapped empty/append contexts; final sentences and sets
are equal as syntax. No transport between different original theories is used. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler
open CategoryTheory Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Matching
open Initial.Presented Initial.Presented.Characterization
open FixedPoint.Simultaneous

variable {D : Profile} {B C : EQ.Signature}

theorem coordinate_map (σ : D.signature ⟶ B) (f : B ⟶ C) :
    (SignedSpectrum.nativeMap f).sorts ∘ coordinate σ = coordinate (σ ≫ f) := rfl

theorem emptyContext_map (f : B ⟶ C) :
    (SignedSpectrum.nativeMap f).sorts ∘ emptyContext (B := B) = emptyContext (B := C) :=
  funext (fun i => i.elim0)

theorem bodyContext_map (σ : D.signature ⟶ B) (f : B ⟶ C) :
    (SignedSpectrum.nativeMap f).sorts ∘ append (coordinate σ) (emptyContext (B := B)) =
      append (coordinate (σ ≫ f)) (emptyContext (B := C)) :=
  (map_append (SignedSpectrum.nativeMap f) _ _).trans
    (congrArg (append (coordinate (σ ≫ f))) (emptyContext_map f))

private theorem cast_heq {α : Sort _} {F : α → Sort _} {a b : α}
    (h : a = b) (x : F a) : HEq (h ▸ x : F b) x := by
  cases h
  rfl

private theorem map_sort_cast_heq {A E : SortMaps.Signature} (f : A ⟶ E)
    {r k : Nat} {P : Fin r → A.sorts} {Γ : Fin k → A.sorts} {s t : A.sorts}
    (h : s = t) (p : FixedPoint.Pattern A.symbols P Γ s) :
    HEq (SortMaps.Hom.fixedPattern f (h ▸ p : FixedPoint.Pattern A.symbols P Γ t))
      (SortMaps.Hom.fixedPattern f p) := by
  cases h
  rfl

private theorem setvar_heq {A : SortMaps.Signature} {r k : Nat}
    {P Q : Fin r → A.sorts} {Γ Δ : Fin k → A.sorts}
    (hP : P = Q) (hΓ : Γ = Δ) (i : Fin r) :
    HEq (.setvar i : FixedPoint.Pattern A.symbols P Γ (P i))
      (.setvar i : FixedPoint.Pattern A.symbols Q Δ (Q i)) := by
  cases hP
  cases hΓ
  rfl

private theorem app_heq {A : SortMaps.Signature} {r k n : Nat}
    {P Q : Fin r → A.sorts} {Γ Δ : Fin k → A.sorts}
    {inputs : Fin n → A.sorts} {output : A.sorts}
    (hP : P = Q) (hΓ : Γ = Δ) (op : A.symbols.operations n inputs output)
    (a : ∀ j, FixedPoint.Pattern A.symbols P Γ (inputs j))
    (b : ∀ j, FixedPoint.Pattern A.symbols Q Δ (inputs j))
    (h : ∀ j, HEq (a j) (b j)) :
    HEq (FixedPoint.Pattern.app op a) (FixedPoint.Pattern.app op b) := by
  cases hP
  cases hΓ
  exact heq_of_eq (congrArg (FixedPoint.Pattern.app op) (funext (fun j => eq_of_heq (h j))))

private theorem disj_heq {A : SortMaps.Signature} {r k : Nat}
    {P Q : Fin r → A.sorts} {Γ Δ : Fin k → A.sorts} {s : A.sorts}
    (hP : P = Q) (hΓ : Γ = Δ)
    (p q : FixedPoint.Pattern A.symbols P Γ s) (p' q' : FixedPoint.Pattern A.symbols Q Δ s)
    (hp : HEq p p') (hq : HEq q q') : HEq (FixedPoint.Pattern.disj p q) (FixedPoint.Pattern.disj p' q') := by
  cases hP
  cases hΓ
  cases hp
  cases hq
  rfl

private theorem base_heq {A : SortMaps.Signature} {r k : Nat}
    {P Q : Fin r → A.sorts} {Γ Δ : Fin k → A.sorts} {s : A.sorts}
    (hP : P = Q) (hΓ : Γ = Δ)
    (p : FirstOrder.Pattern A.symbols Γ s) (q : FirstOrder.Pattern A.symbols Δ s)
    (hp : HEq p q) :
    HEq (FixedPoint.Pattern.base (P := P) p) (FixedPoint.Pattern.base (P := Q) q) := by
  cases hP
  cases hΓ
  cases hp
  rfl

private theorem fo_var_heq {A : SortMaps.Signature} {k : Nat}
    {Γ Δ : Fin k → A.sorts} (hΓ : Γ = Δ) (i : Fin k) :
    HEq (.var i : FirstOrder.Pattern A.symbols Γ (Γ i))
      (.var i : FirstOrder.Pattern A.symbols Δ (Δ i)) := by
  cases hΓ
  rfl

private theorem fo_neg_heq {A : SortMaps.Signature} {k : Nat}
    {Γ Δ : Fin k → A.sorts} {s : A.sorts} (hΓ : Γ = Δ)
    (p : FirstOrder.Pattern A.symbols Γ s) (q : FirstOrder.Pattern A.symbols Δ s)
    (h : HEq p q) : HEq (FirstOrder.Pattern.neg p) (FirstOrder.Pattern.neg q) := by
  cases hΓ
  cases h
  rfl

private theorem fo_conj_heq {A : SortMaps.Signature} {k : Nat}
    {Γ Δ : Fin k → A.sorts} {s : A.sorts} (hΓ : Γ = Δ)
    (p q : FirstOrder.Pattern A.symbols Γ s) (p' q' : FirstOrder.Pattern A.symbols Δ s)
    (hp : HEq p p') (hq : HEq q q') : HEq (FirstOrder.Pattern.conj p q) (FirstOrder.Pattern.conj p' q') := by
  cases hΓ
  cases hp
  cases hq
  rfl

private theorem fo_ex_heq {A : SortMaps.Signature} {k : Nat}
    {Γ Δ : Fin k → A.sorts} {s : A.sorts} (hΓ : Γ = Δ) (bound : A.sorts)
    (p : FirstOrder.Pattern A.symbols (Fin.cases bound Γ) s)
    (q : FirstOrder.Pattern A.symbols (Fin.cases bound Δ) s)
    (h : HEq p q) : HEq (FirstOrder.Pattern.ex bound p) (FirstOrder.Pattern.ex bound q) := by
  cases hΓ
  cases h
  rfl

private theorem fo_app_heq {A : SortMaps.Signature} {k n : Nat}
    {Γ Δ : Fin k → A.sorts} {inputs : Fin n → A.sorts} {output : A.sorts}
    (hΓ : Γ = Δ) (op : A.symbols.operations n inputs output)
    (a : ∀ j, FirstOrder.Pattern A.symbols Γ (inputs j))
    (b : ∀ j, FirstOrder.Pattern A.symbols Δ (inputs j))
    (h : ∀ j, HEq (a j) (b j)) :
    HEq (FirstOrder.Pattern.app op a) (FirstOrder.Pattern.app op b) := by
  cases hΓ
  exact heq_of_eq (congrArg (FirstOrder.Pattern.app op) (funext (fun j => eq_of_heq (h j))))

theorem recursionVariable_map (σ : D.signature ⟶ B) (f : B ⟶ C) (i : Fin D.sortCount) :
    HEq (SortMaps.Hom.fixedPattern (SignedSpectrum.nativeMap f) (recursionVariable σ i))
      (recursionVariable (σ ≫ f) i) := by
  unfold recursionVariable
  apply (map_sort_cast_heq (SignedSpectrum.nativeMap f) _ _).trans
  apply (setvar_heq (bodyContext_map σ f) (emptyContext_map f) (Fin.castAdd 0 i)).trans
  exact (cast_heq _ _).symm

theorem constructorPattern_map (σ : D.signature ⟶ B) (f : B ⟶ C)
    (c : Fin D.operationCount) :
    HEq (SortMaps.Hom.fixedPattern (SignedSpectrum.nativeMap f) (constructorPattern σ c))
      (constructorPattern (σ ≫ f) c) := by
  apply app_heq (bodyContext_map σ f) (emptyContext_map f)
  intro j
  exact recursionVariable_map σ f (D.input c j)

private theorem empty_ex_map (σ : D.signature ⟶ B) (f : B ⟶ C) (i : Fin D.sortCount) :
    HEq (SortMaps.Hom.pattern (SignedSpectrum.nativeMap f)
      (.ex (coordinate σ i) (.var 0) : FirstOrder.Pattern (SignedSpectrum.nativeSignature B).symbols
        (emptyContext (B := B)) (coordinate σ i)))
      (.ex (coordinate (σ ≫ f) i) (.var 0) : FirstOrder.Pattern (SignedSpectrum.nativeSignature C).symbols
        (emptyContext (B := C)) (coordinate (σ ≫ f) i)) := by
  apply fo_ex_heq (emptyContext_map f)
  apply (cast_heq (F := fun Γ => FirstOrder.Pattern
    (SignedSpectrum.nativeSignature C).symbols Γ (coordinate (σ ≫ f) i)) _ _).trans
  refine fo_var_heq ?_ 0
  funext j
  exact Fin.cases rfl (fun j => j.elim0) j

theorem bottom_map (σ : D.signature ⟶ B) (f : B ⟶ C) (i : Fin D.sortCount) :
    HEq (SortMaps.Hom.fixedPattern (SignedSpectrum.nativeMap f) (bottom σ i))
      (bottom (σ ≫ f) i) := by
  apply base_heq (bodyContext_map σ f) (emptyContext_map f)
  apply fo_conj_heq (emptyContext_map f)
  · exact empty_ex_map σ f i
  · exact fo_neg_heq (emptyContext_map f) _ _ (empty_ex_map σ f i)

/-- The list order is retained literally; no ambient-image deduplication occurs. -/
theorem disjunction_map (σ : D.signature ⟶ B) (f : B ⟶ C) (i : Fin D.sortCount)
    {J : Type} (js : List J) (p : J → BodyPat σ i) (q : J → BodyPat (σ ≫ f) i)
    (h : ∀ j, HEq (SortMaps.Hom.fixedPattern (SignedSpectrum.nativeMap f) (p j)) (q j)) :
    HEq (SortMaps.Hom.fixedPattern (SignedSpectrum.nativeMap f) (disjunction σ i (js.map p)))
      (disjunction (σ ≫ f) i (js.map q)) := by
  induction js with
  | nil => exact bottom_map σ f i
  | cons j js ih =>
      exact disj_heq (bodyContext_map σ f) (emptyContext_map f) _ _ _ _ (h j) ih

theorem body_map (σ : D.signature ⟶ B) (f : B ⟶ C) (i : Fin D.sortCount) :
    HEq (SortMaps.Hom.fixedPattern (SignedSpectrum.nativeMap f) (body σ i))
      (body (σ ≫ f) i) := by
  unfold body
  apply disjunction_map
  intro c
  rcases c with ⟨c, hc⟩
  cases hc
  exact constructorPattern_map σ f c

private theorem system_heq {A : SortMaps.Signature} {r l k : Nat}
    {P P' : Fin r → A.sorts} {Q Q' : Fin l → A.sorts} {Γ Γ' : Fin k → A.sorts}
    (hP : P = P') (hQ : Q = Q') (hΓ : Γ = Γ')
    (s : System A.symbols P Q Γ) (t : System A.symbols P' Q' Γ')
    (h : ∀ i, HEq (s.body i) (t.body i)) : HEq s t := by
  cases hP
  cases hQ
  cases hΓ
  apply heq_of_eq
  cases s with
  | mk sb =>
    cases t with
    | mk tb =>
      have hb : sb = tb := funext (fun i => eq_of_heq (h i))
      cases hb
      rfl

theorem system_map (σ : D.signature ⟶ B) (f : B ⟶ C) :
    HEq ((system σ).map (SignedSpectrum.nativeMap f)) (system (σ ≫ f)) := by
  apply system_heq (coordinate_map σ f) (emptyContext_map f) (emptyContext_map f)
  intro i
  change HEq ((map_append (SignedSpectrum.nativeMap f) (coordinate σ)
    (emptyContext (B := B))) ▸
      SortMaps.Hom.fixedPattern (SignedSpectrum.nativeMap f) (body σ i))
    (body (σ ≫ f) i)
  exact (cast_heq (F := fun P => FixedPoint.Pattern
    (SignedSpectrum.nativeSignature C).symbols P
      ((SignedSpectrum.nativeMap f).sorts ∘ emptyContext (B := B))
      (coordinate (σ ≫ f) i)) _ _).trans (body_map σ f i)

private theorem compile_heq {A : SortMaps.Signature} {r l k : Nat}
    {P P' : Fin r → A.sorts} {Q Q' : Fin l → A.sorts} {Γ Γ' : Fin k → A.sorts}
    (hP : P = P') (hQ : Q = Q') (hΓ : Γ = Γ')
    (s : System A.symbols P Q Γ) (t : System A.symbols P' Q' Γ')
    (hs : HEq s t) (i : Fin r) : HEq (s.compile i) (t.compile i) := by
  cases hP
  cases hQ
  cases hΓ
  cases hs
  rfl

/-- This uses literal dependent Bekič compile_map, not semantic denotation. -/
theorem generated_map (σ : D.signature ⟶ B) (f : B ⟶ C) (i : Fin D.sortCount) :
    HEq (SortMaps.Hom.fixedPattern (SignedSpectrum.nativeMap f) (generated σ i))
      (generated (σ ≫ f) i) :=
  (heq_of_eq (System.compile_map (SignedSpectrum.nativeMap f) (system σ) i)).trans
    (compile_heq (coordinate_map σ f) (emptyContext_map f) (emptyContext_map f)
      _ _ (system_map σ f) i)

private theorem sentence_mk_eq {A : SortMaps.Signature} {r k : Nat}
    {P Q : Fin r → A.sorts} {Γ Δ : Fin k → A.sorts} {s t : A.sorts}
    (hP : P = Q) (hΓ : Γ = Δ) (hs : s = t)
    (p : FixedPoint.Pattern A.symbols P Γ s) (q : FixedPoint.Pattern A.symbols Q Δ t)
    (hp : HEq p q) :
    FixedPoint.Sentence.mk r k P Γ s p = FixedPoint.Sentence.mk r k Q Δ t q := by
  cases hP
  cases hΓ
  cases hs
  cases hp
  rfl

theorem generationClause_map (σ : D.signature ⟶ B) (f : B ⟶ C) (i : Fin D.sortCount) :
    SortMaps.Hom.fixedSentence (SignedSpectrum.nativeMap f) (generationClause σ i) =
      generationClause (σ ≫ f) i := by
  apply sentence_mk_eq (emptyContext_map f) (emptyContext_map f) rfl
  apply disj_heq (emptyContext_map f) (emptyContext_map f)
  · apply base_heq (emptyContext_map f) (emptyContext_map f)
    apply fo_neg_heq (emptyContext_map f)
    apply fo_app_heq (emptyContext_map f)
    intro j
    exact j.elim0
  · exact generated_map σ f i

/-- Existing signed-spectrum transport retains the same original ground terms
and Rel/not-Rel witnesses under arbitrary ambient sort and operation collisions. -/
theorem encoded_spectrum_map (T : Initial.Theory) {B C : EQ.Signature}
    (σ : T.sig ⟶ B) (f : B ⟶ C) :
    SortMaps.Hom.fixedSentence (SignedSpectrum.nativeMap f) ''
        (FixedPoint.encodeFirstOrder '' SignedSpectrum.spectrum T σ) =
      FixedPoint.encodeFirstOrder '' SignedSpectrum.spectrum T (σ ≫ f) := by
  rw [SignedSpectrum.spectrum_map, Set.image_image, Set.image_image]
  apply congrArg (fun g => g '' SignedSpectrum.spectrum T σ)
  funext p
  exact SortMaps.Hom.encodeFirstOrder_map (SignedSpectrum.nativeMap f) p

/-- Equality of the COMPLETE compiled native sentence set, with no changes to
original equations, constructor order or recursion coordinates. -/
theorem compiled_map (E : Set (Equations D)) (σ : D.signature ⟶ B) (f : B ⟶ C) :
    SortMaps.Hom.fixedSentence (SignedSpectrum.nativeMap f) '' compiled E σ =
      compiled E (σ ≫ f) := by
  have hr : SortMaps.Hom.fixedSentence (SignedSpectrum.nativeMap f) ''
      Set.range (generationClause σ) = Set.range (generationClause (σ ≫ f)) := by
    ext p
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (generationClause_map σ f i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨generationClause σ i, ⟨i, rfl⟩, generationClause_map σ f i⟩
  unfold compiled
  rw [Set.image_union, encoded_spectrum_map, hr]

end Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler
