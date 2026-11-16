module

public import Silmaril.Logic.Matching.SortMaps.Defs

@[expose] public section
namespace Silmaril.Logic.Matching.SortMaps
open CategoryTheory
namespace Hom
variable {A B C : Signature}

private theorem denote_cast {S : Type} {A : SortedSignature S} (M : FirstOrder.Model A)
    {k : Nat} {Γ Δ : Fin k → S} {s : S} (h : Γ = Δ)
    (p : FirstOrder.Pattern A Γ s) (v : ∀ i, M.carrier (Δ i)) :
    M.denote v (h ▸ p) = M.denote (h.symm ▸ v) p := by
  cases h
  rfl

private theorem context_cast_apply {S : Type} {A : SortedSignature S}
    (M : FirstOrder.Model A) {k : Nat} {Γ Δ : Fin k → S}
    (h : Γ = Δ) (v : ∀ i, M.carrier (Γ i)) (i : Fin k) :
    HEq ((h ▸ v : ∀ i, M.carrier (Δ i)) i) (v i) := by
  cases h
  rfl

private theorem env_cons (f : Hom A B) (M : FirstOrder.Model B.symbols)
    {k : Nat} {Γ : Fin k → A.sorts} (bound : A.sorts)
    (v : ∀ i, M.carrier (f.sorts (Γ i))) (x : M.carrier (f.sorts bound)) :
    Eq.rec (motive := fun Δ _ => ∀ i, M.carrier (Δ i))
      (Fin.cases x v) (map_cons f bound Γ).symm =
      (show (∀ i, (reduct f M).carrier (Fin.cases bound Γ i)) from Fin.cases x v) := by
  funext i
  cases i using Fin.cases with
  | zero => exact eq_of_heq (context_cast_apply M (map_cons f bound Γ).symm (Fin.cases x v) _)
  | succ i => exact eq_of_heq (context_cast_apply M (map_cons f bound Γ).symm (Fin.cases x v) _)

theorem denote_pattern (f : Hom A B) (M : FirstOrder.Model B.symbols)
    {k : Nat} {Γ : Fin k → A.sorts} {s : A.sorts}
    (p : FirstOrder.Pattern A.symbols Γ s) :
    ∀ v, M.denote v (pattern f p) = (reduct f M).denote v p := by
  induction p with
  | var => intro v; rfl
  | app op args ih => intro v; simp only [pattern, FirstOrder.Model.denote, ih]; rfl
  | neg p ih => intro v; exact congrArg (fun X => Xᶜ) (ih v)
  | conj p q hp hq => intro v; exact congrArg₂ Set.inter (hp v) (hq v)
  | ex bound body ih =>
      intro v
      simp only [pattern, FirstOrder.Model.denote, denote_cast, ih]
      congr 1
      funext result
      congr 1
      funext value
      exact congrArg (fun env => result ∈ (reduct f M).denote env body) (env_cons f M bound v value)

theorem satisfaction (f : Hom A B) (M : FirstOrder.Model B.symbols)
    (p : FirstOrder.Sentence A.symbols) :
    FirstOrder.Sentence.Satisfies M (sentence f p) ↔
      FirstOrder.Sentence.Satisfies (reduct f M) p := by
  simp only [FirstOrder.Sentence.Satisfies, sentence, denote_pattern]
  rfl
end Hom
end Silmaril.Logic.Matching.SortMaps

@[expose] public section
namespace Silmaril.Logic.Matching.SortMaps
open CategoryTheory
namespace Hom
variable {A B C : Signature}

@[simp] theorem reduct_id (M : FirstOrder.Model A.symbols) : reduct (𝟙 A) M = M := by
  cases M
  rfl
@[simp] theorem reduct_comp (f : A ⟶ B) (g : B ⟶ C) (M : FirstOrder.Model C.symbols) :
    reduct (f ≫ g) M = reduct f (reduct g M) := rfl

private theorem pattern_transport_heq {S : Type} {A : SortedSignature S} {k : Nat}
    {Γ Δ : Fin k → S} {s : S} (h : Γ = Δ) (p : FirstOrder.Pattern A Γ s) :
    HEq (h ▸ p : FirstOrder.Pattern A Δ s) p := by
  cases h
  rfl

private theorem fixed_transport_heq {S : Type} {A : SortedSignature S} {r k : Nat}
    {P : Fin r → S} {Γ Δ : Fin k → S} {s : S} (h : Γ = Δ)
    (p : FixedPoint.Pattern A P Γ s) : HEq (h ▸ p : FixedPoint.Pattern A P Δ s) p := by
  cases h
  rfl

private theorem pattern_cast (f : A ⟶ B) {k : Nat} {Γ Δ : Fin k → A.sorts}
    {s : A.sorts} (h : Γ = Δ) (p : FirstOrder.Pattern A.symbols Γ s) :
    pattern f (h ▸ p) = congrArg (f.sorts ∘ ·) h ▸ pattern f p := by
  cases h
  rfl

@[simp] theorem pattern_id {k : Nat} {Γ : Fin k → A.sorts} {s : A.sorts}
    (p : FirstOrder.Pattern A.symbols Γ s) : pattern (𝟙 A) p = p := by
  induction p with
  | var => rfl
  | app op args ih => exact congrArg (FirstOrder.Pattern.app op) (funext ih)
  | neg p ih => exact congrArg FirstOrder.Pattern.neg ih
  | conj p q hp hq => exact congrArg₂ FirstOrder.Pattern.conj hp hq
  | ex bound body ih =>
      change FirstOrder.Pattern.ex bound (pattern (𝟙 A) body) = .ex bound body
      exact congrArg (FirstOrder.Pattern.ex bound) ih

@[simp] theorem pattern_comp (f : A ⟶ B) (g : B ⟶ C)
    {k : Nat} {Γ : Fin k → A.sorts} {s : A.sorts}
    (p : FirstOrder.Pattern A.symbols Γ s) :
    pattern (f ≫ g) p = pattern g (pattern f p) := by
  induction p with
  | var => rfl
  | app op args ih => exact congrArg (FirstOrder.Pattern.app (g.operations (f.operations op))) (funext ih)
  | neg p ih => exact congrArg FirstOrder.Pattern.neg ih
  | conj p q hp hq => exact congrArg₂ FirstOrder.Pattern.conj hp hq
  | ex bound body ih =>
      simp only [pattern, pattern_cast]
      congr 1
      apply eq_of_heq
      exact (pattern_transport_heq (map_cons (f ≫ g) bound _) _).trans
        ((heq_of_eq ih).trans
          ((pattern_transport_heq (map_cons g (f.sorts bound) _) _).trans
            (pattern_transport_heq (congrArg (g.sorts ∘ ·) (map_cons f bound _)) _)).symm)
end Hom
end Silmaril.Logic.Matching.SortMaps

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.SortMaps.Hom
open CategoryTheory
variable {A B C : Signature}

private theorem fixedPattern_cast (f : A ⟶ B) {r k : Nat} {P : Fin r → A.sorts}
    {Γ Δ : Fin k → A.sorts} {s : A.sorts} (h : Γ = Δ)
    (p : FixedPoint.Pattern A.symbols P Γ s) :
    fixedPattern f (h ▸ p) = congrArg (f.sorts ∘ ·) h ▸ fixedPattern f p := by
  cases h
  rfl

@[simp] theorem fixedPattern_id {r k : Nat} {P : Fin r → A.sorts} {Γ : Fin k → A.sorts}
    {s : A.sorts} (p : FixedPoint.Pattern A.symbols P Γ s) : fixedPattern (𝟙 A) p = p := by
  induction p with
  | base p => exact congrArg FixedPoint.Pattern.base (pattern_id p)
  | setvar => rfl
  | app op args ih => exact congrArg (FixedPoint.Pattern.app op) (funext ih)
  | dualApp op args ih => exact congrArg (FixedPoint.Pattern.dualApp op) (funext ih)
  | conj p q hp hq => exact congrArg₂ FixedPoint.Pattern.conj hp hq
  | disj p q hp hq => exact congrArg₂ FixedPoint.Pattern.disj hp hq
  | ex bound p hp =>
      change FixedPoint.Pattern.ex bound (fixedPattern (𝟙 A) p) = .ex bound p
      exact congrArg (FixedPoint.Pattern.ex bound) hp
  | all bound p hp =>
      change FixedPoint.Pattern.all bound (fixedPattern (𝟙 A) p) = .all bound p
      exact congrArg (FixedPoint.Pattern.all bound) hp
  | mu p hp => exact congrArg FixedPoint.Pattern.mu hp
  | nu p hp => exact congrArg FixedPoint.Pattern.nu hp

@[simp] theorem fixedPattern_comp (f : A ⟶ B) (g : B ⟶ C)
    {r k : Nat} {P : Fin r → A.sorts} {Γ : Fin k → A.sorts} {s : A.sorts}
    (p : FixedPoint.Pattern A.symbols P Γ s) :
    fixedPattern (f ≫ g) p = fixedPattern g (fixedPattern f p) := by
  induction p with
  | base p => exact congrArg FixedPoint.Pattern.base (pattern_comp f g p)
  | setvar => rfl
  | app op args ih => exact congrArg (FixedPoint.Pattern.app _) (funext ih)
  | dualApp op args ih => exact congrArg (FixedPoint.Pattern.dualApp _) (funext ih)
  | conj p q hp hq => exact congrArg₂ FixedPoint.Pattern.conj hp hq
  | disj p q hp hq => exact congrArg₂ FixedPoint.Pattern.disj hp hq
  | @ex r k P Γ s bound p hp =>
      change FixedPoint.Pattern.ex ((f ≫ g).sorts bound)
        ((map_cons (f ≫ g) bound Γ) ▸ fixedPattern (f ≫ g) p) =
        FixedPoint.Pattern.ex (g.sorts (f.sorts bound))
          ((map_cons g (f.sorts bound) (f.sorts ∘ Γ)) ▸
            fixedPattern g ((map_cons f bound Γ) ▸ fixedPattern f p))
      rw [fixedPattern_cast]
      congr 1
      apply eq_of_heq
      exact (fixed_transport_heq (map_cons (f ≫ g) bound _) _).trans
        ((heq_of_eq hp).trans
          ((fixed_transport_heq (map_cons g (f.sorts bound) _) _).trans
            (fixed_transport_heq (congrArg (g.sorts ∘ ·) (map_cons f bound _)) _)).symm)
  | @all r k P Γ s bound p hp =>
      change FixedPoint.Pattern.all ((f ≫ g).sorts bound)
        ((map_cons (f ≫ g) bound Γ) ▸ fixedPattern (f ≫ g) p) =
        FixedPoint.Pattern.all (g.sorts (f.sorts bound))
          ((map_cons g (f.sorts bound) (f.sorts ∘ Γ)) ▸
            fixedPattern g ((map_cons f bound Γ) ▸ fixedPattern f p))
      rw [fixedPattern_cast]
      congr 1
      apply eq_of_heq
      exact (fixed_transport_heq (map_cons (f ≫ g) bound _) _).trans
        ((heq_of_eq hp).trans
          ((fixed_transport_heq (map_cons g (f.sorts bound) _) _).trans
            (fixed_transport_heq (congrArg (g.sorts ∘ ·) (map_cons f bound _)) _)).symm)
  | mu p hp => exact congrArg FixedPoint.Pattern.mu hp
  | nu p hp => exact congrArg FixedPoint.Pattern.nu hp

private theorem fixedDenote_cast {S : Type} {A : SortedSignature S} (M : FirstOrder.Model A)
    {r k : Nat} {P : Fin r → S} {Γ Δ : Fin k → S} {s : S} (h : Γ = Δ)
    (p : FixedPoint.Pattern A P Γ s) (v : ∀ i, M.carrier (Δ i)) :
    FixedPoint.Pattern.denote M (h ▸ p) v = p.denote M (h.symm ▸ v) := by
  cases h
  rfl

/-- Native μ and ν denotations commute with general sort-changing reducts. -/
theorem denote_fixedPattern (f : A ⟶ B) (M : FirstOrder.Model B.symbols)
    {r k : Nat} {P : Fin r → A.sorts} {Γ : Fin k → A.sorts} {s : A.sorts}
    (p : FixedPoint.Pattern A.symbols P Γ s) :
    ∀ v, (fixedPattern f p).denote M v = p.denote (reduct f M) v := by
  induction p with
  | base p =>
      intro v
      apply OrderHom.ext
      funext η
      exact denote_pattern f M p v
  | setvar => intro v; rfl
  | app op args ih =>
      intro v
      apply OrderHom.ext
      funext η
      change FixedPoint.application M (f.operations op) (fun i => (fixedPattern f (args i)).denote M v η) = _
      simp only [ih]
      rfl
  | dualApp op args ih =>
      intro v
      apply OrderHom.ext
      funext η
      change FixedPoint.dualApplication M (f.operations op) (fun i => (fixedPattern f (args i)).denote M v η) = _
      simp only [ih]
      rfl
  | conj p q hp hq =>
      intro v
      apply OrderHom.ext
      funext η
      change (fixedPattern f p).denote M v η ∩ (fixedPattern f q).denote M v η = _
      rw [hp, hq]
      rfl
  | disj p q hp hq =>
      intro v
      apply OrderHom.ext
      funext η
      change (fixedPattern f p).denote M v η ∪ (fixedPattern f q).denote M v η = _
      rw [hp, hq]
      rfl
  | ex bound p hp =>
      show ∀ v, (fixedPattern f (.ex bound p)).denote M v = (FixedPoint.Pattern.ex bound p).denote (reduct f M) v
      intro v
      apply OrderHom.ext
      funext η
      change {x | ∃ a, x ∈ (map_cons f bound _ ▸ fixedPattern f p).denote M (Fin.cases a v) η} = _
      simp only [fixedDenote_cast, hp]
      congr 1
      funext result
      congr 1
      funext value
      exact congrArg (fun env => result ∈ p.denote (reduct f M) env η) (env_cons f M bound v value)
  | @all r k P Γ s bound p hp =>
      show ∀ v, (fixedPattern f (.all bound p)).denote M v = (FixedPoint.Pattern.all bound p).denote (reduct f M) v
      intro v
      apply OrderHom.ext
      funext η
      change {x | ∀ a, x ∈ (map_cons f bound _ ▸ fixedPattern f p).denote M (Fin.cases a v) η} = _
      simp only [fixedDenote_cast, hp]
      apply Set.ext
      intro result
      change (∀ value, result ∈ p.denote (reduct f M) (Eq.rec (motive := fun Δ _ => ∀ i, M.carrier (Δ i)) (Fin.cases value v) (map_cons f bound Γ).symm) η) ↔
        ∀ value, result ∈ p.denote (reduct f M) (Fin.cases value v) η
      apply forall_congr'
      intro value
      exact iff_of_eq (congrArg (fun env => result ∈ p.denote (reduct f M) env η) (env_cons f M bound v value))
  | mu p hp =>
      intro v
      apply OrderHom.ext
      funext η
      change (((fixedPattern f p).denote M v).comp (FixedPoint.insert _ M η)).lfp = _
      rw [hp]
      rfl
  | nu p hp =>
      intro v
      apply OrderHom.ext
      funext η
      change (((fixedPattern f p).denote M v).comp (FixedPoint.insert _ M η)).gfp = _
      rw [hp]
      rfl
end Silmaril.Logic.Matching.SortMaps.Hom
