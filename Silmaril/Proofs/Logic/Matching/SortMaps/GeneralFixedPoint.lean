module

public import Silmaril.Logic.Matching.SortMaps.GeneralFixedPoint.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.SortMaps.Hom
open CategoryTheory
variable {A B C : Signature}

private theorem generalPattern_cast (f : A ⟶ B) {r k : Nat} {P : Fin r → A.sorts}
    {Γ Δ : Fin k → A.sorts} {s : A.sorts} (h : Γ = Δ)
    (p : GeneralFixedPoint.Pattern A.symbols P Γ s) :
    generalPattern f (h ▸ p) = congrArg (f.sorts ∘ ·) h ▸ generalPattern f p := by
  cases h
  rfl

private theorem general_transport_heq {S : Type} {A : SortedSignature S} {r k : Nat}
    {P : Fin r → S} {Γ Δ : Fin k → S} {s : S} (h : Γ = Δ)
    (p : GeneralFixedPoint.Pattern A P Γ s) :
    HEq (h ▸ p : GeneralFixedPoint.Pattern A P Δ s) p := by
  cases h
  rfl

@[simp] theorem generalPattern_id {r k : Nat} {P : Fin r → A.sorts}
    {Γ : Fin k → A.sorts} {s : A.sorts}
    (p : GeneralFixedPoint.Pattern A.symbols P Γ s) : generalPattern (𝟙 A) p = p := by
  induction p with
  | base p => exact congrArg GeneralFixedPoint.Pattern.base (pattern_id p)
  | setvar => rfl
  | app op _ ih => exact congrArg (GeneralFixedPoint.Pattern.app op) (funext ih)
  | neg _ ih => exact congrArg GeneralFixedPoint.Pattern.neg ih
  | conj _ _ hp hq => exact congrArg₂ GeneralFixedPoint.Pattern.conj hp hq
  | ex bound p hp =>
      change GeneralFixedPoint.Pattern.ex bound (generalPattern (𝟙 A) p) = .ex bound p
      exact congrArg (GeneralFixedPoint.Pattern.ex bound) hp
  | mu _ ih => exact congrArg GeneralFixedPoint.Pattern.mu ih
  | nu _ ih => exact congrArg GeneralFixedPoint.Pattern.nu ih

@[simp] theorem generalPattern_comp (f : A ⟶ B) (g : B ⟶ C)
    {r k : Nat} {P : Fin r → A.sorts} {Γ : Fin k → A.sorts} {s : A.sorts}
    (p : GeneralFixedPoint.Pattern A.symbols P Γ s) :
    generalPattern (f ≫ g) p = generalPattern g (generalPattern f p) := by
  induction p with
  | base p => exact congrArg GeneralFixedPoint.Pattern.base (pattern_comp f g p)
  | setvar => rfl
  | app op _ ih => exact congrArg (GeneralFixedPoint.Pattern.app _) (funext ih)
  | neg _ ih => exact congrArg GeneralFixedPoint.Pattern.neg ih
  | conj _ _ hp hq => exact congrArg₂ GeneralFixedPoint.Pattern.conj hp hq
  | @ex r k P Γ s bound p hp =>
      change GeneralFixedPoint.Pattern.ex ((f ≫ g).sorts bound)
        ((map_cons (f ≫ g) bound Γ) ▸ generalPattern (f ≫ g) p) =
        GeneralFixedPoint.Pattern.ex (g.sorts (f.sorts bound))
          ((map_cons g (f.sorts bound) (f.sorts ∘ Γ)) ▸
            generalPattern g ((map_cons f bound Γ) ▸ generalPattern f p))
      rw [generalPattern_cast]
      congr 1
      apply eq_of_heq
      exact (general_transport_heq (map_cons (f ≫ g) bound _) _).trans
        ((heq_of_eq hp).trans
          ((general_transport_heq (map_cons g (f.sorts bound) _) _).trans
            (general_transport_heq (congrArg (g.sorts ∘ ·) (map_cons f bound _)) _)).symm)
  | mu _ ih => exact congrArg GeneralFixedPoint.Pattern.mu ih
  | nu _ ih => exact congrArg GeneralFixedPoint.Pattern.nu ih

private theorem generalOccurs_cast {S : Type} {A : SortedSignature S} {r k : Nat}
    {P : Fin r → S} {Γ Δ : Fin k → S} {s : S} (h : Γ = Δ)
    (p : GeneralFixedPoint.Pattern A P Γ s) :
    (h ▸ p : GeneralFixedPoint.Pattern A P Δ s).occurs = p.occurs := by
  cases h
  rfl

private theorem generalAdmissible_cast {S : Type} {A : SortedSignature S} {r k : Nat}
    {P : Fin r → S} {Γ Δ : Fin k → S} {s : S} (h : Γ = Δ)
    (p : GeneralFixedPoint.Pattern A P Γ s) :
    (h ▸ p : GeneralFixedPoint.Pattern A P Δ s).admissible = p.admissible := by
  cases h
  rfl

/-- Both polarities and all free set variables are preserved, including the
binder-local negative occurrence check; no global positivity is imposed. -/
theorem occurs_generalPattern (f : A ⟶ B) {r k : Nat} {P : Fin r → A.sorts}
    {Γ : Fin k → A.sorts} {s : A.sorts}
    (p : GeneralFixedPoint.Pattern A.symbols P Γ s) :
    (generalPattern f p).occurs = p.occurs := by
  induction p with
  | base _ | setvar _ => rfl
  | app op args ih =>
      change (fun n i => (List.finRange _).any (fun j => (generalPattern f (args j)).occurs n i)) = _
      simp only [ih]
      rfl
  | neg p ih =>
      change (fun n i => (generalPattern f p).occurs (!n) i) = _
      rw [ih]
      rfl
  | conj p q hp hq =>
      change (fun n i => (generalPattern f p).occurs n i || (generalPattern f q).occurs n i) = _
      rw [hp, hq]
      rfl
  | ex bound p ih =>
      change (map_cons f bound _ ▸ generalPattern f p).occurs = _
      rw [generalOccurs_cast, ih]
      rfl
  | mu p ih | nu p ih =>
      change (fun n i => (generalPattern f p).occurs n (Fin.succ i)) = _
      rw [ih]
      rfl

theorem admissible_generalPattern (f : A ⟶ B) {r k : Nat} {P : Fin r → A.sorts}
    {Γ : Fin k → A.sorts} {s : A.sorts}
    (p : GeneralFixedPoint.Pattern A.symbols P Γ s) :
    (generalPattern f p).admissible = p.admissible := by
  induction p with
  | base _ | setvar _ => rfl
  | app op args ih =>
      change (List.finRange _).all (fun j => (generalPattern f (args j)).admissible) = _
      simp only [ih]
      rfl
  | neg p ih => exact ih
  | ex bound p ih =>
      change (map_cons f bound _ ▸ generalPattern f p).admissible = _
      rw [generalAdmissible_cast, ih]
      rfl
  | conj p q hp hq =>
      change ((generalPattern f p).admissible && (generalPattern f q).admissible) = _
      rw [hp, hq]
      rfl
  | mu p ih | nu p ih =>
      change ((generalPattern f p).admissible && !(generalPattern f p).occurs true 0) = _
      rw [ih, occurs_generalPattern]
      rfl

private theorem generalDenote_cast {S : Type} {A : SortedSignature S}
    (M : FirstOrder.Model A) {r k : Nat} {P : Fin r → S} {Γ Δ : Fin k → S}
    {s : S} (h : Γ = Δ) (p : GeneralFixedPoint.Pattern A P Γ s)
    (v : ∀ i, M.carrier (Δ i)) :
    GeneralFixedPoint.Pattern.denote M (h ▸ p) v = p.denote M (h.symm ▸ v) := by
  cases h
  rfl

private theorem context_cast_apply {S : Type} {A : SortedSignature S}
    (M : FirstOrder.Model A) {k : Nat} {Γ Δ : Fin k → S}
    (h : Γ = Δ) (v : ∀ i, M.carrier (Γ i)) (i : Fin k) :
    HEq ((h ▸ v : ∀ i, M.carrier (Δ i)) i) (v i) := by
  cases h
  rfl

private theorem general_env_cons (f : Hom A B) (M : FirstOrder.Model B.symbols)
    {k : Nat} {Γ : Fin k → A.sorts} (bound : A.sorts)
    (v : ∀ i, M.carrier (f.sorts (Γ i))) (x : M.carrier (f.sorts bound)) :
    Eq.rec (motive := fun Δ _ => ∀ i, M.carrier (Δ i))
      (Fin.cases x v) (map_cons f bound Γ).symm =
      (show (∀ i, (reduct f M).carrier (Fin.cases bound Γ i)) from Fin.cases x v) := by
  funext i
  cases i using Fin.cases with
  | zero => exact eq_of_heq (context_cast_apply M (map_cons f bound Γ).symm (Fin.cases x v) _)
  | succ i => exact eq_of_heq (context_cast_apply M (map_cons f bound Γ).symm (Fin.cases x v) _)

/-- Denotation transport for the full Boolean syntax, including complement,
locally admitted μ/ν and also the pre-admission denotations of all raw typed
patterns. No monotonicity or global polarity hypothesis is inserted. -/
theorem denote_generalPattern (f : A ⟶ B) (M : FirstOrder.Model B.symbols)
    {r k : Nat} {P : Fin r → A.sorts} {Γ : Fin k → A.sorts} {s : A.sorts}
    (p : GeneralFixedPoint.Pattern A.symbols P Γ s) :
    ∀ v η, (generalPattern f p).denote M v η = p.denote (reduct f M) v η := by
  induction p with
  | base p => intro v η; exact denote_pattern f M p v
  | setvar => intro v η; rfl
  | app op args ih =>
      intro v η
      change FixedPoint.application M (f.operations op)
        (fun i => (generalPattern f (args i)).denote M v η) = _
      simp only [ih]
      rfl
  | neg p ih =>
      intro v η
      change ((generalPattern f p).denote M v η)ᶜ = _
      rw [ih]
      rfl
  | conj p q hp hq =>
      intro v η
      change (generalPattern f p).denote M v η ∩ (generalPattern f q).denote M v η = _
      rw [hp, hq]
      rfl
  | ex bound p ih =>
      intro v η
      change {x | ∃ a, x ∈ (map_cons f bound _ ▸ generalPattern f p).denote M (Fin.cases a v) η} = _
      simp only [generalDenote_cast, ih]
      congr 1
      funext result
      congr 1
      funext value
      exact congrArg (fun env => result ∈ p.denote (reduct f M) env η)
        (general_env_cons f M bound v value)
  | mu p ih =>
      intro v η
      change sInf {X | (generalPattern f p).denote M v (Fin.cases X η) ⊆ X} = _
      simp only [ih]
      rfl
  | nu p ih =>
      intro v η
      change sSup {X | X ⊆ (generalPattern f p).denote M v (Fin.cases X η)} = _
      simp only [ih]
      rfl

def generalSentence (f : A ⟶ B) (p : GeneralFixedPoint.Sentence A.symbols) :
    GeneralFixedPoint.Sentence B.symbols :=
  ⟨p.setCount, p.objectCount, f.sorts ∘ p.sets, f.sorts ∘ p.objects,
    f.sorts p.sort, generalPattern f p.pattern,
    by rw [admissible_generalPattern]; exact p.admitted⟩

@[simp] theorem generalSentence_id (p : GeneralFixedPoint.Sentence A.symbols) :
    generalSentence (𝟙 A) p = p := by
  cases p
  simp only [generalSentence, generalPattern_id]
  rfl

@[simp] theorem generalSentence_comp (f : A ⟶ B) (g : B ⟶ C)
    (p : GeneralFixedPoint.Sentence A.symbols) :
    generalSentence (f ≫ g) p = generalSentence g (generalSentence f p) := by
  cases p
  simp only [generalSentence, generalPattern_comp]
  rfl

theorem generalSatisfaction (f : A ⟶ B) (M : FirstOrder.Model B.symbols)
    (p : GeneralFixedPoint.Sentence A.symbols) :
    GeneralFixedPoint.Sentence.Satisfies M (generalSentence f p) ↔
      GeneralFixedPoint.Sentence.Satisfies (reduct f M) p := by
  change (∀ v η x, x ∈ (generalPattern f p.pattern).denote M v η) ↔ _
  simp only [denote_generalPattern]
  rfl

end Silmaril.Logic.Matching.SortMaps.Hom
