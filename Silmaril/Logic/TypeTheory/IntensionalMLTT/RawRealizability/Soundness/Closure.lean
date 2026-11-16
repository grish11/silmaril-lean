module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability.Soundness.Defs
public import Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability.Computation
import Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilitySoundness

public section

/-! Reusable actual code/member closure laws for the unchanged original typing rules. -/

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability

theorem realizes_univ_iff {n i : ℕ} {A : Term n} {ρ : Environment n 0} :
    Realizes A (.univ i) ρ ↔ ∃ X, Code i (eval A ρ) X :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilitySoundness.realizes_univ_iff

theorem realizes_mem {n k : ℕ} {t A : Term n} {ρ : Environment n 0}
    {X : Set (Value 0)} (hX : Code k (eval A ρ) X) (ht : Realizes t A ρ) :
    eval t ρ ∈ X :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilitySoundness.realizes_mem hX ht

theorem context_cons {n i : ℕ} {Γ : Context n} {A : Term n} {ρ : Environment n 0}
    {X : Set (Value 0)} {a : Value 0} (hρ : RealizesContext Γ ρ)
    (hA : Code i (eval A ρ) X) (ha : a ∈ X) :
    RealizesContext (Γ.snoc A) (Fin.cons a ρ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilitySoundness.context_cons hρ hA ha

theorem lookup {n : ℕ} {Γ : Context n} {i : Fin n} {A : Term n} (hi : Lookup Γ i A) :
    ∀ ρ, RealizesContext Γ ρ → Realizes (.var i) A ρ :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilitySoundness.lookup hi

theorem valid_code {n i : ℕ} {Γ : Context n} {A : Term n}
    (h : Valid Γ A (.univ i)) {ρ : Environment n 0} (hρ : RealizesContext Γ ρ) :
    ∃ X, Code i (eval A ρ) X :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilitySoundness.valid_code h hρ

theorem realizes_app {n : ℕ} {f a A : Term n} {B : Term (n+1)} {ρ : Environment n 0}
    (hf : Realizes f (.pi A B) ρ) (ha : Realizes a A ρ) :
    Realizes (.app f a) (B.instantiate a) ρ :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilitySoundness.realizes_app hf ha

theorem family_codes {n i j : ℕ} {Γ : Context n} {A : Term n} {B : Term (n+1)}
    (hB : Valid (Γ.snoc A) B (.univ j)) {ρ : Environment n 0}
    {X : Set (Value 0)} (hρ : RealizesContext Γ ρ) (hA : Code i (eval A ρ) X) :
    ∃ Y : Value 0 → Set (Value 0), ∀ a ∈ X,
      Code j (instantiate (eval B (liftEnv ρ)) a) (Y a) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilitySoundness.family_codes hB hρ hA

theorem valid_pi {n i j : ℕ} {Γ : Context n} {A : Term n} {B : Term (n+1)}
    (hA : Valid Γ A (.univ i)) (hB : Valid (Γ.snoc A) B (.univ j)) :
    Valid Γ (.pi A B) (.univ (max i j)) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilitySoundness.valid_pi hA hB

theorem valid_sigma {n i j : ℕ} {Γ : Context n} {A : Term n} {B : Term (n+1)}
    (hA : Valid Γ A (.univ i)) (hB : Valid (Γ.snoc A) B (.univ j)) :
    Valid Γ (.sigma A B) (.univ (max i j)) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilitySoundness.valid_sigma hA hB

theorem valid_lam {n i j : ℕ} {Γ : Context n} {A : Term n} {B body : Term (n+1)}
    (hA : Valid Γ A (.univ i)) (hB : Valid (Γ.snoc A) B (.univ j))
    (ht : Valid (Γ.snoc A) body B) : Valid Γ (.lam A body) (.pi A B) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilitySoundness.valid_lam hA hB ht

theorem valid_pair {n i j : ℕ} {Γ : Context n} {A a b : Term n} {B : Term (n+1)}
    (hA : Valid Γ A (.univ i)) (hB : Valid (Γ.snoc A) B (.univ j))
    (ha : Valid Γ a A) (hb : Valid Γ b (B.instantiate a)) :
    Valid Γ (.pair a b) (.sigma A B) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilitySoundness.valid_pair hA hB ha hb

theorem valid_fst {n : ℕ} {Γ : Context n} {A p : Term n} {B : Term (n+1)}
    (hp : Valid Γ p (.sigma A B)) : Valid Γ (.fst p) A :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilitySoundness.valid_fst hp

theorem valid_snd {n : ℕ} {Γ : Context n} {A p : Term n} {B : Term (n+1)}
    (hp : Valid Γ p (.sigma A B)) : Valid Γ (.snd p) (B.instantiate (.fst p)) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilitySoundness.valid_snd hp

theorem valid_id {n i : ℕ} {Γ : Context n} {A a b : Term n}
    (hA : Valid Γ A (.univ i)) (ha : Valid Γ a A) (hb : Valid Γ b A) :
    Valid Γ (.id A a b) (.univ i) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilitySoundness.valid_id hA ha hb

theorem valid_refl {n i : ℕ} {Γ : Context n} {A a : Term n}
    (hA : Valid Γ A (.univ i)) (ha : Valid Γ a A) :
    Valid Γ (.refl a) (.id A a a) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilitySoundness.valid_refl hA ha

theorem valid_conv {n : ℕ} {Γ : Context n} {t A B : Term n}
    (ht : Valid Γ t A) (hAB : Conversion A B) : Valid Γ t B :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilitySoundness.valid_conv ht hAB

theorem valid_cumulative {n i j : ℕ} {Γ : Context n} {A : Term n}
    (hA : Valid Γ A (.univ i)) (hij : i ≤ j) : Valid Γ A (.univ j) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilitySoundness.valid_cumulative hA hij

theorem valid_j {n : ℕ} {Γ : Context n} {A a d b p : Term n} {C : Term (n+2)}
    (hd : Valid Γ d (C.instantiate₂ a (.refl a)))
    (hp : Valid Γ p (.id A a b)) : Valid Γ (.j A a C d b p) (C.instantiate₂ b p) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilitySoundness.valid_j hd hp

theorem valid_succ {n : ℕ} {Γ : Context n} {t : Term n}
    (ht : Valid Γ t .nat) : Valid Γ (.succ t) .nat :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilitySoundness.valid_succ ht

theorem code_application {f a A : Value 0} {B : Value 1}
    (hf : ∃ i X, Code i (pi A B) X ∧ f ∈ X)
    (ha : ∃ i X, Code i A X ∧ a ∈ X) :
    ∃ i X, Code i (instantiate B a) X ∧ app f a ∈ X :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilitySoundness.code_application hf ha

theorem valid_natrec {n : ℕ} {Γ : Context n} {C : Term (n+1)} {z s t : Term n}
    (hz : Valid Γ z (C.instantiate .zero)) (hs : Valid Γ s C.natStepType)
    (ht : Valid Γ t .nat) : Valid Γ (.natrec C z s t) (C.instantiate t) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilitySoundness.valid_natrec hz hs ht

end Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability
