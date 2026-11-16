module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Reduction.Defs
import Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Reduction

@[expose] public section

/-!
# Directed reduction and exact conversion factorization

All primitive laws and compatible term positions belong to the existing full
intensional grammar, including cumulative-universe annotations and both J
motive binders. Conversion is exactly a finite zigzag of these contractions.
Confluence, constructor injectivity and subject reduction are separate results.
-/

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT

theorem RootReduction.rename {n m : ℕ} {t u : Term n} (h : RootReduction t u) (ρ : Fin n → Fin m) :
    RootReduction (t.rename ρ) (u.rename ρ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Reduction.root_rename h ρ

theorem RootReduction.subst {n m : ℕ} {t u : Term n} (h : RootReduction t u) (σ : Fin n → Term m) :
    RootReduction (t.subst σ) (u.subst σ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Reduction.root_subst h σ

theorem RootReduction.toConvertible {n : ℕ} {t u : Term n} (h : RootReduction t u) : Convertible t u :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Reduction.root_convertible h

theorem ReductionStep.rename {n m : ℕ} {t u : Term n} (h : ReductionStep t u) (ρ : Fin n → Fin m) :
    ReductionStep (t.rename ρ) (u.rename ρ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Reduction.step_rename h ρ

theorem ReductionStep.subst {n m : ℕ} {t u : Term n} (h : ReductionStep t u) (σ : Fin n → Term m) :
    ReductionStep (t.subst σ) (u.subst σ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Reduction.step_subst h σ

theorem ReductionStep.toConvertible {n : ℕ} {t u : Term n} (h : ReductionStep t u) : Convertible t u :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Reduction.step_convertible h

theorem Reduces.refl {n : ℕ} (t : Term n) : Reduces t t := Relation.ReflTransGen.refl

theorem ReductionStep.toReduces {n : ℕ} {t u : Term n} (h : ReductionStep t u) : Reduces t u :=
  .single h

theorem Reduces.trans {n : ℕ} {t u v : Term n} (h : Reduces t u) (k : Reduces u v) : Reduces t v :=
  Relation.ReflTransGen.trans h k

theorem Reduces.rename {n m : ℕ} {t u : Term n} (h : Reduces t u) (ρ : Fin n → Fin m) :
    Reduces (t.rename ρ) (u.rename ρ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Reduction.reduces_map (fun t => t.rename ρ) (fun h => h.rename ρ) h

theorem Reduces.subst {n m : ℕ} {t u : Term n} (h : Reduces t u) (σ : Fin n → Term m) :
    Reduces (t.subst σ) (u.subst σ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Reduction.reduces_map (fun t => t.subst σ) (fun h => h.subst σ) h

theorem Reduces.congr_succ {n : ℕ} {t t' : Term n}
    (ht : Reduces t t') :
    Reduces (.succ t) (.succ t') :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Reduction.reduces_congr_succ ht

theorem Reduces.congr_pi {n : ℕ} {A A' : Term n} {B B' : Term (n + 1)}
    (hA : Reduces A A') (hB : Reduces B B') :
    Reduces (.pi A B) (.pi A' B') :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Reduction.reduces_congr_pi hA hB

theorem Reduces.congr_sigma {n : ℕ} {A A' : Term n} {B B' : Term (n + 1)}
    (hA : Reduces A A') (hB : Reduces B B') :
    Reduces (.sigma A B) (.sigma A' B') :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Reduction.reduces_congr_sigma hA hB

theorem Reduces.congr_lam {n : ℕ} {A A' : Term n} {body body' : Term (n + 1)}
    (hA : Reduces A A') (hbody : Reduces body body') :
    Reduces (.lam A body) (.lam A' body') :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Reduction.reduces_congr_lam hA hbody

theorem Reduces.congr_app {n : ℕ} {f f' : Term n} {a a' : Term n}
    (hf : Reduces f f') (ha : Reduces a a') :
    Reduces (.app f a) (.app f' a') :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Reduction.reduces_congr_app hf ha

theorem Reduces.congr_pair {n : ℕ} {a a' : Term n} {b b' : Term n}
    (ha : Reduces a a') (hb : Reduces b b') :
    Reduces (.pair a b) (.pair a' b') :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Reduction.reduces_congr_pair ha hb

theorem Reduces.congr_fst {n : ℕ} {p p' : Term n}
    (hp : Reduces p p') :
    Reduces (.fst p) (.fst p') :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Reduction.reduces_congr_fst hp

theorem Reduces.congr_snd {n : ℕ} {p p' : Term n}
    (hp : Reduces p p') :
    Reduces (.snd p) (.snd p') :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Reduction.reduces_congr_snd hp

theorem Reduces.congr_natrec {n : ℕ} {C C' : Term (n + 1)} {z z' : Term n} {s s' : Term n} {t t' : Term n}
    (hC : Reduces C C') (hz : Reduces z z') (hs : Reduces s s') (ht : Reduces t t') :
    Reduces (.natrec C z s t) (.natrec C' z' s' t') :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Reduction.reduces_congr_natrec hC hz hs ht

theorem Reduces.congr_absurd {n : ℕ} {A A' : Term n} {e e' : Term n}
    (hA : Reduces A A') (he : Reduces e e') :
    Reduces (.absurd A e) (.absurd A' e') :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Reduction.reduces_congr_absurd hA he

theorem Reduces.congr_id {n : ℕ} {A A' : Term n} {a a' : Term n} {b b' : Term n}
    (hA : Reduces A A') (ha : Reduces a a') (hb : Reduces b b') :
    Reduces (.id A a b) (.id A' a' b') :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Reduction.reduces_congr_id hA ha hb

theorem Reduces.congr_refl {n : ℕ} {a a' : Term n}
    (ha : Reduces a a') :
    Reduces (.refl a) (.refl a') :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Reduction.reduces_congr_refl ha

theorem Reduces.congr_j {n : ℕ} {A A' : Term n} {a a' : Term n} {C C' : Term (n + 2)} {d d' : Term n} {b b' : Term n} {p p' : Term n}
    (hA : Reduces A A') (ha : Reduces a a') (hC : Reduces C C') (hd : Reduces d d') (hb : Reduces b b') (hp : Reduces p p') :
    Reduces (.j A a C d b p) (.j A' a' C' d' b' p') :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Reduction.reduces_congr_j hA ha hC hd hb hp

/-- Factor an existing proof-relevant conversion into finite directed-step zigzags. -/
theorem Conversion.toReductionZigzag {n : ℕ} {t u : Term n} (h : Conversion t u) :
    ReductionZigzag t u :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Reduction.conversion_zigzag h

/-- Every generated zigzag is an existing raw conversion. -/
theorem ReductionZigzag.toConvertible {n : ℕ} {t u : Term n} (h : ReductionZigzag t u) :
    Convertible t u :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Reduction.zigzag_convertible h

theorem Reduces.toConvertible {n : ℕ} {t u : Term n} (h : Reduces t u) : Convertible t u :=
  ReductionZigzag.toConvertible (Relation.EqvGen.reflTransGen_le_eqvGen ReductionStep t u h)

/-- Independently reduced copies of the based-J endpoint may be synchronized before contraction. -/
theorem Reduces.j_synchronize {n : ℕ} {A a b c d r : Term n} {C : Term (n + 2)}
    (ha : Reduces a r) (hb : Reduces b r) (hc : Reduces c r) :
    Reduces (.j A a C d b (.refl c)) d := by
  have h := Reduces.congr_j (.refl A) ha (.refl C) (.refl d) hb (Reduces.congr_refl hc)
  exact h.trans (ReductionStep.toReduces (.root (.j_refl A r C d)))

/-- The oriented presentation generates exactly the original raw conversion relation. -/
theorem convertible_iff_reductionZigzag {n : ℕ} {t u : Term n} :
    Convertible t u ↔ ReductionZigzag t u :=
  ⟨fun ⟨h⟩ => h.toReductionZigzag, ReductionZigzag.toConvertible⟩

/-- Equivalently, conversion is a finite path of forward or backward compatible steps. -/
theorem convertible_iff_reductionChain {n : ℕ} {t u : Term n} :
    Convertible t u ↔ Relation.ReflTransGen (Relation.SymmGen ReductionStep) t u := by
  rw [Relation.EqvGen.reflTransGen_symmGen]
  exact convertible_iff_reductionZigzag

end Silmaril.Logic.TypeTheory.IntensionalMLTT
