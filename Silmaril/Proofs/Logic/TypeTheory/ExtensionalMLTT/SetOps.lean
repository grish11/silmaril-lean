module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.SetOps.Defs

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.SetSem

universe u

open ZFSet
open Silmaril.Logic.SetTheory

noncomputable section
open Classical

@[simp] theorem mem_tt {a : ZFSet.{u}} : a ∈ tt ↔ a = ∅ := by
  simp [tt]

@[simp] theorem mem_truth {p : Prop} {a : ZFSet.{u}} : a ∈ truth p ↔ p ∧ a = ∅ := by
  by_cases h : p <;> simp [truth, h]

@[simp] theorem truth_true : truth True = (tt : ZFSet.{u}) := by simp [truth]
@[simp] theorem truth_false : truth False = (∅ : ZFSet.{u}) := by simp [truth]

@[simp] theorem fst_pair (a b : ZFSet.{u}) : fst (pair a b) = a := by
  have h : ∃ x y, pair a b = pair x y := ⟨a, b, rfl⟩
  rw [fst, dite_eq_left h]
  exact (ZFSet.pair_inj.1 h.choose_spec.choose_spec).1.symm

@[simp] theorem snd_pair (a b : ZFSet.{u}) : snd (pair a b) = b := by
  have h : ∃ x y, pair a b = pair x y := ⟨a, b, rfl⟩
  rw [snd, dite_eq_left h]
  exact (ZFSet.pair_inj.1 h.choose_spec.choose_spec).2.symm

theorem mem_lam {A z : ZFSet.{u}} {g : ZFSet.{u} → ZFSet.{u}} :
    z ∈ lam A g ↔ ∃ a ∈ A, pair a (g a) = z := by
  simp only [lam, ZFSet.mem_range]
  exact ⟨fun ⟨a, h⟩ => ⟨a.1, a.2, h⟩, fun ⟨a, ha, h⟩ => ⟨⟨a, ha⟩, h⟩⟩

@[simp] theorem pair_mem_lam {A a b : ZFSet.{u}} {g : ZFSet.{u} → ZFSet.{u}} :
    pair a b ∈ lam A g ↔ a ∈ A ∧ b = g a := by
  rw [mem_lam]
  simp only [ZFSet.pair_inj]
  constructor
  · rintro ⟨x, hx, rfl, h⟩
    exact ⟨hx, h.symm⟩
  · rintro ⟨ha, rfl⟩
    exact ⟨a, ha, rfl, rfl⟩

/-- Application computes a graph at every member of its domain. -/
@[simp] theorem app_lam {A a : ZFSet.{u}} (g : ZFSet.{u} → ZFSet.{u}) (ha : a ∈ A) :
    app (lam A g) a = g a := by
  have h : ∃ b, pair a b ∈ lam A g := ⟨g a, pair_mem_lam.2 ⟨ha, rfl⟩⟩
  rw [app, dite_eq_left h]
  exact (pair_mem_lam.1 h.choose_spec).2

/-- A graph only depends on its function on the specified domain. -/
theorem lam_congr {A : ZFSet.{u}} {g h : ZFSet.{u} → ZFSet.{u}}
    (e : ∀ a ∈ A, g a = h a) : lam A g = lam A h := by
  ext z
  rw [mem_lam, mem_lam]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, by rw [e a ha]⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, by rw [e a ha]⟩

/-- Product members are exactly the graphs of pointwise typed sections. -/
theorem mem_pi {A f : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}} :
    f ∈ pi A B ↔ ∃ g : ZFSet.{u} → ZFSet.{u},
      (∀ a ∈ A, g a ∈ B a) ∧ lam A g = f := by
  rw [pi, ZFSet.mem_range]
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨_, ?_, rfl⟩
    intro a ha
    simp only [dite_eq_left ha]
    exact (s ⟨a, ha⟩).2
  · rintro ⟨g, hg, rfl⟩
    refine ⟨fun a => ⟨g a.1, hg a.1 a.2⟩, ?_⟩
    apply lam_congr
    intro a ha
    simp only [dite_eq_left ha]

/-- Lambda abstraction introduces a dependent product. -/
theorem lam_mem_pi {A : ZFSet.{u}} {B g : ZFSet.{u} → ZFSet.{u}}
    (hg : ∀ a ∈ A, g a ∈ B a) : lam A g ∈ pi A B :=
  mem_pi.2 ⟨g, hg, rfl⟩

/-- A member of a dependent product maps each argument into its fibre. -/
theorem app_mem_of_mem_pi {A f a : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (hf : f ∈ pi A B) (ha : a ∈ A) : app f a ∈ B a := by
  obtain ⟨g, hg, rfl⟩ := mem_pi.1 hf
  rw [app_lam g ha]
  exact hg a ha

/-- Every member of a dependent product is its application graph. -/
theorem lam_app_of_mem_pi {A f : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (hf : f ∈ pi A B) : lam A (app f) = f := by
  obtain ⟨g, -, rfl⟩ := mem_pi.1 hf
  apply lam_congr
  intro a ha
  exact app_lam g ha

/-- Pointwise equality determines members of a dependent product. -/
theorem pi_ext {A f g : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (hf : f ∈ pi A B) (hg : g ∈ pi A B)
    (h : ∀ a ∈ A, app f a = app g a) : f = g := by
  rw [← lam_app_of_mem_pi hf, ← lam_app_of_mem_pi hg]
  exact lam_congr h

/-- Fibres outside the domain do not affect a dependent product. -/
theorem pi_congr {A : ZFSet.{u}} {B C : ZFSet.{u} → ZFSet.{u}}
    (h : ∀ a ∈ A, B a = C a) : pi A B = pi A C := by
  ext f
  rw [mem_pi, mem_pi]
  constructor
  · rintro ⟨g, hg, e⟩
    exact ⟨g, fun a ha => h a ha ▸ hg a ha, e⟩
  · rintro ⟨g, hg, e⟩
    exact ⟨g, fun a ha => (h a ha).symm ▸ hg a ha, e⟩

theorem mem_sigma {A p : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}} :
    p ∈ sigma A B ↔ ∃ a ∈ A, ∃ b ∈ B a, pair a b = p := by
  rw [sigma, ZFSet.mem_range]
  exact ⟨fun ⟨p, e⟩ => ⟨p.1.1, p.1.2, p.2.1, p.2.2, e⟩,
    fun ⟨a, ha, b, hb, e⟩ => ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, e⟩⟩

@[simp] theorem pair_mem_sigma {A a b : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}} :
    pair a b ∈ sigma A B ↔ a ∈ A ∧ b ∈ B a := by
  rw [mem_sigma]
  simp only [ZFSet.pair_inj]
  constructor
  · rintro ⟨x, hx, y, hy, rfl, rfl⟩
    exact ⟨hx, hy⟩
  · rintro ⟨ha, hb⟩
    exact ⟨a, ha, b, hb, rfl, rfl⟩

theorem fst_mem_of_mem_sigma {A p : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (hp : p ∈ sigma A B) : fst p ∈ A := by
  obtain ⟨a, ha, b, -, rfl⟩ := mem_sigma.1 hp
  simpa using ha

theorem snd_mem_of_mem_sigma {A p : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (hp : p ∈ sigma A B) : snd p ∈ B (fst p) := by
  obtain ⟨a, -, b, hb, rfl⟩ := mem_sigma.1 hp
  simpa using hb

theorem pair_fst_snd_of_mem_sigma {A p : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (hp : p ∈ sigma A B) : pair (fst p) (snd p) = p := by
  obtain ⟨a, -, b, -, rfl⟩ := mem_sigma.1 hp
  simp

/-- Equal projections determine a member of a dependent sum. -/
theorem sigma_ext {A p q : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (hp : p ∈ sigma A B) (hq : q ∈ sigma A B)
    (h₁ : fst p = fst q) (h₂ : snd p = snd q) : p = q := by
  rw [← pair_fst_snd_of_mem_sigma hp, ← pair_fst_snd_of_mem_sigma hq, h₁, h₂]

/-- Fibres outside the domain do not affect a dependent sum. -/
theorem sigma_congr {A : ZFSet.{u}} {B C : ZFSet.{u} → ZFSet.{u}}
    (h : ∀ a ∈ A, B a = C a) : sigma A B = sigma A C := by
  ext p
  rw [mem_sigma, mem_sigma]
  constructor
  · rintro ⟨a, ha, b, hb, e⟩
    exact ⟨a, ha, b, h a ha ▸ hb, e⟩
  · rintro ⟨a, ha, b, hb, e⟩
    exact ⟨a, ha, b, (h a ha).symm ▸ hb, e⟩

/-- Primitive recursion computes on the chosen numeral, independently of choice. -/
@[simp] theorem natrec_numeral (z : ZFSet.{u})
    (s : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}) (n : ℕ) :
    natrec z s (numeral n) = Nat.rec z (fun n r => s (numeral n) r) n := by
  have h : ∃ m, numeral m = (numeral n : ZFSet.{u}) := ⟨n, rfl⟩
  rw [natrec, dite_eq_left h, numeral_injective h.choose_spec]

@[simp] theorem natrec_zero (z : ZFSet.{u})
    (s : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}) : natrec z s ∅ = z := by
  simpa using natrec_numeral z s 0

/-- The successor equation is needed only on natural-number inputs. -/
theorem natrec_succ (z : ZFSet.{u})
    (s : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}) {n : ZFSet.{u}} (hn : n ∈ omega) :
    natrec z s (insert n n) = s n (natrec z s n) := by
  obtain ⟨n, rfl⟩ := mem_omega_iff.1 hn
  change natrec z s (numeral (n + 1)) = _
  simp only [natrec_numeral]

/-- Recursion preserves an arbitrary family of sets over `ω`. -/
theorem natrec_mem {B : ZFSet.{u} → ZFSet.{u}} {z n : ZFSet.{u}}
    {s : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}} (hz : z ∈ B ∅)
    (hs : ∀ m ∈ omega, ∀ r ∈ B m, s m r ∈ B (insert m m)) (hn : n ∈ omega) :
    natrec z s n ∈ B n := by
  obtain ⟨n, rfl⟩ := mem_omega_iff.1 hn
  clear hn
  simp only [natrec_numeral]
  induction n with
  | zero => exact hz
  | succ n ih => exact hs _ (numeral_mem_omega n) _ ih

/-- Pointwise equality of steps on reachable inputs is enough for recursion. -/
theorem natrec_congr {B : ZFSet.{u} → ZFSet.{u}} {z z' n : ZFSet.{u}}
    {s s' : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}}
    (hz : z = z') (hzB : z ∈ B ∅)
    (hsB : ∀ m ∈ omega, ∀ r ∈ B m, s m r ∈ B (insert m m))
    (hs : ∀ m ∈ omega, ∀ r ∈ B m, s m r = s' m r) (hn : n ∈ omega) :
    natrec z s n = natrec z' s' n := by
  subst z'
  obtain ⟨n, rfl⟩ := mem_omega_iff.1 hn
  clear hn
  simp only [natrec_numeral]
  induction n with
  | zero => rfl
  | succ n ih =>
    change s (numeral n) _ = s' (numeral n) _
    rw [← ih]
    apply hs _ (numeral_mem_omega n)
    simpa only [natrec_numeral] using
      (natrec_mem hzB hsB (numeral_mem_omega n))

end
end Silmaril.Logic.TypeTheory.ExtensionalMLTT.SetSem
