module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.OriginalHypotheses.Defs
public import Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability.Soundness.Closure

public section

namespace Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.OriginalHypotheses

open Silmaril.Logic.TypeTheory.IntensionalMLTT
open Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability

/-- Hypothesis substitution traverses every original rule and context premise. -/
noncomputable def bind {H K : Set ScopedTyping} {n : ℕ} {Γ : Context n} {t A : Term n}
    (d : DerivationH H Γ t A)
    (hH : ∀ q ∈ H, DerivationH K q.Γ q.term q.carrier) : DerivationH K Γ t A := by
  induction d using DerivationH.rec (motive_1 := fun Γ _ => ContextDerivationH K Γ) with
  | hyp hq => exact hH _ hq
  | nil => exact .nil
  | snoc _ _ ihΓ ihA => exact .snoc ihΓ ihA
  | univ _ i ihΓ => exact .univ ihΓ i
  | nat _ ihΓ => exact .nat ihΓ
  | empty _ ihΓ => exact .empty ihΓ
  | unit _ ihΓ => exact .unit ihΓ
  | var _ hi ihΓ => exact .var ihΓ hi
  | pi _ _ ihA ihB => exact .pi ihA ihB
  | sigma _ _ ihA ihB => exact .sigma ihA ihB
  | lam _ _ _ ihA ihB iht => exact .lam ihA ihB iht
  | app _ _ ihf iha => exact .app ihf iha
  | pair _ _ _ _ ihA ihB iha ihb => exact .pair ihA ihB iha ihb
  | fst _ ihp => exact .fst ihp
  | snd _ ihp => exact .snd ihp
  | zero _ ihΓ => exact .zero ihΓ
  | succ _ iht => exact .succ iht
  | natrec _ _ _ _ ihC ihz ihs iht => exact .natrec ihC ihz ihs iht
  | star _ ihΓ => exact .star ihΓ
  | absurd _ _ ihA ihe => exact .absurd ihA ihe
  | id _ _ _ ihA iha ihb => exact .id ihA iha ihb
  | refl _ _ ihA iha => exact .refl ihA iha
  | j _ _ _ _ _ _ ihA iha ihC ihd ihb ihp => exact .j ihA iha ihC ihd ihb ihp
  | conv _ _ hAB iht ihB => exact .conv iht ihB hAB
  | cumulative _ hij ihA => exact .cumulative ihA hij

/-- Replace hypothesis leaves while retaining a prescribed bound on every proof-tree node. -/
noncomputable def bindBoundedCore {H K : Set ScopedTyping} {n : ℕ} {Γ : Context n} {t A : Term n}
    (d : DerivationH H Γ t A) : ∀ cap, d.universeBudget ≤ cap →
    (∀ q ∈ H, BoundedDerivationH cap K q.Γ q.term q.carrier) → BoundedDerivationH cap K Γ t A := by
  induction d using DerivationH.rec
      (motive_1 := fun Γ d => ∀ cap, d.universeBudget ≤ cap →
        (∀ q ∈ H, BoundedDerivationH cap K q.Γ q.term q.carrier) →
        {k : ContextDerivationH K Γ // k.universeBudget ≤ cap}) with
  | nil => exact ⟨.nil, Nat.zero_le _⟩
  | snoc _ _ ihΓ ihA cap hBudget hH =>
    rcases max_le_iff.mp hBudget with ⟨hΓ, hA⟩
    rcases ihΓ cap hΓ hH with ⟨dΓ, bΓ⟩
    rcases ihA cap hA hH with ⟨dA, bA⟩
    exact ⟨.snoc dΓ dA, max_le bΓ bA⟩
  | hyp hq => exact fun _ _ hH => hH _ hq
  | univ _ i ihΓ =>
    intro cap hBudget hH
    show BoundedDerivationH cap K _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases ihΓ cap hChildren hH with ⟨dΓ, bΓ⟩
    exact ⟨.univ dΓ i, max_le hNode bΓ⟩
  | nat _ ihΓ =>
    intro cap hBudget hH
    show BoundedDerivationH cap K _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases ihΓ cap hChildren hH with ⟨dΓ, bΓ⟩
    exact ⟨.nat dΓ, max_le hNode bΓ⟩
  | empty _ ihΓ =>
    intro cap hBudget hH
    show BoundedDerivationH cap K _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases ihΓ cap hChildren hH with ⟨dΓ, bΓ⟩
    exact ⟨.empty dΓ, max_le hNode bΓ⟩
  | unit _ ihΓ =>
    intro cap hBudget hH
    show BoundedDerivationH cap K _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases ihΓ cap hChildren hH with ⟨dΓ, bΓ⟩
    exact ⟨.unit dΓ, max_le hNode bΓ⟩
  | var _ hi ihΓ =>
    intro cap hBudget hH
    show BoundedDerivationH cap K _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases ihΓ cap hChildren hH with ⟨dΓ, bΓ⟩
    exact ⟨.var dΓ hi, max_le hNode bΓ⟩
  | pi _ _ ihA ihB =>
    intro cap hBudget hH
    show BoundedDerivationH cap K _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases max_le_iff.mp hChildren with ⟨hA, hB⟩
    rcases ihA cap hA hH with ⟨dA, bA⟩
    rcases ihB cap hB hH with ⟨dB, bB⟩
    exact ⟨.pi dA dB, max_le hNode (max_le bA bB)⟩
  | sigma _ _ ihA ihB =>
    intro cap hBudget hH
    show BoundedDerivationH cap K _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases max_le_iff.mp hChildren with ⟨hA, hB⟩
    rcases ihA cap hA hH with ⟨dA, bA⟩
    rcases ihB cap hB hH with ⟨dB, bB⟩
    exact ⟨.sigma dA dB, max_le hNode (max_le bA bB)⟩
  | lam _ _ _ ihA ihB iht =>
    intro cap hBudget hH
    show BoundedDerivationH cap K _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases max_le_iff.mp hChildren with ⟨hA, hGroup4R⟩
    rcases max_le_iff.mp hGroup4R with ⟨hB, ht⟩
    rcases ihA cap hA hH with ⟨dA, bA⟩
    rcases ihB cap hB hH with ⟨dB, bB⟩
    rcases iht cap ht hH with ⟨dt, bt⟩
    exact ⟨.lam dA dB dt, max_le hNode (max_le bA (max_le bB bt))⟩
  | app _ _ ihf iha =>
    intro cap hBudget hH
    show BoundedDerivationH cap K _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases max_le_iff.mp hChildren with ⟨hf, ha⟩
    rcases ihf cap hf hH with ⟨df, bf⟩
    rcases iha cap ha hH with ⟨da, ba⟩
    exact ⟨.app df da, max_le hNode (max_le bf ba)⟩
  | pair _ _ _ _ ihA ihB iha ihb =>
    intro cap hBudget hH
    show BoundedDerivationH cap K _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases max_le_iff.mp hChildren with ⟨hGroup4L, hGroup4R⟩
    rcases max_le_iff.mp hGroup4L with ⟨hA, hB⟩
    rcases max_le_iff.mp hGroup4R with ⟨ha, hb⟩
    rcases ihA cap hA hH with ⟨dA, bA⟩
    rcases ihB cap hB hH with ⟨dB, bB⟩
    rcases iha cap ha hH with ⟨da, ba⟩
    rcases ihb cap hb hH with ⟨db, bb⟩
    exact ⟨.pair dA dB da db, max_le hNode (max_le (max_le bA bB) (max_le ba bb))⟩
  | fst _ ihp =>
    intro cap hBudget hH
    show BoundedDerivationH cap K _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases ihp cap hChildren hH with ⟨dp, bp⟩
    exact ⟨.fst dp, max_le hNode bp⟩
  | snd _ ihp =>
    intro cap hBudget hH
    show BoundedDerivationH cap K _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases ihp cap hChildren hH with ⟨dp, bp⟩
    exact ⟨.snd dp, max_le hNode bp⟩
  | zero _ ihΓ =>
    intro cap hBudget hH
    show BoundedDerivationH cap K _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases ihΓ cap hChildren hH with ⟨dΓ, bΓ⟩
    exact ⟨.zero dΓ, max_le hNode bΓ⟩
  | succ _ iht =>
    intro cap hBudget hH
    show BoundedDerivationH cap K _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases iht cap hChildren hH with ⟨dt, bt⟩
    exact ⟨.succ dt, max_le hNode bt⟩
  | natrec _ _ _ _ ihC ihz ihs iht =>
    intro cap hBudget hH
    show BoundedDerivationH cap K _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases max_le_iff.mp hChildren with ⟨hGroup4L, hGroup4R⟩
    rcases max_le_iff.mp hGroup4L with ⟨hC, hz⟩
    rcases max_le_iff.mp hGroup4R with ⟨hs, ht⟩
    rcases ihC cap hC hH with ⟨dC, bC⟩
    rcases ihz cap hz hH with ⟨dz, bz⟩
    rcases ihs cap hs hH with ⟨ds, bs⟩
    rcases iht cap ht hH with ⟨dt, bt⟩
    exact ⟨.natrec dC dz ds dt, max_le hNode (max_le (max_le bC bz) (max_le bs bt))⟩
  | star _ ihΓ =>
    intro cap hBudget hH
    show BoundedDerivationH cap K _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases ihΓ cap hChildren hH with ⟨dΓ, bΓ⟩
    exact ⟨.star dΓ, max_le hNode bΓ⟩
  | absurd _ _ ihA ihe =>
    intro cap hBudget hH
    show BoundedDerivationH cap K _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases max_le_iff.mp hChildren with ⟨hA, he⟩
    rcases ihA cap hA hH with ⟨dA, bA⟩
    rcases ihe cap he hH with ⟨de, be⟩
    exact ⟨.absurd dA de, max_le hNode (max_le bA be)⟩
  | id _ _ _ ihA iha ihb =>
    intro cap hBudget hH
    show BoundedDerivationH cap K _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases max_le_iff.mp hChildren with ⟨hA, hGroup4R⟩
    rcases max_le_iff.mp hGroup4R with ⟨ha, hb⟩
    rcases ihA cap hA hH with ⟨dA, bA⟩
    rcases iha cap ha hH with ⟨da, ba⟩
    rcases ihb cap hb hH with ⟨db, bb⟩
    exact ⟨.id dA da db, max_le hNode (max_le bA (max_le ba bb))⟩
  | refl _ _ ihA iha =>
    intro cap hBudget hH
    show BoundedDerivationH cap K _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases max_le_iff.mp hChildren with ⟨hA, ha⟩
    rcases ihA cap hA hH with ⟨dA, bA⟩
    rcases iha cap ha hH with ⟨da, ba⟩
    exact ⟨.refl dA da, max_le hNode (max_le bA ba)⟩
  | j _ _ _ _ _ _ ihA iha ihC ihd ihb ihp =>
    intro cap hBudget hH
    show BoundedDerivationH cap K _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases max_le_iff.mp hChildren with ⟨hGroup4L, hGroup4R⟩
    rcases max_le_iff.mp hGroup4L with ⟨hA, ha⟩
    rcases max_le_iff.mp hGroup4R with ⟨hGroup6L, hGroup6R⟩
    rcases max_le_iff.mp hGroup6L with ⟨hC, hd⟩
    rcases max_le_iff.mp hGroup6R with ⟨hb, hp⟩
    rcases ihA cap hA hH with ⟨dA, bA⟩
    rcases iha cap ha hH with ⟨da, ba⟩
    rcases ihC cap hC hH with ⟨dC, bC⟩
    rcases ihd cap hd hH with ⟨dd, bd⟩
    rcases ihb cap hb hH with ⟨db, bb⟩
    rcases ihp cap hp hH with ⟨dp, bp⟩
    exact ⟨.j dA da dC dd db dp, max_le hNode (max_le (max_le bA ba) (max_le (max_le bC bd) (max_le bb bp)))⟩
  | conv _ _ hAB iht ihB =>
    intro cap hBudget hH
    show BoundedDerivationH cap K _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases max_le_iff.mp hChildren with ⟨ht, hGroup4R⟩
    rcases max_le_iff.mp hGroup4R with ⟨hB, hconversion⟩
    rcases iht cap ht hH with ⟨dt, bt⟩
    rcases ihB cap hB hH with ⟨dB, bB⟩
    exact ⟨.conv dt dB hAB, max_le hNode (max_le bt (max_le bB hconversion))⟩
  | cumulative _ hij ihA =>
    intro cap hBudget hH
    show BoundedDerivationH cap K _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases ihA cap hChildren hH with ⟨dA, bA⟩
    exact ⟨.cumulative dA hij, max_le hNode bA⟩

/-- Original bounded proof trees embed without increasing their whole-tree cap. -/
noncomputable def ofOriginalBoundedCore {H : Set ScopedTyping} {n : ℕ} {Γ : Context n} {t A : Term n}
    (d : Derivation Γ t A) : ∀ cap, d.universeBudget ≤ cap → BoundedDerivationH cap H Γ t A := by
  induction d using Derivation.rec
      (motive_1 := fun Γ d => ∀ cap, d.universeBudget ≤ cap →
        {k : ContextDerivationH H Γ // k.universeBudget ≤ cap}) with
  | nil => exact ⟨.nil, Nat.zero_le _⟩
  | snoc _ _ ihΓ ihA cap hBudget =>
    rcases max_le_iff.mp hBudget with ⟨hΓ, hA⟩
    rcases ihΓ cap hΓ with ⟨dΓ, bΓ⟩
    rcases ihA cap hA with ⟨dA, bA⟩
    exact ⟨.snoc dΓ dA, max_le bΓ bA⟩
  | univ _ i ihΓ =>
    intro cap hBudget
    show BoundedDerivationH cap H _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases ihΓ cap hChildren with ⟨dΓ, bΓ⟩
    exact ⟨.univ dΓ i, max_le hNode bΓ⟩
  | nat _ ihΓ =>
    intro cap hBudget
    show BoundedDerivationH cap H _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases ihΓ cap hChildren with ⟨dΓ, bΓ⟩
    exact ⟨.nat dΓ, max_le hNode bΓ⟩
  | empty _ ihΓ =>
    intro cap hBudget
    show BoundedDerivationH cap H _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases ihΓ cap hChildren with ⟨dΓ, bΓ⟩
    exact ⟨.empty dΓ, max_le hNode bΓ⟩
  | unit _ ihΓ =>
    intro cap hBudget
    show BoundedDerivationH cap H _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases ihΓ cap hChildren with ⟨dΓ, bΓ⟩
    exact ⟨.unit dΓ, max_le hNode bΓ⟩
  | var _ hi ihΓ =>
    intro cap hBudget
    show BoundedDerivationH cap H _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases ihΓ cap hChildren with ⟨dΓ, bΓ⟩
    exact ⟨.var dΓ hi, max_le hNode bΓ⟩
  | pi _ _ ihA ihB =>
    intro cap hBudget
    show BoundedDerivationH cap H _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases max_le_iff.mp hChildren with ⟨hA, hB⟩
    rcases ihA cap hA with ⟨dA, bA⟩
    rcases ihB cap hB with ⟨dB, bB⟩
    exact ⟨.pi dA dB, max_le hNode (max_le bA bB)⟩
  | sigma _ _ ihA ihB =>
    intro cap hBudget
    show BoundedDerivationH cap H _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases max_le_iff.mp hChildren with ⟨hA, hB⟩
    rcases ihA cap hA with ⟨dA, bA⟩
    rcases ihB cap hB with ⟨dB, bB⟩
    exact ⟨.sigma dA dB, max_le hNode (max_le bA bB)⟩
  | lam _ _ _ ihA ihB iht =>
    intro cap hBudget
    show BoundedDerivationH cap H _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases max_le_iff.mp hChildren with ⟨hA, hGroup4R⟩
    rcases max_le_iff.mp hGroup4R with ⟨hB, ht⟩
    rcases ihA cap hA with ⟨dA, bA⟩
    rcases ihB cap hB with ⟨dB, bB⟩
    rcases iht cap ht with ⟨dt, bt⟩
    exact ⟨.lam dA dB dt, max_le hNode (max_le bA (max_le bB bt))⟩
  | app _ _ ihf iha =>
    intro cap hBudget
    show BoundedDerivationH cap H _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases max_le_iff.mp hChildren with ⟨hf, ha⟩
    rcases ihf cap hf with ⟨df, bf⟩
    rcases iha cap ha with ⟨da, ba⟩
    exact ⟨.app df da, max_le hNode (max_le bf ba)⟩
  | pair _ _ _ _ ihA ihB iha ihb =>
    intro cap hBudget
    show BoundedDerivationH cap H _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases max_le_iff.mp hChildren with ⟨hGroup4L, hGroup4R⟩
    rcases max_le_iff.mp hGroup4L with ⟨hA, hB⟩
    rcases max_le_iff.mp hGroup4R with ⟨ha, hb⟩
    rcases ihA cap hA with ⟨dA, bA⟩
    rcases ihB cap hB with ⟨dB, bB⟩
    rcases iha cap ha with ⟨da, ba⟩
    rcases ihb cap hb with ⟨db, bb⟩
    exact ⟨.pair dA dB da db, max_le hNode (max_le (max_le bA bB) (max_le ba bb))⟩
  | fst _ ihp =>
    intro cap hBudget
    show BoundedDerivationH cap H _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases ihp cap hChildren with ⟨dp, bp⟩
    exact ⟨.fst dp, max_le hNode bp⟩
  | snd _ ihp =>
    intro cap hBudget
    show BoundedDerivationH cap H _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases ihp cap hChildren with ⟨dp, bp⟩
    exact ⟨.snd dp, max_le hNode bp⟩
  | zero _ ihΓ =>
    intro cap hBudget
    show BoundedDerivationH cap H _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases ihΓ cap hChildren with ⟨dΓ, bΓ⟩
    exact ⟨.zero dΓ, max_le hNode bΓ⟩
  | succ _ iht =>
    intro cap hBudget
    show BoundedDerivationH cap H _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases iht cap hChildren with ⟨dt, bt⟩
    exact ⟨.succ dt, max_le hNode bt⟩
  | natrec _ _ _ _ ihC ihz ihs iht =>
    intro cap hBudget
    show BoundedDerivationH cap H _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases max_le_iff.mp hChildren with ⟨hGroup4L, hGroup4R⟩
    rcases max_le_iff.mp hGroup4L with ⟨hC, hz⟩
    rcases max_le_iff.mp hGroup4R with ⟨hs, ht⟩
    rcases ihC cap hC with ⟨dC, bC⟩
    rcases ihz cap hz with ⟨dz, bz⟩
    rcases ihs cap hs with ⟨ds, bs⟩
    rcases iht cap ht with ⟨dt, bt⟩
    exact ⟨.natrec dC dz ds dt, max_le hNode (max_le (max_le bC bz) (max_le bs bt))⟩
  | star _ ihΓ =>
    intro cap hBudget
    show BoundedDerivationH cap H _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases ihΓ cap hChildren with ⟨dΓ, bΓ⟩
    exact ⟨.star dΓ, max_le hNode bΓ⟩
  | absurd _ _ ihA ihe =>
    intro cap hBudget
    show BoundedDerivationH cap H _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases max_le_iff.mp hChildren with ⟨hA, he⟩
    rcases ihA cap hA with ⟨dA, bA⟩
    rcases ihe cap he with ⟨de, be⟩
    exact ⟨.absurd dA de, max_le hNode (max_le bA be)⟩
  | id _ _ _ ihA iha ihb =>
    intro cap hBudget
    show BoundedDerivationH cap H _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases max_le_iff.mp hChildren with ⟨hA, hGroup4R⟩
    rcases max_le_iff.mp hGroup4R with ⟨ha, hb⟩
    rcases ihA cap hA with ⟨dA, bA⟩
    rcases iha cap ha with ⟨da, ba⟩
    rcases ihb cap hb with ⟨db, bb⟩
    exact ⟨.id dA da db, max_le hNode (max_le bA (max_le ba bb))⟩
  | refl _ _ ihA iha =>
    intro cap hBudget
    show BoundedDerivationH cap H _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases max_le_iff.mp hChildren with ⟨hA, ha⟩
    rcases ihA cap hA with ⟨dA, bA⟩
    rcases iha cap ha with ⟨da, ba⟩
    exact ⟨.refl dA da, max_le hNode (max_le bA ba)⟩
  | j _ _ _ _ _ _ ihA iha ihC ihd ihb ihp =>
    intro cap hBudget
    show BoundedDerivationH cap H _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases max_le_iff.mp hChildren with ⟨hGroup4L, hGroup4R⟩
    rcases max_le_iff.mp hGroup4L with ⟨hA, ha⟩
    rcases max_le_iff.mp hGroup4R with ⟨hGroup6L, hGroup6R⟩
    rcases max_le_iff.mp hGroup6L with ⟨hC, hd⟩
    rcases max_le_iff.mp hGroup6R with ⟨hb, hp⟩
    rcases ihA cap hA with ⟨dA, bA⟩
    rcases iha cap ha with ⟨da, ba⟩
    rcases ihC cap hC with ⟨dC, bC⟩
    rcases ihd cap hd with ⟨dd, bd⟩
    rcases ihb cap hb with ⟨db, bb⟩
    rcases ihp cap hp with ⟨dp, bp⟩
    exact ⟨.j dA da dC dd db dp, max_le hNode (max_le (max_le bA ba) (max_le (max_le bC bd) (max_le bb bp)))⟩
  | conv _ _ hAB iht ihB =>
    intro cap hBudget
    show BoundedDerivationH cap H _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases max_le_iff.mp hChildren with ⟨ht, hGroup4R⟩
    rcases max_le_iff.mp hGroup4R with ⟨hB, hconversion⟩
    rcases iht cap ht with ⟨dt, bt⟩
    rcases ihB cap hB with ⟨dB, bB⟩
    exact ⟨.conv dt dB hAB, max_le hNode (max_le bt (max_le bB hconversion))⟩
  | cumulative _ hij ihA =>
    intro cap hBudget
    show BoundedDerivationH cap H _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases ihA cap hChildren with ⟨dA, bA⟩
    exact ⟨.cumulative dA hij, max_le hNode bA⟩

/-- Empty-hypothesis bounded trees recover actual original bounded proof data. -/
noncomputable def toOriginalBoundedCore {n : ℕ} {Γ : Context n} {t A : Term n}
    (d : DerivationH ∅ Γ t A) : ∀ cap, d.universeBudget ≤ cap → BoundedDerivation cap Γ t A := by
  induction d using DerivationH.rec
      (motive_1 := fun Γ d => ∀ cap, d.universeBudget ≤ cap →
        {k : ContextDerivation Γ // k.universeBudget ≤ cap}) with
  | nil => exact ⟨.nil, Nat.zero_le _⟩
  | snoc _ _ ihΓ ihA cap hBudget =>
    rcases max_le_iff.mp hBudget with ⟨hΓ, hA⟩
    rcases ihΓ cap hΓ with ⟨dΓ, bΓ⟩
    rcases ihA cap hA with ⟨dA, bA⟩
    exact ⟨.snoc dΓ dA, max_le bΓ bA⟩
  | hyp hq => exact False.elim hq
  | univ _ i ihΓ =>
    intro cap hBudget
    show BoundedDerivation cap _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases ihΓ cap hChildren with ⟨dΓ, bΓ⟩
    exact ⟨.univ dΓ i, max_le hNode bΓ⟩
  | nat _ ihΓ =>
    intro cap hBudget
    show BoundedDerivation cap _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases ihΓ cap hChildren with ⟨dΓ, bΓ⟩
    exact ⟨.nat dΓ, max_le hNode bΓ⟩
  | empty _ ihΓ =>
    intro cap hBudget
    show BoundedDerivation cap _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases ihΓ cap hChildren with ⟨dΓ, bΓ⟩
    exact ⟨.empty dΓ, max_le hNode bΓ⟩
  | unit _ ihΓ =>
    intro cap hBudget
    show BoundedDerivation cap _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases ihΓ cap hChildren with ⟨dΓ, bΓ⟩
    exact ⟨.unit dΓ, max_le hNode bΓ⟩
  | var _ hi ihΓ =>
    intro cap hBudget
    show BoundedDerivation cap _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases ihΓ cap hChildren with ⟨dΓ, bΓ⟩
    exact ⟨.var dΓ hi, max_le hNode bΓ⟩
  | pi _ _ ihA ihB =>
    intro cap hBudget
    show BoundedDerivation cap _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases max_le_iff.mp hChildren with ⟨hA, hB⟩
    rcases ihA cap hA with ⟨dA, bA⟩
    rcases ihB cap hB with ⟨dB, bB⟩
    exact ⟨.pi dA dB, max_le hNode (max_le bA bB)⟩
  | sigma _ _ ihA ihB =>
    intro cap hBudget
    show BoundedDerivation cap _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases max_le_iff.mp hChildren with ⟨hA, hB⟩
    rcases ihA cap hA with ⟨dA, bA⟩
    rcases ihB cap hB with ⟨dB, bB⟩
    exact ⟨.sigma dA dB, max_le hNode (max_le bA bB)⟩
  | lam _ _ _ ihA ihB iht =>
    intro cap hBudget
    show BoundedDerivation cap _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases max_le_iff.mp hChildren with ⟨hA, hGroup4R⟩
    rcases max_le_iff.mp hGroup4R with ⟨hB, ht⟩
    rcases ihA cap hA with ⟨dA, bA⟩
    rcases ihB cap hB with ⟨dB, bB⟩
    rcases iht cap ht with ⟨dt, bt⟩
    exact ⟨.lam dA dB dt, max_le hNode (max_le bA (max_le bB bt))⟩
  | app _ _ ihf iha =>
    intro cap hBudget
    show BoundedDerivation cap _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases max_le_iff.mp hChildren with ⟨hf, ha⟩
    rcases ihf cap hf with ⟨df, bf⟩
    rcases iha cap ha with ⟨da, ba⟩
    exact ⟨.app df da, max_le hNode (max_le bf ba)⟩
  | pair _ _ _ _ ihA ihB iha ihb =>
    intro cap hBudget
    show BoundedDerivation cap _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases max_le_iff.mp hChildren with ⟨hGroup4L, hGroup4R⟩
    rcases max_le_iff.mp hGroup4L with ⟨hA, hB⟩
    rcases max_le_iff.mp hGroup4R with ⟨ha, hb⟩
    rcases ihA cap hA with ⟨dA, bA⟩
    rcases ihB cap hB with ⟨dB, bB⟩
    rcases iha cap ha with ⟨da, ba⟩
    rcases ihb cap hb with ⟨db, bb⟩
    exact ⟨.pair dA dB da db, max_le hNode (max_le (max_le bA bB) (max_le ba bb))⟩
  | fst _ ihp =>
    intro cap hBudget
    show BoundedDerivation cap _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases ihp cap hChildren with ⟨dp, bp⟩
    exact ⟨.fst dp, max_le hNode bp⟩
  | snd _ ihp =>
    intro cap hBudget
    show BoundedDerivation cap _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases ihp cap hChildren with ⟨dp, bp⟩
    exact ⟨.snd dp, max_le hNode bp⟩
  | zero _ ihΓ =>
    intro cap hBudget
    show BoundedDerivation cap _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases ihΓ cap hChildren with ⟨dΓ, bΓ⟩
    exact ⟨.zero dΓ, max_le hNode bΓ⟩
  | succ _ iht =>
    intro cap hBudget
    show BoundedDerivation cap _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases iht cap hChildren with ⟨dt, bt⟩
    exact ⟨.succ dt, max_le hNode bt⟩
  | natrec _ _ _ _ ihC ihz ihs iht =>
    intro cap hBudget
    show BoundedDerivation cap _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases max_le_iff.mp hChildren with ⟨hGroup4L, hGroup4R⟩
    rcases max_le_iff.mp hGroup4L with ⟨hC, hz⟩
    rcases max_le_iff.mp hGroup4R with ⟨hs, ht⟩
    rcases ihC cap hC with ⟨dC, bC⟩
    rcases ihz cap hz with ⟨dz, bz⟩
    rcases ihs cap hs with ⟨ds, bs⟩
    rcases iht cap ht with ⟨dt, bt⟩
    exact ⟨.natrec dC dz ds dt, max_le hNode (max_le (max_le bC bz) (max_le bs bt))⟩
  | star _ ihΓ =>
    intro cap hBudget
    show BoundedDerivation cap _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases ihΓ cap hChildren with ⟨dΓ, bΓ⟩
    exact ⟨.star dΓ, max_le hNode bΓ⟩
  | absurd _ _ ihA ihe =>
    intro cap hBudget
    show BoundedDerivation cap _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases max_le_iff.mp hChildren with ⟨hA, he⟩
    rcases ihA cap hA with ⟨dA, bA⟩
    rcases ihe cap he with ⟨de, be⟩
    exact ⟨.absurd dA de, max_le hNode (max_le bA be)⟩
  | id _ _ _ ihA iha ihb =>
    intro cap hBudget
    show BoundedDerivation cap _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases max_le_iff.mp hChildren with ⟨hA, hGroup4R⟩
    rcases max_le_iff.mp hGroup4R with ⟨ha, hb⟩
    rcases ihA cap hA with ⟨dA, bA⟩
    rcases iha cap ha with ⟨da, ba⟩
    rcases ihb cap hb with ⟨db, bb⟩
    exact ⟨.id dA da db, max_le hNode (max_le bA (max_le ba bb))⟩
  | refl _ _ ihA iha =>
    intro cap hBudget
    show BoundedDerivation cap _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases max_le_iff.mp hChildren with ⟨hA, ha⟩
    rcases ihA cap hA with ⟨dA, bA⟩
    rcases iha cap ha with ⟨da, ba⟩
    exact ⟨.refl dA da, max_le hNode (max_le bA ba)⟩
  | j _ _ _ _ _ _ ihA iha ihC ihd ihb ihp =>
    intro cap hBudget
    show BoundedDerivation cap _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases max_le_iff.mp hChildren with ⟨hGroup4L, hGroup4R⟩
    rcases max_le_iff.mp hGroup4L with ⟨hA, ha⟩
    rcases max_le_iff.mp hGroup4R with ⟨hGroup6L, hGroup6R⟩
    rcases max_le_iff.mp hGroup6L with ⟨hC, hd⟩
    rcases max_le_iff.mp hGroup6R with ⟨hb, hp⟩
    rcases ihA cap hA with ⟨dA, bA⟩
    rcases iha cap ha with ⟨da, ba⟩
    rcases ihC cap hC with ⟨dC, bC⟩
    rcases ihd cap hd with ⟨dd, bd⟩
    rcases ihb cap hb with ⟨db, bb⟩
    rcases ihp cap hp with ⟨dp, bp⟩
    exact ⟨.j dA da dC dd db dp, max_le hNode (max_le (max_le bA ba) (max_le (max_le bC bd) (max_le bb bp)))⟩
  | conv _ _ hAB iht ihB =>
    intro cap hBudget
    show BoundedDerivation cap _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases max_le_iff.mp hChildren with ⟨ht, hGroup4R⟩
    rcases max_le_iff.mp hGroup4R with ⟨hB, hconversion⟩
    rcases iht cap ht with ⟨dt, bt⟩
    rcases ihB cap hB with ⟨dB, bB⟩
    exact ⟨.conv dt dB hAB, max_le hNode (max_le bt (max_le bB hconversion))⟩
  | cumulative _ hij ihA =>
    intro cap hBudget
    show BoundedDerivation cap _ _ _
    rcases max_le_iff.mp hBudget with ⟨hNode, hChildren⟩
    rcases ihA cap hChildren with ⟨dA, bA⟩
    exact ⟨.cumulative dA hij, max_le hNode bA⟩

/-- Every original proof embeds rule for rule, independently of the chosen hypotheses. -/
noncomputable def ofOriginal {H : Set ScopedTyping} {n : ℕ} {Γ : Context n} {t A : Term n}
    (d : Derivation Γ t A) : DerivationH H Γ t A := by
  induction d using Derivation.rec (motive_1 := fun Γ _ => ContextDerivationH H Γ) with
  | nil => exact .nil
  | snoc _ _ ihΓ ihA => exact .snoc ihΓ ihA
  | univ _ i ihΓ => exact .univ ihΓ i
  | nat _ ihΓ => exact .nat ihΓ
  | empty _ ihΓ => exact .empty ihΓ
  | unit _ ihΓ => exact .unit ihΓ
  | var _ hi ihΓ => exact .var ihΓ hi
  | pi _ _ ihA ihB => exact .pi ihA ihB
  | sigma _ _ ihA ihB => exact .sigma ihA ihB
  | lam _ _ _ ihA ihB iht => exact .lam ihA ihB iht
  | app _ _ ihf iha => exact .app ihf iha
  | pair _ _ _ _ ihA ihB iha ihb => exact .pair ihA ihB iha ihb
  | fst _ ihp => exact .fst ihp
  | snd _ ihp => exact .snd ihp
  | zero _ ihΓ => exact .zero ihΓ
  | succ _ iht => exact .succ iht
  | natrec _ _ _ _ ihC ihz ihs iht => exact .natrec ihC ihz ihs iht
  | star _ ihΓ => exact .star ihΓ
  | absurd _ _ ihA ihe => exact .absurd ihA ihe
  | id _ _ _ ihA iha ihb => exact .id ihA iha ihb
  | refl _ _ ihA iha => exact .refl ihA iha
  | j _ _ _ _ _ _ ihA iha ihC ihd ihb ihp => exact .j ihA iha ihC ihd ihb ihp
  | conv _ _ hAB iht ihB => exact .conv iht ihB hAB
  | cumulative _ hij ihA => exact .cumulative ihA hij

/-- Actual original derivations interpreting the hypotheses recover an original derivation. -/
noncomputable def toOriginal {H : Set ScopedTyping} {n : ℕ} {Γ : Context n} {t A : Term n}
    (d : DerivationH H Γ t A)
    (hH : ∀ q ∈ H, Derivation q.Γ q.term q.carrier) : Derivation Γ t A := by
  induction d using DerivationH.rec (motive_1 := fun Γ _ => ContextDerivation Γ) with
  | hyp hq => exact hH _ hq
  | nil => exact .nil
  | snoc _ _ ihΓ ihA => exact .snoc ihΓ ihA
  | univ _ i ihΓ => exact .univ ihΓ i
  | nat _ ihΓ => exact .nat ihΓ
  | empty _ ihΓ => exact .empty ihΓ
  | unit _ ihΓ => exact .unit ihΓ
  | var _ hi ihΓ => exact .var ihΓ hi
  | pi _ _ ihA ihB => exact .pi ihA ihB
  | sigma _ _ ihA ihB => exact .sigma ihA ihB
  | lam _ _ _ ihA ihB iht => exact .lam ihA ihB iht
  | app _ _ ihf iha => exact .app ihf iha
  | pair _ _ _ _ ihA ihB iha ihb => exact .pair ihA ihB iha ihb
  | fst _ ihp => exact .fst ihp
  | snd _ ihp => exact .snd ihp
  | zero _ ihΓ => exact .zero ihΓ
  | succ _ iht => exact .succ iht
  | natrec _ _ _ _ ihC ihz ihs iht => exact .natrec ihC ihz ihs iht
  | star _ ihΓ => exact .star ihΓ
  | absurd _ _ ihA ihe => exact .absurd ihA ihe
  | id _ _ _ ihA iha ihb => exact .id ihA iha ihb
  | refl _ _ ihA iha => exact .refl ihA iha
  | j _ _ _ _ _ _ ihA iha ihC ihd ihb ihp => exact .j ihA iha ihC ihd ihb ihp
  | conv _ _ hAB iht ihB => exact .conv iht ihB hAB
  | cumulative _ hij ihA => exact .cumulative ihA hij

theorem realizes {H : Set ScopedTyping} {n : ℕ} {Γ : Context n} {t A : Term n} (d : DerivationH H Γ t A)
    (hH : ∀ q ∈ H, Valid q.Γ q.term q.carrier) :
    Valid Γ t A := by
  induction d using DerivationH.rec (motive_1 := fun _ _ => True) with
  | hyp hq => exact hH _ hq
  | nil => trivial
  | snoc _ _ _ _ => trivial
  | univ _ i _ =>
    intro ρ _
    exact realizes_univ_iff.mpr ⟨{q | ∃ X, Code i q X}, Code.univ (Nat.lt_succ_self i)⟩
  | nat _ _ =>
    intro ρ _
    exact realizes_univ_iff.mpr ⟨Naturals, Code.nat 0⟩
  | empty _ _ =>
    intro ρ _
    exact realizes_univ_iff.mpr ⟨∅, Code.empty 0⟩
  | unit _ _ =>
    intro ρ _
    exact realizes_univ_iff.mpr ⟨Units, Code.unit 0⟩
  | var _ hi _ => exact lookup hi
  | pi _ _ ihA ihB => exact valid_pi ihA ihB
  | sigma _ _ ihA ihB => exact valid_sigma ihA ihB
  | lam _ _ _ ihA ihB iht => exact valid_lam ihA ihB iht
  | app _ _ ihf iha => exact fun ρ hρ => realizes_app (ihf ρ hρ) (iha ρ hρ)
  | pair _ _ _ _ ihA ihB iha ihb => exact valid_pair ihA ihB iha ihb
  | fst _ ihp => exact valid_fst ihp
  | snd _ ihp => exact valid_snd ihp
  | zero _ _ => exact fun _ _ => ⟨0, Naturals, Code.nat 0, 0, rfl⟩
  | succ _ iht => exact valid_succ iht
  | natrec _ _ _ _ _ ihz ihs iht => exact valid_natrec ihz ihs iht
  | star _ _ => exact fun _ _ => ⟨0, Units, Code.unit 0, rfl⟩
  | absurd _ _ _ ihe =>
    intro ρ hρ
    rcases ihe ρ hρ with ⟨i, X, hX, he⟩
    exact False.elim (hX.no_empty_realizer _ he)
  | id _ _ _ ihA iha ihb => exact valid_id ihA iha ihb
  | refl _ _ ihA iha => exact valid_refl ihA iha
  | j _ _ _ _ _ _ _ _ _ ihd _ ihp => exact valid_j ihd ihp
  | conv _ _ hAB iht _ => exact valid_conv iht hAB
  | cumulative _ hij ihA => exact valid_cumulative ihA hij

end Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.OriginalHypotheses
