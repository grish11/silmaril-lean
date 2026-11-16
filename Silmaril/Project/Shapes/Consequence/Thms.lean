module

public import Silmaril.Project.Shapes.Consequence.Defs
public import Silmaril.Logic.Consequence.Thms

/-!
# Standard problem shapes: consequence systems, what each status means

For an instance that leaves exactly the listed binders free, in order, the SZS statuses are
the statements below (each left-hand side is the shape of `@[answers … s]` for that status, so
an answer of status `s` *is* a proof of the right-hand side, and conversely), in the terms of
the core API `Silmaril.Consequence` (`Silmaril.Logic.Consequence.Defs`). `⊤` is the universal
system and `⊥` the empty one.

* `derives S` (over `Γ φ`): `thm` ↔ `S.Universal` ↔ `S = ⊤`, `sat` ↔ `S ≠ ⊥`, `uns` ↔ `S = ⊥`,
  `csa` ↔ `S ≠ ⊤`;
* `derives S Γ` (over `φ`): `thm` ↔ `S.ProvesAll Γ`, `csa` ↔ `S.ContextConsistent Γ`;
* `context_universal S` (over `Γ`): `thm` ↔ `S.Universal`; with `Γ` fixed it is `S.ProvesAll Γ`;
* `derives_bottom S ff` (over `Γ`): `thm` ↔ every context `S.ProvesFalse ff`, `uns` ↔ every
  context is `S.ConsistentWrt ff`;
* `sound_at S T`: `thm` ↔ `S.Sound T`, `csa` ↔ `¬ S.Sound T`; `complete_at S T`: `thm` ↔
  `S.Complete T`, `csa` ↔ `¬ S.Complete T`;
* `complete_within_at S T μ b`: `thm` ↔ completeness on the pairs with `μ Γ φ ≤ b`, `csa` ↔ a
  counterexample within the bound;
* `gentzen_closed rs S` (closed): `thm` ↔ `Gentzen.Closed rs S`;
* `translates_at S T f g`: `thm` ↔ `S ≤ T.pullback f g`; `reflects_at`: `T.pullback f g ≤ S`.

Nothing is assumed inhabited: over an empty type of contexts `derives S` is THM and UNS at once
(`derives_thm_and_uns_of_isEmpty`). And the three properties that are sometimes all called
"inconsistency" differ (`derivesBottom_not_contextUniversal`,
`contextUniversal_not_universal`).
-/

@[expose] public section

namespace Silmaril.Project.Shapes.Consequence

open Silmaril.Consequence (System)

variable {Ax C Bx D : Type} {S T : System Ax C} {f : Ax → Bx} {g : C → D}

theorem derives_thm_iff_universal : (∀ Γ φ, Derives S Γ φ) ↔ S.Universal := Iff.rfl

theorem derives_thm_iff : (∀ Γ φ, Derives S Γ φ) ↔ S = ⊤ := System.universal_iff_eq_top

theorem derives_uns_iff : (∀ Γ φ, ¬ Derives S Γ φ) ↔ S = ⊥ :=
  ⟨fun h => funext fun Γ => funext fun φ => eq_false (h Γ φ), fun h _ _ => h ▸ id⟩

theorem derives_sat_iff : (∃ Γ φ, Derives S Γ φ) ↔ S ≠ ⊥ := by
  rw [Ne, ← derives_uns_iff]; simp only [not_forall, not_not]

theorem derives_csa_iff : (∃ Γ φ, ¬ Derives S Γ φ) ↔ S ≠ ⊤ := by
  rw [Ne, ← derives_thm_iff]; simp only [not_forall]

theorem contextUniversal_iff {Γ : Ax} : ContextUniversal S Γ ↔ S.ProvesAll Γ := Iff.rfl

theorem derives_ctx_thm_iff {Γ : Ax} : (∀ φ, Derives S Γ φ) ↔ S.ProvesAll Γ := Iff.rfl

theorem derives_ctx_csa_iff {Γ : Ax} : (∃ φ, ¬ Derives S Γ φ) ↔ S.ContextConsistent Γ :=
  (System.contextConsistent_iff Γ).symm

theorem contextUniversal_thm_iff : (∀ Γ, ContextUniversal S Γ) ↔ S.Universal := Iff.rfl

theorem derivesBottom_iff {ff : C} {Γ : Ax} : DerivesBottom S ff Γ ↔ S.ProvesFalse ff Γ := Iff.rfl

theorem derivesBottom_uns_iff {ff : C} :
    (∀ Γ, ¬ DerivesBottom S ff Γ) ↔ ∀ Γ, S.ConsistentWrt ff Γ := Iff.rfl

theorem soundAt_thm_iff : (∀ Γ φ, SoundAt S T Γ φ) ↔ S.Sound T := Iff.rfl

theorem soundAt_csa_iff : (∃ Γ φ, ¬ SoundAt S T Γ φ) ↔ ¬ S.Sound T := by
  rw [← soundAt_thm_iff]; simp only [not_forall]

theorem completeAt_thm_iff : (∀ Γ φ, CompleteAt S T Γ φ) ↔ S.Complete T := Iff.rfl

theorem completeAt_csa_iff : (∃ Γ φ, ¬ CompleteAt S T Γ φ) ↔ ¬ S.Complete T := by
  rw [← completeAt_thm_iff]; simp only [not_forall]

theorem completeWithinAt_thm_iff {μ : Ax → C → ℕ} {b : ℕ} :
    (∀ Γ φ, CompleteWithinAt S T μ b Γ φ) ↔ ∀ Γ φ, μ Γ φ ≤ b → T Γ φ → S Γ φ := Iff.rfl

theorem completeWithinAt_csa_iff {μ : Ax → C → ℕ} {b : ℕ} :
    (∃ Γ φ, ¬ CompleteWithinAt S T μ b Γ φ) ↔ ∃ Γ φ, μ Γ φ ≤ b ∧ T Γ φ ∧ ¬ S Γ φ := by
  simp only [CompleteWithinAt, Classical.not_imp]

theorem gentzenClosed_iff {C : Type} {rs : Silmaril.Consequence.Gentzen.Rules C}
    {S : Silmaril.Consequence.Gentzen.Seq C} : GentzenClosed rs S ↔ Silmaril.Consequence.Gentzen.Closed rs S :=
  Iff.rfl

theorem translatesAt_thm_iff {U : System Bx D} :
    (∀ Γ φ, TranslatesAt S U f g Γ φ) ↔ S ≤ U.pullback f g := Iff.rfl

theorem reflectsAt_thm_iff {U : System Bx D} :
    (∀ Γ φ, ReflectsAt S U f g Γ φ) ↔ U.pullback f g ≤ S := Iff.rfl

/-- Over an empty type of contexts, `derives S` is THM and UNS at once: the readings quantify
over the binders that remain, and nothing is assumed inhabited. -/
theorem derives_thm_and_uns_of_isEmpty [IsEmpty Ax] :
    (∀ Γ φ, Derives S Γ φ) ∧ (∀ Γ φ, ¬ Derives S Γ φ) :=
  ⟨fun Γ => isEmptyElim Γ, fun Γ => isEmptyElim Γ⟩

/-- Deriving a chosen `ff` is not context-universality: `() ⊢ false` holds but `() ⊢ true`
does not, in the system `Γ ⊢ φ ↔ φ = false`. -/
theorem derivesBottom_not_contextUniversal :
    DerivesBottom (fun (_ : Unit) (φ : Bool) => φ = false) false () ∧
      ¬ ContextUniversal (fun (_ : Unit) (φ : Bool) => φ = false) () :=
  ⟨rfl, fun h => Bool.noConfusion (h true)⟩

/-- Context-universality is not universality: the context `true` derives everything and the
context `false` derives nothing, in the system `Γ ⊢ φ ↔ Γ = true`. -/
theorem contextUniversal_not_universal :
    ContextUniversal (fun (Γ : Bool) (_ : Unit) => Γ = true) true ∧
      ¬ ∀ Γ φ, Derives (fun (Γ : Bool) (_ : Unit) => Γ = true) Γ φ :=
  ⟨fun _ => rfl, fun h => Bool.noConfusion (h false ())⟩

end Silmaril.Project.Shapes.Consequence
