module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Defs

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native

open Morphism.CaseSSA (erase ofScoped erase_ofScoped ofScoped_hasType_iff)
open LetCase.LocallyNameless (Derivation)

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

set_option backward.isDefEq.respectTransparency false

private theorem operand {n : Nat} {β : BoundCtx τ n} {a : Tm Φ} {A : τ}
    (h : Tm.HasType β.toList a A) : Nonempty {d : Operand Φ β A // erase d.1 = a} := by
  have inScope : a.Scoped n := by simpa using h.scoped
  obtain ⟨d⟩ := Derivation.ofHasType ((ofScoped_hasType_iff (Γ := .nil) inScope).mpr h)
  exact ⟨⟨⟨_, d⟩, erase_ofScoped _ _⟩⟩

theorem recognize_proof {n : Nat} {β : BoundCtx τ n} {r : Region Φ} {L : LCtx τ} {exit : Nat}
    (shape : Outward exit r) (typed : Region.HasType β.toList r L) {A : τ}
    (destination : At L exit A) : Nonempty {c : Code Φ β A // c.toSSA exit = r} := by
  induction shape generalizing n L A with
  | br arg =>
    cases typed with
    | br label ha =>
      obtain rfl := Option.some.inj (destination.symm.trans label)
      obtain ⟨⟨a, e⟩⟩ := operand ha
      exact ⟨⟨.br a, congrArg _ e⟩⟩
  | let₁ arg _ ih =>
    cases typed with
    | @let₁ _ _ _ _ X ha hr =>
      obtain ⟨⟨a, ea⟩⟩ := operand ha
      obtain ⟨⟨r, er⟩⟩ := ih (β := β.snoc X) hr destination
      exact ⟨⟨.let₁ a r, congrArg₂ Region.let₁ ea er⟩⟩
  | let₂ arg _ ih =>
    cases typed with
    | @let₂ _ _ _ _ X Y ha hr =>
      obtain ⟨⟨a, ea⟩⟩ := operand ha
      obtain ⟨⟨r, er⟩⟩ := ih (β := (β.snoc X).snoc Y) hr destination
      exact ⟨⟨.let₂ a r, congrArg₂ Region.let₂ ea er⟩⟩
  | case arg _ _ il ir =>
    cases typed with
    | @case _ _ _ _ _ X Y ha hl hr =>
      obtain ⟨⟨a, ea⟩⟩ := operand ha
      obtain ⟨⟨l, el⟩⟩ := il (β := β.snoc X) hl destination
      obtain ⟨⟨r, er⟩⟩ := ir (β := β.snoc Y) hr destination
      exact ⟨⟨.case a l r, by simp only [Code.toSSA, ea, el, er]⟩⟩
  | @join exit entry blocks _ _ ie ib =>
    cases typed with
    | cfg R he hb =>
      have here : At (List.ofFn R ++ L) 0 (R 0) := by simp [At, List.ofFn_succ]
      have there : At (List.ofFn R ++ L) (exit + 1) A := by
        simpa [At, List.ofFn_succ] using destination
      obtain ⟨⟨e, ee⟩⟩ := ie he here
      obtain ⟨⟨b, eb⟩⟩ := ib (β := β.snoc (R 0)) (hb 0) there
      refine ⟨⟨.join e b, ?_⟩⟩
      simp only [Code.toSSA, ee]
      congr 1
      funext i
      rw [show i = 0 from Subsingleton.elim _ _, eb]

end Silmaril.Isotope.LambdaSSA.Acyclic.Native
