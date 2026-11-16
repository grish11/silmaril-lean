module

public import Silmaril.Logic.Reachability.Derivation.FirstOrder.Calculus.Defs

@[expose] public section
namespace Silmaril.Logic.Reachability.Derivation.FirstOrder
open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.FirstOrder.Variables
variable {Sg : FOL.Signature} {cfg : Sg.S} {k : Nat} {Γ : Fin k → Sg.S}
variable (M : FOL.Structure Sg)

theorem Pattern.holds_disj (p q : Pattern Sg cfg Γ) (e : Embedding Γ)
    (a : StockAssignment M) (w : M.carrier cfg) :
    Pattern.holds (p.disj q) M e a w ↔
      Pattern.holds p M e a w ∨ Pattern.holds q M e a w := by
  classical
  simp only [Pattern.disj, Pattern.holds, FOL.Formula.Holds, not_and_or, not_not]

theorem Claim.interpret_weakenBlock (e : Embedding Γ) (xs : List Sg.S)
    (c : Claim Sg cfg Γ) :
    (c.weakenBlock xs).interpret M (e.extendBlock xs) = c.interpret M e := by
  cases c with
  | mk pre post =>
    apply congrArg₂ Derivation.Claim.mk
    · funext a w
      exact propext (Pattern.holds_weakenBlock pre M e a w xs)
    · funext a w
      exact propext (Pattern.holds_weakenBlock post M e a w xs)

theorem environment_weakenBlock (e : Embedding Γ) (xs : List Sg.S)
    (E : Set (Claim Sg cfg Γ)) :
    environment M (e.extendBlock xs) (weakenEnvironment xs E) = environment M e E := by
  simp only [environment, weakenEnvironment, Set.image_image,
    Claim.interpret_weakenBlock]

/-- Every source constructor maps to the existing full semantic calculus.
The abstraction case invokes actual block rebinding and proved independence;
there is no assumed adequacy/reification equality or nonempty-sort hypothesis. -/
noncomputable def Derives.interpret {ι : Type}
    {rules : ι → RuleSystem.Scheme (M.carrier cfg)}
    {E C : Set (Claim Sg cfg Γ)} {c : Claim Sg cfg Γ}
    (d : Derives M rules E C c) : ∀ e : Embedding Γ,
    Derivation.Derives rules (environment M e E) (environment M e C) (c.interpret M e) := by
  induction d with
  | step cover successors =>
    intro e
    exact .step (fun a => cover (e.assignment M a))
      (fun a => successors (e.assignment M a))
  | useAxiom member =>
    intro e
    exact .useAxiom ⟨_, member, rfl⟩
  | reflexivity =>
    intro e
    simpa only [environment, Claim.interpret, Set.image_empty] using
      (Derivation.Derives.reflexivity (rules := rules)
        (A := environment M e _) (P := fun a w => Pattern.holds _ M e a w))
  | transitivity first second ihFirst ihSecond =>
    intro e
    apply Derivation.Derives.transitivity (ihFirst e)
    simpa only [environment, Claim.interpret, Set.image_union, Set.image_empty] using ihSecond e
  | cases left right ihLeft ihRight =>
    intro e
    apply Derivation.Derives.consequence
      (P₀ := fun a w => Pattern.holds _ M e a w ∨ Pattern.holds _ M e a w)
    · intro a w h
      exact (Pattern.holds_disj M _ _ e a w).mp h
    · exact .cases (ihLeft e) (ihRight e)
    · exact fun _ _ h => h
  | @abstraction k Γ E C xs P Q inner ih =>
    intro e
    have child := ih (e.extendBlock xs)
    rw [environment_weakenBlock, environment_weakenBlock] at child
    have normalized : Derivation.Derives rules (environment M e E) (environment M e C)
        ⟨(fun a w => Pattern.holds P M (e.extendBlock xs) a w),
          (fun a w => Pattern.holds Q M e a w)⟩ := by
      apply Derivation.Derives.consequence (fun _ _ h => h) child
      intro a w h
      exact (Pattern.holds_weakenBlock Q M e a w xs).mp h
    apply Derivation.Derives.consequence
      (P₀ := Derivation.Abstract (↑(e.freshNames xs) : Set (StockName Sg))
        (fun a w => Pattern.holds P M (e.extendBlock xs) a w))
    · intro a w h
      exact (Pattern.existsBlock_iff_abstract M e xs P a w).mp h
    · exact .abstraction _ normalized (Pattern.independent_freshNames Q M e xs)
    · exact fun _ _ h => h
  | consequence pre inner post ih =>
    intro e
    exact .consequence (fun a w h => pre (e.assignment M a) w h) (ih e)
      (fun a w h => post (e.assignment M a) w h)
  | circularity inner ih =>
    intro e
    apply Derivation.Derives.circularity
    simpa only [environment, Claim.interpret, Set.image_union, Set.image_singleton] using ih e

end Silmaril.Logic.Reachability.Derivation.FirstOrder
