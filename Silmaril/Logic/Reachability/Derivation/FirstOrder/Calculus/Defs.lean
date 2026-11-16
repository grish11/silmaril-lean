module

public import Silmaril.Logic.Reachability.Derivation.FirstOrder.Stock.Rebinding.Thms

@[expose] public section
namespace Silmaril.Logic.Reachability.Derivation.FirstOrder
open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.FirstOrder.Variables
variable {Sg : FOL.Signature} {cfg : Sg.S} {k : Nat} {Γ : Fin k → Sg.S}

/-- Actual Boolean source disjunction, rather than a semantic predicate symbol. -/
def Pattern.disj (p q : Pattern Sg cfg Γ) : Pattern Sg cfg Γ := .not (.and (.not p) (.not q))

def Claim.weakenBlock (xs : List Sg.S) (c : Claim Sg cfg Γ) :
    Claim Sg cfg (blockContext Γ xs) :=
  ⟨Silmaril.Logic.FirstOrder.Variables.weakenBlock cfg Γ xs c.pre, Silmaril.Logic.FirstOrder.Variables.weakenBlock cfg Γ xs c.post⟩

def weakenEnvironment (xs : List Sg.S) (E : Set (Claim Sg cfg Γ)) :=
  Claim.weakenBlock xs '' E

def Pattern.localHolds (p : Pattern Sg cfg Γ) (M : FOL.Structure Sg)
    (a : (i : Fin k) → M.carrier (Γ i)) (w : M.carrier cfg) : Prop :=
  FOL.Formula.Holds M p (consAssignment M cfg Γ w a)

def Pattern.entails (M : FOL.Structure Sg) (p q : Pattern Sg cfg Γ) : Prop :=
  ∀ a w, Pattern.localHolds p M a w → Pattern.localHolds q M a w

/-- Full eight-rule FOL syntax with finite-context fresh-block Abstraction.
Only the newly introduced source block is discharged; environments and target
are actual weakenings. This does not assert arbitrary named-environment erasure. -/
inductive Derives (M : FOL.Structure Sg) {ι : Type}
    (rules : ι → RuleSystem.Scheme (M.carrier cfg)) :
    {k : Nat} → {Γ : Fin k → Sg.S} →
    Set (Claim Sg cfg Γ) → Set (Claim Sg cfg Γ) → Claim Sg cfg Γ → Type where
  | step {k Γ E C P Q}
      (cover : ∀ a, RuleSystem.Covers rules (fun w => Pattern.localHolds P M a w))
      (successors : ∀ a, RuleSystem.SuccessorsIn rules
        (fun w => Pattern.localHolds P M a w) (fun w => Pattern.localHolds Q M a w)) :
      Derives M rules (k := k) (Γ := Γ) E C ⟨P, Q⟩
  | useAxiom {k Γ E C c} : c ∈ E → Derives M rules (k := k) (Γ := Γ) E C c
  | reflexivity {k Γ E P} : Derives M rules (k := k) (Γ := Γ) E ∅ ⟨P, P⟩
  | transitivity {k Γ E C P B Q} :
      Derives M rules (k := k) (Γ := Γ) E C ⟨P, B⟩ →
      Derives M rules (E ∪ C) ∅ ⟨B, Q⟩ → Derives M rules E C ⟨P, Q⟩
  | cases {k Γ E C P₁ P₂ Q} :
      Derives M rules (k := k) (Γ := Γ) E C ⟨P₁, Q⟩ →
      Derives M rules E C ⟨P₂, Q⟩ → Derives M rules E C ⟨P₁.disj P₂, Q⟩
  | abstraction {k Γ E C} (xs : List Sg.S)
      {P : Pattern Sg cfg (blockContext Γ xs)} {Q : Pattern Sg cfg Γ} :
      Derives M rules (Γ := blockContext Γ xs)
        (weakenEnvironment xs E) (weakenEnvironment xs C)
        ⟨(P : Pattern Sg cfg (blockContext Γ xs)), Silmaril.Logic.FirstOrder.Variables.weakenBlock cfg Γ xs Q⟩ →
      Derives M rules (k := k) (Γ := Γ) E C ⟨existsBlock cfg Γ xs P, Q⟩
  | consequence {k Γ E C P Q P₀ Q₀} :
      Pattern.entails M P P₀ →
      Derives M rules (k := k) (Γ := Γ) E C ⟨P₀, Q₀⟩ → Pattern.entails M Q₀ Q →
      Derives M rules E C ⟨P, Q⟩
  | circularity {k Γ E C c} :
      Derives M rules (k := k) (Γ := Γ) E (C ∪ {c}) c → Derives M rules E C c

def Claim.interpret (M : FOL.Structure Sg) (e : Embedding Γ) (c : Claim Sg cfg Γ) :
    Derivation.Claim (fun j : StockName Sg => M.carrier j.1) (M.carrier cfg) :=
  ⟨fun a w => Pattern.holds c.pre M e a w, fun a w => Pattern.holds c.post M e a w⟩

def environment (M : FOL.Structure Sg) (e : Embedding Γ) (E : Set (Claim Sg cfg Γ)) :=
  Claim.interpret M e '' E

end Silmaril.Logic.Reachability.Derivation.FirstOrder
