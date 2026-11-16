module

public import Silmaril.Logic.Rewriting.Reachability

@[expose] public section
namespace Silmaril.Logic.Rewriting.Examples
open CategoryTheory Silmaril.Logic.Institution

inductive NatOperation : (n : Nat) → (Fin n → Unit) → Unit → Type where
  | successor : NatOperation 1 (fun _ => ()) ()

def natSignature : Algebraic.ManySorted.Signature Unit := ⟨NatOperation⟩

abbrev natModel : Model natSignature where
  algebra := ⟨fun _ => Nat, fun op args => match op with | .successor => args 0 + 1⟩
  reaches _ := Nat.le
  refl _ := Nat.le_refl
  trans _ := Nat.le_trans
  congruence op x y h := by cases op; exact Nat.add_le_add_right (h 0) 1

abbrev successorRule : Algebraic.ManySorted.Equation natSignature :=
  ⟨1, (fun _ => ()), (), .var 0, .app .successor (fun _ => .var 0)⟩

theorem successor_rewrites : Sentence.Satisfies natModel (.rewrite successorRule) :=
  fun v => Nat.le_succ (v 0)

theorem successor_not_equation : ¬ Sentence.Satisfies natModel (.equation successorRule) := by
  intro h
  have bad := h (fun _ => 0)
  exact Nat.noConfusion bad

abbrev reverseRule : Algebraic.ManySorted.Equation natSignature :=
  ⟨1, (fun _ => ()), (), successorRule.rhs, successorRule.lhs⟩

theorem successor_not_reversible : ¬ Sentence.Satisfies natModel (.rewrite reverseRule) := by
  intro h
  exact Nat.not_succ_le_zero 0 (h (fun _ => 0))

theorem successor_canonical_reachability : CanonicalSentence.Satisfies
    ⟨natModel, fun _ => inferInstance⟩ (compile (.rewrite successorRule)) :=
  (compile_satisfaction _ _).mpr successor_rewrites

/-- Unrestricted matching models need not interpret algebraic operations as
singletons, nor their step as a preorder. The canonical restriction matters. -/
abbrev deadMatching : Reachability.Model () (reachSignature natSignature ()) where
  carrier _ := Unit
  nonempty _ := inferInstance
  operation _ _ := ∅

theorem successor_unrestricted_invalid :
    ¬ (compileEquation successorRule).Satisfies () deadMatching := by
  intro h
  have reachable := h (fun _ => ()) () rfl
  have empty_post : deadMatching.denote (fun _ => ()) (compileEquation successorRule).post = ∅ := by
    ext x
    simp [Matching.FirstOrder.Model.denote, Matching.FirstOrder.Pattern.ofTerm,
      Algebraic.ManySorted.Term.map, termEmbedding]
  rw [empty_post] at reachable
  change CTL.Until (fun _ _ => False) (fun _ => True) (fun _ => False) () at reachable
  cases reachable with
  | now hp => exact hp
  | next _ hs _ => exact hs

/-- A preorder may identify reachability in both directions without object equality. -/
def indiscreteNat : Model natSignature where
  algebra := natModel.algebra
  reaches _ _ _ := True
  refl _ _ := trivial
  trans _ {_ _ _} _ _ := trivial
  congruence _ _ _ _ := trivial

theorem opposite_rewrites_do_not_imply_equation :
    Sentence.Satisfies indiscreteNat (.rewrite successorRule) ∧
    Sentence.Satisfies indiscreteNat (.rewrite reverseRule) ∧
    ¬ Sentence.Satisfies indiscreteNat (.equation successorRule) :=
  ⟨fun _ => trivial, fun _ => trivial, successor_not_equation⟩

def emptySignature : Algebraic.ManySorted.Signature Unit := ⟨fun _ _ _ => Empty⟩

def emptyAlgebra : Algebraic.ManySorted.Model emptySignature :=
  ⟨fun _ => Empty, fun op => op.elim⟩

theorem eq_expansion_allows_empty : (discrete emptyAlgebra).algebra = emptyAlgebra := rfl

theorem empty_excluded_from_matching : ¬ ∃ M : InhabitedModel emptySignature, M.model = discrete emptyAlgebra := by
  rintro ⟨M, hm⟩
  have h := M.nonempty ()
  rw [hm] at h
  change Nonempty Empty at h
  obtain ⟨x⟩ := h
  exact x.elim

theorem restrictInhabited_not_modelExpansive : ¬ (restrictInhabited Unit).ModelExpansive := by
  intro h
  obtain ⟨M, hm⟩ := h emptySignature (discrete emptyAlgebra)
  exact empty_excluded_from_matching ⟨M, hm⟩

end Silmaril.Logic.Rewriting.Examples
