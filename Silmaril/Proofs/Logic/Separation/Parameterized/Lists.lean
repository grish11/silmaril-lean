module

public import Silmaril.Logic.Separation.Parameterized.Lists.Defs

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Separation.Parameterized.Lists

private theorem eval_var (M : Model signature) {k} (ρ : Tuple M k) (i : Fin k) :
    (Term.var i : Term signature k).eval M ρ = ρ i := rfl

private theorem eval_nil (M : Model signature) {k} (ρ : Tuple M k) :
    nilTerm.eval M ρ = null M := by
  apply congrArg (M.operation Operation.nil)
  funext i
  exact i.elim0

private theorem denote_link (M : Model signature) {k} (ρ : Tuple M k) (x y : Term signature k) :
    (link x y).denote M ρ = cell M (x.eval M ρ) (y.eval M ρ) := by
  apply congrArg (M.atom Atom.link)
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  rfl

/-- This computation includes pointer passing, object binding and the actual
resource split, and is uniform in the arbitrary captured outside value. -/
theorem body_step (M : Model signature) (ρ : Tuple M 1) (X : Set (State M 1)) :
    bodyOperator M body (fun i => i.elim0) ρ X = step M X := by
  ext s
  dsimp only [bodyOperator, body, Pattern.denote]
  simp only [Assertion.denote, denote_link, eval_nil, eval_var,
    insert, step,
    Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_compl_iff]
  constructor
  · rintro (h | ⟨y,a,b,hj,⟨hn,hc⟩,ht⟩)
    · exact Or.inl h
    · exact Or.inr ⟨y,a,b,hn,hc,hj,ht⟩
  · rintro (h | ⟨y,a,b,hn,hc,hj,ht⟩)
    · exact Or.inl h
    · exact Or.inr ⟨y,a,b,hj,⟨hn,hc⟩,ht⟩

/-- Every resource admitted by the true powerset LFP has a finite linked
construction. The theorem does not assume that arbitrary resources are finite. -/
theorem lfp_linked (M : Model signature) (ρ : Tuple M 1) :
    lfpSet M body (fun i => i.elim0) ρ ⊆ {s | Linked M (s.1 0) s.2} := by
  apply lfpSet_induction
  rw [body_step]
  intro s hs
  rcases hs with ⟨hn,he⟩ | ⟨y,a,b,hn,hc,hj,ht⟩
  · change Linked M (s.1 0) s.2
    rw [hn,he]
    exact Linked.nil
  · exact Linked.cons hn hc hj ht

/-- Conversely, arbitrary finite linked constructions are in the LFP. -/
theorem linked_lfp (M : Model signature) (ρ : Tuple M 1) {x h} (linked : Linked M x h) :
    ((fun _ => x), h) ∈ lfpSet M body (fun i => i.elim0) ρ := by
  induction linked with
  | nil =>
      rw [lfpSet_unfold, body_step]
      exact Or.inl ⟨rfl,rfl⟩
  | @cons x y a b h hn hc hj ht ih =>
      rw [lfpSet_unfold, body_step]
      exact Or.inr ⟨y,a,b,hn,hc,hj,ih⟩

/-- The actual source list(x) denotes exactly the separate inductive linked
shape, for every model, starting pointer and resource. -/
theorem list_iff_linked (M : Model signature) (ρ : Tuple M 1) (h : M.resource.carrier) :
    (ρ,h) ∈ list.denote M (fun i => i.elim0) ↔ Linked M (ρ 0) h := by
  change ((fun _ : Fin 1 => ρ 0), h) ∈ lfpSet M (P' := fun _ : Fin 1 => 1) body (fun i => i.elim0) ρ ↔ _
  exact ⟨fun hs => lfp_linked M ρ hs, linked_lfp M ρ⟩

end Silmaril.Logic.Separation.Parameterized.Lists
