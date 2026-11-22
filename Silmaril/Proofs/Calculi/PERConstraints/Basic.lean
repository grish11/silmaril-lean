module

public import Silmaril.Calculi.PERConstraints.Defs
public import Mathlib.Data.Set.Pairwise.List

@[expose] public section
namespace Silmaril.Calculi.PERConstraints.Proofs

open CategoryTheory Silmaril.Formats

variable {α β γ : Type}

theorem eq_class (model : PER α) {terms : Set α} {pivot : α} (hp : pivot ∈ terms) :
    EQ model terms ↔ ∀ term ∈ terms, model.rel pivot term := by
  refine ⟨fun holds => holds pivot hp, ?_⟩
  intro same left hl right hr
  exact model.laws.trans (model.laws.symm (same left hl)) (same right hr)

theorem all_image {rename : α → β} {items : Set α} {holds : β → Prop} :
    All holds (rename '' items) ↔ All (holds ∘ rename) items :=
  Set.forall_mem_image

theorem any_image {rename : α → β} {items : Set α} {holds : β → Prop} :
    Any holds (rename '' items) ↔ Any (holds ∘ rename) items :=
  Set.exists_mem_image

theorem eq_image (model : PER β) (rename : α → β) (terms : Set α) :
    EQ model (rename '' terms) ↔ EQ (model.pull rename) terms := by
  simp only [EQ, Set.forall_mem_image, PER.pull]

theorem distinct_image (model : PER β) {rename : α → β} {terms : Set α}
    (injective : terms.InjOn rename) :
    DISTINCT model (rename '' terms) ↔ DISTINCT (model.pull rename) terms := by
  exact and_congr Set.forall_mem_image injective.pairwise_image

theorem distinct_list_map (model : PER β) (rename : α → β) (terms : List α) :
    DISTINCTList model (terms.map rename) ↔ DISTINCTList (model.pull rename) terms :=
  and_congr List.forall_mem_map List.pairwise_map

theorem distinct_list_perm (model : PER α) {first second : List α} (perm : first.Perm second) :
    DISTINCTList model first ↔ DISTINCTList model second := by
  unfold DISTINCTList
  refine and_congr (forall_congr' fun term => imp_congr_left perm.mem_iff) ?_
  exact perm.pairwise_iff (fun unrelated related => unrelated (model.laws.symm related))

theorem distinct_list_iff (model : PER α) (terms : List α) :
    DISTINCTList model terms ↔ terms.Nodup ∧ DISTINCT model {term | term ∈ terms} := by
  let : Std.Symm (fun left right => ¬model.rel left right) :=
    ⟨fun _ _ unrelated related => unrelated (model.laws.symm related)⟩
  constructor
  · rintro ⟨valid, separated⟩
    have nodup : terms.Nodup := separated.imp_of_mem fun {left _right} hl _hr unrelated same =>
      unrelated (same ▸ valid left hl)
    exact ⟨nodup, valid, nodup.pairwise_coe.mpr separated⟩
  · rintro ⟨nodup, valid, separated⟩
    exact ⟨valid, nodup.pairwise_of_set_pairwise separated⟩

theorem bound_map_id (bound : Bound α) : bound.map id = bound := by
  cases bound <;> simp [Bound.map]

theorem bound_map_comp (first : α → β) (second : β → γ) (bound : Bound α) :
    bound.map (second ∘ first) = (bound.map first).map second := by
  cases bound <;> simp [Bound.map, Set.image_image, List.map_map, Function.comp_def]

theorem bound_map (model : PER β) (rename : α → β) (bound : Bound α) :
    (bound.map rename).Holds model ↔ bound.Holds (model.pull rename) := by
  cases bound with
  | eq terms => exact eq_image model rename terms
  | distinct terms => exact distinct_list_map model rename terms

theorem cnf_map (model : PER β) (rename : α → β) (sentence : CNF α) :
    CNF.Holds model (CNF.map rename sentence) ↔ CNF.Holds (model.pull rename) sentence := by
  simp only [CNF.Holds, CNF.map, All, Any, Set.forall_mem_image, Set.exists_mem_image, bound_map]

theorem dnf_map (model : PER β) (rename : α → β) (sentence : DNF α) :
    DNF.Holds model (DNF.map rename sentence) ↔ DNF.Holds (model.pull rename) sentence := by
  simp only [DNF.Holds, DNF.map, All, Any, Set.forall_mem_image, Set.exists_mem_image, bound_map]

theorem cnf_map_id (sentence : CNF α) : CNF.map id sentence = sentence := by
  have atoms : Bound.map (id : α → α) = id := funext bound_map_id
  simp only [CNF.map, atoms, Set.image_id, Set.image_id']

theorem cnf_map_comp (first : α → β) (second : β → γ) (sentence : CNF α) :
    CNF.map (second ∘ first) sentence = CNF.map second (CNF.map first sentence) := by
  simp only [CNF.map, Set.image_image, bound_map_comp]

theorem cnf_to_dnf (model : PER α) (sentence : CNF α) :
    DNF.Holds model (CNF.toDNF sentence) ↔ CNF.Holds model sentence := by
  constructor
  · rintro ⟨term, meets, holds⟩ clause member
    obtain ⟨bound, inside, chosen⟩ := meets clause member
    exact ⟨bound, inside, holds bound chosen⟩
  · intro holds
    exact ⟨{bound | bound.Holds model}, holds, fun _ member => member⟩

theorem dictionary_cnf {Key : Type} (model : PER α) (dict : Dictionary Key α) :
    CNF.Holds model (Dictionary.toCNF dict) ↔ Dictionary.Holds model dict := by
  constructor
  · intro holds key bound lookup
    obtain ⟨found, member, satisfied⟩ := holds {bound} ⟨key, bound, lookup, rfl⟩
    have same : found = bound := Set.mem_singleton_iff.mp member
    exact same ▸ satisfied
  · rintro holds clause ⟨key, bound, lookup, rfl⟩
    exact ⟨bound, Set.mem_singleton _, holds key bound lookup⟩

theorem modelReduct_id (signature : Syntax) :
    modelReduct (𝟙 signature) = 𝟭 (room signature).Mod := by
  exact CategoryTheory.Functor.ext (fun _ => rfl)
    (fun _ _ _ => @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _)

theorem modelReduct_comp {source middle target : Syntax} (first : source ⟶ middle)
    (second : middle ⟶ target) : modelReduct (first ≫ second) = modelReduct second ⋙ modelReduct first := by
  exact CategoryTheory.Functor.ext (fun _ => rfl)
    (fun _ _ _ => @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _)

end Silmaril.Calculi.PERConstraints.Proofs
