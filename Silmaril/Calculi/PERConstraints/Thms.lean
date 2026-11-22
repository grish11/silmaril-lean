module

public import Silmaril.Calculi.PERConstraints.Defs
public import Silmaril.Logic.Institution.Morphism
public import Mathlib.Data.Finset.Dedup
import Silmaril.Proofs.Calculi.PERConstraints.Basic

@[expose] public section
namespace Silmaril.Calculi.PERConstraints

open CategoryTheory Silmaril.Formats Silmaril.Logic.Institution

variable {α β γ : Type}

@[simp] theorem eq_empty (model : PER α) : EQ model ∅ := by simp [EQ]
@[simp] theorem eq_singleton (model : PER α) (term : α) :
    EQ model {term} ↔ model.Dom term := by simp [EQ, PER.Dom]

theorem eq_class (model : PER α) {terms : Set α} {pivot : α} (member : pivot ∈ terms) :
    EQ model terms ↔ ∀ term ∈ terms, model.rel pivot term := Proofs.eq_class model member

@[simp] theorem distinct_empty (model : PER α) : DISTINCT model ∅ :=
  by simp [DISTINCT, Set.Pairwise]
@[simp] theorem distinct_singleton (model : PER α) (term : α) :
    DISTINCT model {term} ↔ model.Dom term := by simp [DISTINCT, Set.Pairwise]
@[simp] theorem distinct_list_nil (model : PER α) : DISTINCTList model [] := by simp [DISTINCTList]
@[simp] theorem distinct_list_singleton (model : PER α) (term : α) :
    DISTINCTList model [term] ↔ model.Dom term := by simp [DISTINCTList]

theorem distinct_list_perm (model : PER α) {first second : List α} (perm : first.Perm second) :
    DISTINCTList model first ↔ DISTINCTList model second := Proofs.distinct_list_perm model perm

/-- Forgetting order is harmless, but forgetting repeated occurrences is not. -/
theorem distinct_list_iff (model : PER α) (terms : List α) :
    DISTINCTList model terms ↔ terms.Nodup ∧ DISTINCT model {term | term ∈ terms} :=
  Proofs.distinct_list_iff model terms

theorem distinct_list_iff_finset [DecidableEq α] (model : PER α) (terms : List α) :
    DISTINCTList model terms ↔ terms.Nodup ∧ DISTINCTFinset model terms.toFinset := by
  have same : (terms.toFinset : Set α) = {term | term ∈ terms} := Set.ext fun _ => List.mem_toFinset
  rw [DISTINCTFinset, same, distinct_list_iff]

theorem Bound.holds_ofFinsetEq (model : PER α) (terms : Finset α) :
    (Bound.ofFinsetEq terms).Holds model ↔ EQFinset model terms := Iff.rfl

theorem Bound.holds_ofFinsetDistinct (model : PER α) (terms : Finset α) :
    (Bound.ofFinsetDistinct terms).Holds model ↔ DISTINCTFinset model terms := by
  have same : {term | term ∈ terms.toList} = (terms : Set α) := Set.ext fun _ => Finset.mem_toList
  simp only [Bound.ofFinsetDistinct, Bound.Holds, distinct_list_iff, same, terms.nodup_toList,
    true_and, DISTINCTFinset]

theorem eq_image (model : PER β) (rename : α → β) (terms : Set α) :
    EQ model (rename '' terms) ↔ EQ (model.pull rename) terms := Proofs.eq_image model rename terms

/-- Set distinctness requires injectivity on the designated terms, not necessarily globally. -/
theorem distinct_image (model : PER β) {rename : α → β} {terms : Set α}
    (injective : terms.InjOn rename) : DISTINCT model (rename '' terms) ↔ DISTINCT (model.pull rename) terms :=
  Proofs.distinct_image model injective

theorem distinct_list_map (model : PER β) (rename : α → β) (terms : List α) :
    DISTINCTList model (terms.map rename) ↔ DISTINCTList (model.pull rename) terms :=
  Proofs.distinct_list_map model rename terms

@[simp] theorem Bound.map_id (bound : Bound α) : bound.map id = bound := Proofs.bound_map_id bound
theorem Bound.map_comp (first : α → β) (second : β → γ) (bound : Bound α) :
    bound.map (second ∘ first) = (bound.map first).map second := Proofs.bound_map_comp first second bound

theorem Bound.holds_map (model : PER β) (rename : α → β) (bound : Bound α) :
    (bound.map rename).Holds model ↔ bound.Holds (model.pull rename) := Proofs.bound_map model rename bound

theorem all_image {rename : α → β} {items : Set α} {holds : β → Prop} :
    All holds (rename '' items) ↔ All (holds ∘ rename) items := Proofs.all_image
theorem any_image {rename : α → β} {items : Set α} {holds : β → Prop} :
    Any holds (rename '' items) ↔ Any (holds ∘ rename) items := Proofs.any_image

@[simp] theorem CNF.holds_empty (model : PER α) : CNF.Holds model ∅ := by simp [CNF.Holds, All]
theorem CNF.not_holds_of_empty_clause (model : PER α) {sentence : CNF α} (member : ∅ ∈ sentence) :
    ¬ CNF.Holds model sentence := by
  intro holds
  simpa [Any] using holds ∅ member

@[simp] theorem DNF.not_holds_empty (model : PER α) : ¬ DNF.Holds model ∅ := by simp [DNF.Holds, Any]
theorem DNF.holds_of_empty_term (model : PER α) {sentence : DNF α} (member : ∅ ∈ sentence) :
    DNF.Holds model sentence := ⟨∅, member, by simp [All]⟩

theorem CNF.holds_ofFinsets (model : PER α) (clauses : Finset (Finset (Bound α))) :
    CNF.Holds model (CNF.ofFinsets clauses) ↔ AllFinset (AnyFinset (Bound.Holds model)) clauses :=
  all_image

theorem DNF.holds_ofFinsets (model : PER α) (terms : Finset (Finset (Bound α))) :
    DNF.Holds model (DNF.ofFinsets terms) ↔ AnyFinset (AllFinset (Bound.Holds model)) terms :=
  any_image

theorem CNF.holds_toDNF (model : PER α) (sentence : CNF α) :
    DNF.Holds model (CNF.toDNF sentence) ↔ CNF.Holds model sentence :=
  Proofs.cnf_to_dnf model sentence

@[simp] theorem CNF.map_id (sentence : CNF α) : CNF.map id sentence = sentence := Proofs.cnf_map_id sentence
theorem CNF.map_comp (first : α → β) (second : β → γ) (sentence : CNF α) :
    CNF.map (second ∘ first) sentence = CNF.map second (CNF.map first sentence) :=
  Proofs.cnf_map_comp first second sentence

theorem CNF.holds_map (model : PER β) (rename : α → β) (sentence : CNF α) :
    CNF.Holds model (CNF.map rename sentence) ↔ CNF.Holds (model.pull rename) sentence :=
  Proofs.cnf_map model rename sentence

theorem DNF.holds_map (model : PER β) (rename : α → β) (sentence : DNF α) :
    DNF.Holds model (DNF.map rename sentence) ↔ DNF.Holds (model.pull rename) sentence :=
  Proofs.dnf_map model rename sentence

/-- Any target witness pulls back; an arbitrary source witness need not extend. -/
theorem CNF.sat_of_map {rename : α → β} {sentence : CNF α} :
    (CNF.map rename sentence).SAT → sentence.SAT :=
  fun ⟨model, holds⟩ => ⟨model.pull rename, (CNF.holds_map model rename sentence).mp holds⟩

theorem CNF.unsat_map {rename : α → β} {sentence : CNF α} :
    sentence.UNSAT → (CNF.map rename sentence).UNSAT :=
  fun unsat model holds => unsat _ ((CNF.holds_map model rename sentence).mp holds)

theorem CNF.unsat_iff_not_sat (sentence : CNF α) : sentence.UNSAT ↔ ¬sentence.SAT :=
  not_exists.symm
theorem DNF.unsat_iff_not_sat (sentence : DNF α) : sentence.UNSAT ↔ ¬sentence.SAT :=
  not_exists.symm

theorem CNF.sat_toDNF (sentence : CNF α) : (CNF.toDNF sentence).SAT ↔ sentence.SAT :=
  exists_congr fun model => CNF.holds_toDNF model sentence

theorem CNF.unsat_toDNF (sentence : CNF α) : (CNF.toDNF sentence).UNSAT ↔ sentence.UNSAT :=
  forall_congr' fun model => not_congr (CNF.holds_toDNF model sentence)

theorem Dictionary.holds_toCNF {Key : Type} (model : PER α) (dict : Dictionary Key α) :
    CNF.Holds model (Dictionary.toCNF dict) ↔ Dictionary.Holds model dict :=
  Proofs.dictionary_cnf model dict

theorem Dictionary.sat_iff_cnf {Key : Type} (dict : Dictionary Key α) :
    Dictionary.SAT dict ↔ (Dictionary.toCNF dict).SAT :=
  exists_congr fun model => (Dictionary.holds_toCNF model dict).symm

theorem Dictionary.unsat_iff_cnf {Key : Type} (dict : Dictionary Key α) :
    Dictionary.UNSAT dict ↔ (Dictionary.toCNF dict).UNSAT :=
  forall_congr' fun model => not_congr (Dictionary.holds_toCNF model dict).symm

@[simp] theorem reduct_id {signature : Syntax} (model : Model signature) :
    reduct (𝟙 signature) model = model := rfl

theorem reduct_comp {source middle target : Syntax} (first : source ⟶ middle) (second : middle ⟶ target)
    (model : Model target) : reduct (first ≫ second) model = reduct first (reduct second model) := rfl

/-- The institution satisfaction law for inverse-image PER reducts. -/
theorem satisfaction {source target : Syntax} (rename : source ⟶ target)
    (model : Model target) (sentence : CNF source.Term) :
    CNF.Holds model (CNF.map rename.term sentence) ↔ CNF.Holds (reduct rename model) sentence :=
  CNF.holds_map model rename.term sentence

def corridor {source target : Syntax} (rename : source ⟶ target) : room source ⟶ room target :=
  ⟨CNF.map rename.term, modelReduct rename, fun model sentence => satisfaction rename model.as sentence⟩

theorem corridor_id (signature : Syntax) : corridor (𝟙 signature) = 𝟙 (room signature) := by
  apply Room.hom_ext (funext CNF.map_id)
  exact Proofs.modelReduct_id signature

theorem corridor_comp {source middle target : Syntax} (first : source ⟶ middle) (second : middle ⟶ target) :
    corridor (first ≫ second) = corridor first ≫ corridor second := by
  apply Room.hom_ext (funext (CNF.map_comp first.term second.term))
  exact Proofs.modelReduct_comp first second

/-- The CNF institution for PER constraints over all total syntax functions. -/
def institution : Syntax ⥤ Room.{0,0,0} where
  obj := room
  map := corridor
  map_id := corridor_id
  map_comp := corridor_comp

/-- Partial-equivalence constraints: sentences are CNFs and models are PERs. -/
def bundled : Inst := ⟨Syntax, institution⟩

end Silmaril.Calculi.PERConstraints
