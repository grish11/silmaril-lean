module

public import Silmaril.Logic.Egglog.Merge.Institution.Thms
public import Silmaril.Logic.Egglog.Core.Graph.Defs
public import Silmaril.Logic.Egglog.Core.Positive.Thms

@[expose] public section
namespace Silmaril.Logic.Egglog.Merge.Institution
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples

/-- Integrity constraints make a uniform encoding into the always-satisfiable
positive Core impossible, independently of model expansion. Full Graph formulas
are a different target. -/
theorem no_comorphism_to_positiveCore (Value : Type) [SemilatticeSup Value] :
    ¬ Nonempty (Inst.CoHom (inst Value) Egglog.Core.inst) := by
  rintro ⟨f⟩
  let s : Sentence Value Empty := .rule ⟨[], none⟩
  let M := Egglog.Core.Positive.singletonModel (f.Φ.obj Empty)
  have ht := Egglog.Core.Positive.singletonModel_sentence_holds ((f.ρ.app Empty).sen s)
  have hs := ((f.ρ.app Empty).sat M s).mp ht
  exact hs (by simp)

namespace BooleanGraph

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Only the two-element semantic lattice is encoded here. General lattice
orders are not silently identified with equality-table relations. -/
def signature (Key : Type) : Egglog.Core.Signature where
  S := Unit
  Op := fun _ _ _ => PEmpty
  Rel := fun _ _ => Key
  Function := fun _ _ _ => PEmpty

def signatures : Type ⥤ Egglog.Core.Signature where
  obj := signature
  map f := { sorts := id, ops := fun o => o.elim, rels := f, functions := fun t => t.elim }
  map_id _ := by
    congr 1
    · congr 1
      congr 1
      funext n w s o; exact o.elim
    · funext n w s o; exact o.elim
  map_comp _ _ := by
    congr 1
    · congr 1
      congr 1
      funext n w s o; exact o.elim
    · funext n w s o; exact o.elim

noncomputable def decode {Key : Type} (M : Egglog.Core.Model (signature Key)) : Model Bool Key :=
  by classical exact ⟨fun key => decide (M.rel (n := 0) (w := fun _ => ()) key (fun i => i.elim0))⟩

noncomputable def models (Key : Type) : Egglog.Core.Model (signature Key) ⥤ Model Bool Key where
  obj := decode
  map h := ⟨fun key => by
    classical
    apply Bool.le_iff_imp.mpr
    simp only [decode, Bool.decide_iff]
    intro hp
    have hh := h.map_rel key (fun i => i.elim0) hp
    convert hh using 1⟩
  map_id _ := by rfl
  map_comp _ _ := by rfl

abbrev empty : Fin 0 → Unit := fun i => i.elim0
abbrev Formula (Key : Type) := FOL.Formula (Egglog.Core.Graph.signature (signature Key)) empty

def atom {Key : Type} (a : Bound Bool Key) : Formula Key :=
  if a.lower then .rel (n := 0) (w := empty) (.predicate a.key) (fun i => i.elim0) else .tt

def conjunction {Key : Type} : List (Bound Bool Key) → Formula Key
  | [] => .tt
  | a :: rest => .and (atom a) (conjunction rest)

def formula {Key : Type} : Sentence Bool Key → Formula Key
  | .query goals => conjunction goals
  | .rule r => .not (.and (conjunction r.body)
      (.not (r.head.elim (.not .tt) atom)))

def sentence {Key : Type} (s : Sentence Bool Key) :
    FOL.Sentence (Egglog.Core.Graph.signature (signature Key)) := ⟨empty, formula s⟩

theorem atom_holds {Key : Type} (M : Egglog.Core.Model (signature Key))
    (a : Bound Bool Key) (ρ : ∀ i, M.carrier (empty i)) :
    (atom a).Holds (Egglog.Core.Graph.model M) ρ ↔ a.Holds (decode M) := by
  classical
  cases a with
  | mk key lower =>
    cases lower <;> simp [atom, Bound.Holds, decode, FOL.Formula.Holds, Egglog.Core.Graph.model, Bool.le_iff_imp]
    apply iff_of_eq
    congr 1
    funext i; exact i.elim0

theorem conjunction_holds {Key : Type} (M : Egglog.Core.Model (signature Key))
    (as : List (Bound Bool Key)) (ρ : ∀ i, M.carrier (empty i)) :
    (conjunction as).Holds (Egglog.Core.Graph.model M) ρ ↔ ∀ a ∈ as, a.Holds (decode M) := by
  induction as with
  | nil => simp [conjunction, FOL.Formula.Holds]
  | cons a rest ih => simp [conjunction, FOL.Formula.Holds, atom_holds, ih]

theorem sentence_holds {Key : Type} (M : Egglog.Core.Model (signature Key))
    (s : Sentence Bool Key) : (sentence s).Holds (Egglog.Core.Graph.model M) ↔ s.Holds (decode M) := by
  classical
  cases s with
  | query goals => exact conjunction_holds M goals _
  | rule r =>
    simp only [sentence, formula, FOL.Sentence.Holds, FOL.Formula.Holds,
      Sentence.Holds, Rule.Holds]
    cases r.head <;> simp only [Option.elim, FOL.Formula.Holds]
    all_goals simp only [conjunction_holds, atom_holds]
    all_goals tauto

/-- Every Boolean ideal has an independent graph expansion with a singleton
carrier and no constructor/table symbols. -/
def expansion {Key : Type} (M : Model Bool Key) : Egglog.Core.Model (signature Key) where
  carrier := fun _ => Unit
  op o := o.elim
  rel key _ := M.value key = true
  row t := t.elim
  functional t := t.elim

@[simp] theorem decode_expansion {Key : Type} (M : Model Bool Key) :
    decode (expansion M) = M := by
  classical
  cases M with
  | mk value =>
    change Model.mk _ = Model.mk value
    congr 1
    funext key
    simp only [expansion]
    simp

/-- This is satisfiability in functional partial-table graph models, not in
arbitrary first-order structures. -/
theorem sat_iff {Key : Type} (H : Set (Sentence Bool Key)) :
    (∃ M : Egglog.Core.Model (signature Key), ∀ s ∈ H,
      (sentence s).Holds (Egglog.Core.Graph.model M)) ↔ Sat H := by
  constructor
  · rintro ⟨M, hM⟩
    exact ⟨decode M, fun s hs => (sentence_holds M s).mp (hM s hs)⟩
  · rintro ⟨M, hM⟩
    refine ⟨expansion M, fun s hs => ?_⟩
    apply (sentence_holds (expansion M) s).mpr
    simpa only [decode_expansion] using hM s hs

/-- Both directions concern exactly the encoded Boolean ground theory. -/
theorem unsat_iff {Key : Type} (H : Set (Sentence Bool Key)) :
    (¬ ∃ M : Egglog.Core.Model (signature Key), ∀ s ∈ H,
      (sentence s).Holds (Egglog.Core.Graph.model M)) ↔ Unsat H :=
  not_congr (sat_iff H)

theorem entails_iff {Key : Type} (H : Set (Sentence Bool Key)) (s : Sentence Bool Key) :
    (∀ M : Egglog.Core.Model (signature Key),
      (∀ t ∈ H, (sentence t).Holds (Egglog.Core.Graph.model M)) →
      (sentence s).Holds (Egglog.Core.Graph.model M)) ↔ (room Bool Key).Entails H s := by
  change _ ↔ ∀ M : Model Bool Key, (∀ t ∈ H, t.Holds M) → s.Holds M
  constructor
  · intro h M hM
    have hm : ∀ t ∈ H, (sentence t).Holds (Egglog.Core.Graph.model (expansion M)) := by
      intro t ht
      apply (sentence_holds (expansion M) t).mpr
      simpa only [decode_expansion] using hM t ht
    have hs := (sentence_holds (expansion M) s).mp (h (expansion M) hm)
    simpa only [decode_expansion] using hs
  · intro h M hM
    apply (sentence_holds M s).mpr
    exact h (decode M) (fun t ht => (sentence_holds M t).mp (hM t ht))

theorem atom_map {Key Target : Type} (f : Key → Target) (a : Bound Bool Key) :
    atom (a.map f) = (atom a).map (Egglog.Core.Graph.signatureMap (signatures.map (TypeCat.ofHom f))) := by
  cases a with
  | mk key lower =>
    cases lower <;> simp only [atom, Bound.map, Bool.false_eq_true, ite_false, ite_true, FOL.Formula.map]
    congr 1
    funext i; exact i.elim0

theorem conjunction_map {Key Target : Type} (f : Key → Target) (as : List (Bound Bool Key)) :
    conjunction (as.map (Bound.map f)) =
      (conjunction as).map (Egglog.Core.Graph.signatureMap (signatures.map (TypeCat.ofHom f))) := by
  induction as with
  | nil => rfl
  | cons a rest ih => simp only [List.map_cons, conjunction, FOL.Formula.map, atom_map, ih]

theorem sentence_map {Key Target : Type} (f : Key → Target) (s : Sentence Bool Key) :
    sentence (s.map f) = (sentence s).map (Egglog.Core.Graph.signatureMap (signatures.map (TypeCat.ofHom f))) := by
  cases s with
  | query goals =>
    change FOL.Sentence.mk (Sg := Egglog.Core.Graph.signature (signature Target)) empty _ =
      FOL.Sentence.mk (Sg := Egglog.Core.Graph.signature (signature Target)) empty _
    congr 1
    exact conjunction_map f goals
  | rule r =>
    change FOL.Sentence.mk (Sg := Egglog.Core.Graph.signature (signature Target)) empty _ =
      FOL.Sentence.mk (Sg := Egglog.Core.Graph.signature (signature Target)) empty _
    congr 1
    simp only [sentence, formula, Sentence.map, Rule.map, FOL.Formula.map, conjunction_map]
    cases r.head <;> simp only [Option.map, Option.elim, FOL.Formula.map, atom_map]

/-- Natural, truth-exact Boolean lattice rules into the full graph institution. -/
noncomputable def toGraph : Inst.CoHom (inst Bool) Egglog.Core.Graph.inst where
  Φ := signatures
  ρ :=
    { app := fun Key => ⟨sentence, models Key, sentence_holds⟩
      naturality := by
        intro Key Target f
        change Type at Key Target
        change Key ⟶ Target at f
        exact Room.hom_ext (funext (sentence_map (ConcreteCategory.hom f))) rfl }

theorem toGraph_modelExpansive : toGraph.ModelExpansive :=
  fun _ M => ⟨expansion M, decode_expansion M⟩

end BooleanGraph
end Silmaril.Logic.Egglog.Merge.Institution
