module

public import Silmaril.Logic.Egglog.Merge.Institution.Defs

@[expose] public section
namespace Silmaril.Logic.Egglog.Merge.Institution
open CategoryTheory Silmaril.Logic.Institution
variable {Value : Type} [SemilatticeSup Value]
variable {Key Target Other : Signature}

omit [SemilatticeSup Value] in
@[simp] theorem Bound.map_id (a : Bound Value Key) : a.map id = a := by cases a; rfl
omit [SemilatticeSup Value] in
@[simp] theorem Bound.map_comp (f : Key → Target) (g : Target → Other) (a : Bound Value Key) :
    a.map (g ∘ f) = (a.map f).map g := rfl

theorem bounds_holds_map (f : Key → Target) (M : Model Value Target)
    (as : List (Bound Value Key)) :
    (∀ a ∈ as.map (Bound.map f), a.Holds M) ↔
      ∀ a ∈ as, a.Holds ((Model.reduct f).obj M) := by
  simp only [List.forall_mem_map, Bound.holds_map]

@[simp] theorem Rule.holds_map (f : Key → Target) (M : Model Value Target)
    (r : Rule Value Key) : (r.map f).Holds M ↔ r.Holds ((Model.reduct f).obj M) := by
  unfold Rule.Holds Rule.map
  rw [bounds_holds_map]
  cases r.head <;> rfl

@[simp] theorem Sentence.holds_map (f : Key → Target) (M : Model Value Target)
    (s : Sentence Value Key) : (s.map f).Holds M ↔ s.Holds ((Model.reduct f).obj M) := by
  cases s with
  | rule r => exact r.holds_map f M
  | query goals => exact bounds_holds_map f M goals

omit [SemilatticeSup Value] in
@[simp] theorem Sentence.map_id (s : Sentence Value Key) : s.map id = s := by
  have hm : (Bound.map id : Bound Value Key → _) = id := funext Bound.map_id
  cases s with
  | rule r => cases r; simp only [map, Rule.map, hm, List.map_id, Option.map_id, id_eq]
  | query goals => simp only [map, hm, List.map_id]

omit [SemilatticeSup Value] in
@[simp] theorem Sentence.map_comp (f : Key → Target) (g : Target → Other)
    (s : Sentence Value Key) : s.map (g ∘ f) = (s.map f).map g := by
  cases s <;> simp only [Sentence.map, Rule.map, List.map_map, Option.map_map]
  all_goals rfl

/-- Full information-increasing model arrows; signature maps pull ideals back. -/
def room (Value : Type) [SemilatticeSup Value] (Key : Signature) : Room.{0,0,1} :=
  ⟨Sentence Value Key, Cat.of (Model Value Key), Sentence.Holds⟩

def corridor (f : Key → Target) : room Value Key ⟶ room Value Target :=
  ⟨Sentence.map f, Model.reduct f, Sentence.holds_map f⟩

def institution (Value : Type) [SemilatticeSup Value] : Signature ⥤ Room.{0,0,1} where
  obj := room Value
  map f := corridor (Value := Value) f
  map_id _ := Room.hom_ext (funext Sentence.map_id) rfl
  map_comp f g := Room.hom_ext (funext (Sentence.map_comp f g)) rfl

def inst (Value : Type) [SemilatticeSup Value] : Inst.{1,0,0,0,1} :=
  ⟨Signature, institution Value⟩

/-- An arbitrary theory of declarative rules and queries. -/
def TheoryHolds (M : Model Value Key) (H : Set (Sentence Value Key)) : Prop :=
  ∀ s ∈ H, s.Holds M

def Sat (H : Set (Sentence Value Key)) : Prop := ∃ M, TheoryHolds M H
def Unsat (H : Set (Sentence Value Key)) : Prop := ¬ Sat H

theorem theory_holds_map (f : Key → Target) (M : Model Value Target)
    (H : Set (Sentence Value Key)) :
    TheoryHolds M (Sentence.map f '' H) ↔ TheoryHolds ((Model.reduct f).obj M) H := by
  simp only [TheoryHolds, Set.forall_mem_image, Sentence.holds_map]

theorem sat_reduct (f : Key → Target) (H : Set (Sentence Value Key))
    (h : Sat (Sentence.map f '' H)) : Sat H := by
  obtain ⟨M, hM⟩ := h
  exact ⟨(Model.reduct f).obj M, (theory_holds_map f M H).mp hM⟩

theorem unsat_map (f : Key → Target) (H : Set (Sentence Value Key)) (h : Unsat H) :
    Unsat (Sentence.map f '' H) := fun hm => h (sat_reduct f H hm)

theorem entails_map (f : Key → Target) (H : Set (Sentence Value Key))
    (s : Sentence Value Key) (h : (room Value Key).Entails H s) :
    (room Value Target).Entails (Sentence.map f '' H) (s.map f) := by
  intro M hM
  exact (s.holds_map f M).mpr (h ((Model.reduct f).obj M) ((theory_holds_map f M H).mp hM))

/-- Collision joins have precisely the conjunction meaning of stable lower
bounds, in contrast to exact row equality. -/
theorem bound_sup (M : Model Value Key) (key : Key) (a b : Value) :
    (Bound.mk key (a ⊔ b)).Holds M ↔
      (Bound.mk key a).Holds M ∧ (Bound.mk key b).Holds M := sup_le_iff

/-- The existing operational soundness relation is exactly satisfaction of all
currently stored lower-bound observations. No engine invariant is assumed. -/
def tableTheory (table : Merge.Table Key Value) : Set (Sentence Value Key) :=
  {s | ∃ key value, table key = some value ∧ s = .query [⟨key, value⟩]}

theorem table_sound_iff (M : Model Value Key) (table : Merge.Table Key Value) :
    Merge.Sound M.value table ↔ TheoryHolds M (tableTheory table) := by
  constructor
  · intro h s hs
    obtain ⟨key, value, hv, rfl⟩ := hs
    intro a ha
    have he : a = Bound.mk key value := List.mem_singleton.mp ha
    subst a
    exact h key value hv
  · intro h key value hv
    exact h (.query [⟨key, value⟩]) ⟨key, value, hv, rfl⟩ (Bound.mk key value) (by simp)

/-- An already justified program ideal remains a program model after a sound
write: program truth is about the ideal, while stored information grows. -/
theorem write_preserves_model [DecidableEq Key] (M : Model Value Key)
    (H : Set (Sentence Value Key)) (table : Merge.Table Key Value) (key : Key) (value : Value)
    (hprogram : TheoryHolds M H) (hsound : TheoryHolds M (tableTheory table))
    (hvalue : (Bound.mk key value).Holds M) :
    TheoryHolds M H ∧ TheoryHolds M (tableTheory (Merge.write table key value)) :=
  ⟨hprogram, (table_sound_iff M _).mp
    (Merge.write_sound M.value table key value ((table_sound_iff M table).mpr hsound) hvalue)⟩

/-- Rules justify further writes from premises in a sound table. -/
theorem rule_write_sound [DecidableEq Key] (M : Model Value Key)
    (table : Merge.Table Key Value) (r : Rule Value Key) (head : Bound Value Key)
    (hr : r.Holds M) (hh : r.head = some head) (hsound : Merge.Sound M.value table)
    (hbody : ∀ a ∈ r.body, ∃ stored, table a.key = some stored ∧ a.lower ≤ stored) :
    Merge.Sound M.value (Merge.write table head.key head.lower) := by
  apply Merge.write_sound M.value table head.key head.lower hsound
  have h := hr (by
    intro a ha
    obtain ⟨stored, hs, hlo⟩ := hbody a ha
    exact le_trans hlo (hsound a.key stored hs))
  rw [hh] at h
  exact h

end Silmaril.Logic.Egglog.Merge.Institution
