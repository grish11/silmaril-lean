module

public import Silmaril.Semantics.Region.Semantic.Defs
import Silmaril.Proofs.Semantics.Region.Semantic

@[expose] public section
namespace Silmaril.Semantics.Region
universe u v w z
variable {State : Type u} {Lab : Type v} {Event : Type w} {Stop : Type z}
variable {T : TransitionSystem State Lab Event Stop} {A A' D B E C : State → Prop}
variable {U V X Y : Lab → Prop}

theorem sound_iff_outward : Sound T A U X ↔ ∀ l, outward T A U l → X l :=
  Proofs.sound_iff_outward

/-- Soundness is closed under stronger admitted domains and larger allowances,
with the SAME transition system and support. This is not an interface-change rule. -/
theorem sound_weaken (h : Sound T A U X) (ha : ∀ s, A' s → A s)
    (hx : ∀ l, X l → Y l) : Sound T A' U Y :=
  fun s es t hs hf => hx _ (h s es t (ha s hs) hf)

theorem greatest_characterization {Seg : Type*} (wf : Lab → Prop)
    (admit : Lab → State → Prop) (labels : Finset Seg → Lab → Prop)
    (ss : Finset Seg) (e : Lab) (xs : Finset Lab) :
    greatest T wf admit labels ss e xs ↔ Valid T wf (admit e) (labels ss) e xs := Iff.rfl

/-- Every sound recognizer is included; there need be no computable greatest
recognizer, finite least target set, or unique maximal partition. -/
theorem recognizer_included {Seg : Type*} (wf : Lab → Prop)
    (admit : Lab → State → Prop) (labels : Finset Seg → Lab → Prop)
    (recognizes : Finset Seg → Lab → Finset Lab → Prop)
    (sound : ∀ ss e xs, recognizes ss e xs → Valid T wf (admit e) (labels ss) e xs) :
    ∀ ss e xs, recognizes ss e xs → greatest T wf admit labels ss e xs := sound

theorem local_sound (cert : Local T U D B)
    (admit : ∀ s, A s → D s) (boundary : ∀ t, B t → X (T.pc t)) : Sound T A U X :=
  Proofs.local_sound cert admit boundary

theorem glue_local (disjoint : ∀ l, U l → V l → False)
    (left : Local T U D B) (right : Local T V E C)
    {entryU entryV : Lab}
    (uv : Wiring T U V D B E entryV X) (vu : Wiring T V U E C D entryU X) :
    Local T (fun l => U l ∨ V l)
      (fun s => (U (T.pc s) ∧ D s) ∨ (V (T.pc s) ∧ E s))
      (fun s => X (T.pc s)) := Proofs.glue_local disjoint left right uv vu

/-- Semantic parent closure for actually wired children, including cycles.
The entry-domain premise must be discharged for the parent; arbitrary parents
and arbitrary existential support witnesses are not covered. -/
theorem glue_sound (disjoint : ∀ l, U l → V l → False)
    (left : Local T U D B) (right : Local T V E C)
    {entryU entryV : Lab}
    (uv : Wiring T U V D B E entryV X) (vu : Wiring T V U E C D entryU X)
    (admit : ∀ s, A s → (U (T.pc s) ∧ D s) ∨ (V (T.pc s) ∧ E s)) :
    Sound T A (fun l => U l ∨ V l) X :=
  local_sound (glue_local disjoint left right uv vu) admit (fun _ h => h)

theorem wp_iff (Q : Lab → List Event → State → Prop) (R : Stop → List Event → State → Prop) :
    PartialHoare T A U Q R ↔ ∀ s, A s → wp T U Q R s := Proofs.wp_iff Q R

theorem top_sound : TargetSound T A U (.top : Targets Lab) := fun _ _ _ _ _ => trivial

theorem terminator_sound {Term : Type*} {term : Term} {transfer : Term → State → Prop}
    {targets : Targets Lab} (coverage : TerminatorCoverage T A U term transfer)
    (sound : ∀ t, transfer term t → targets.Allows (T.pc t)) : TargetSound T A U targets :=
  fun s es t ha hf => sound t (coverage s es t ha hf)

/-- Congruence is extensional. In particular there is no exit-list order. -/
theorem sound_congr (a : A = A') (x : X = Y) : Sound T A U X ↔ Sound T A' U Y := by
  subst a; subst x; rfl
/-- In particular this proves finite-graph glue by taking Index = Fin n.
Overlapping children require compatible domains at each actual transfer;
this theorem does not derive a dominator tree. -/
theorem family_sound {Index : Type*} (supports : Index → Lab → Prop)
    (domains boundaries : Index → State → Prop) (entries : Index → Lab)
    (children : ∀ i, Local T (supports i) (domains i) (boundaries i))
    (wiring : FamilyWiring T supports domains boundaries entries X)
    (admit : ∀ s, A s → ∃ i, supports i (T.pc s) ∧ domains i s) :
    Sound T A (fun l => ∃ i, supports i l) X :=
  local_sound (Proofs.family_local supports domains boundaries entries children wiring) admit
    (fun _ h => h)

theorem singleEntry_union {edge : Lab → Lab → Prop} {e : Lab}
    (left : SingleEntry edge U e)
    (rightEntries : ∀ x y, edge x y → V y → ¬ V x → U x) :
    SingleEntry edge (fun l => U l ∨ V l) e := Proofs.singleEntry_union left rightEntries

theorem finishes_not_diverges {s : State} (finish : Finishes T U s) : ¬ Diverges T U s :=
  Proofs.finishes_not_diverges finish

/-- Conditional uniqueness is about exact observed exit predicates, not partitions. -/
theorem exact_unique (hx : Exact T A U X) (hy : Exact T A U Y) : X = Y :=
  funext fun l => propext ((hx l).trans (hy l).symm)

/-- A semantic WP composition/unfolding rule. The successor WP carries the
emitted prefix, state, guards, interface and frame to the continuation. -/
theorem wp_unfold (Q : Lab → List Event → State → Prop)
    (R : Stop → List Event → State → Prop) {s : State} (inside : U (T.pc s)) :
    wp T U Q R s ↔
      (∀ k, T.halt s k → R k [] s) ∧
      ∀ es t, T.step s es t →
        (¬ U (T.pc t) → Q (T.pc t) es t) ∧
        (U (T.pc t) → wp T U (fun l rest f => Q l (es ++ rest) f)
          (fun k rest f => R k (es ++ rest) f) t) := Proofs.wp_unfold Q R inside

end Silmaril.Semantics.Region
