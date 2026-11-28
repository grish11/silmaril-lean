module

public import Silmaril.Semantics.Brookes.Word.Thms
public import Silmaril.Semantics.Brookes.TreeSC.Closed.Thms

public section

namespace Silmaril.Proofs.Semantics.Brookes.Word.Regression

open Silmaril.Semantics.Brookes
open Silmaril.Semantics.Brookes.Word

private def sharedWrite (thread : Bool) : Command (TreeSC.Store Unit) :=
  TreeSC.writeBehavior () (if thread then 2 else 1)

private theorem sharedWrites_differ :
    endpoints (Command.seq (sharedWrite false) (sharedWrite true)) ≠
      endpoints (Command.seq (sharedWrite true) (sharedWrite false)) := by
  intro equal
  have forward : endpoints (Command.seq (sharedWrite false) (sharedWrite true))
      (fun _ => 0) (fun _ => 2) :=
    Command.seq_completes_iff.mpr ⟨fun _ => 1,
      Behavior.atomic_completes_iff.mpr (by funext x; cases x; rfl),
      Behavior.atomic_completes_iff.mpr (by funext x; cases x; rfl)⟩
  rw [equal] at forward
  obtain ⟨_, _, last⟩ := Command.seq_completes_iff.mp forward
  have impossible : (2 : Nat) = 1 := congrFun (Behavior.atomic_completes_iff.mp last) ()
  cases impossible

/-- Two distinct thread labels writing the same cell have no endpoint interpretation
through the adjacent-swap quotient. -/
theorem sharedWrites_no_endpoint_lift :
    ¬ ∃ f : Quot (Swap (fun a b : Bool => a ≠ b)) →
        TreeSC.Store Unit → TreeSC.Store Unit → Prop,
      ∀ word, f (Quot.mk _ word) =
        endpoints (eval (fun thread => TreeSC.writeBehavior () (if thread then 2 else 1)) word) := by
  rintro ⟨f, factors⟩
  exact sharedWrites_differ (commutesAtEndpoints_of_lift f factors Bool.false_ne_true)

private def writeLeft : Command (Bool × Bool) :=
  Behavior.atomic fun s t _ => t.1 = true ∧ s.2 = t.2

private def writeRight : Command (Bool × Bool) :=
  Behavior.atomic fun s t _ => s.1 = t.1 ∧ t.2 = true

private theorem disjointWrites_same_endpoints :
    endpoints (Command.seq writeLeft writeRight) = endpoints (Command.seq writeRight writeLeft) :=
  product_commutes_at_endpoints writeLeft writeRight (fun _ x => x = true) (fun _ y => y = true)
    (funext fun _ => funext fun _ => propext Behavior.atomic_completes_iff)
    (funext fun _ => funext fun _ => propext Behavior.atomic_completes_iff)

private def leftThenRight : Trace (Bool × Bool) :=
  [((false, false), (true, false)), ((true, false), (true, true))]

private theorem leftThenRight_accepted : (Command.seq writeLeft writeRight).accepts leftThenRight () :=
  Behavior.bind_accepts_iff.mpr ⟨[((false, false), (true, false))], [((true, false), (true, true))],
    (), Behavior.atomic_completes_iff.mpr ⟨rfl, rfl⟩,
    Behavior.atomic_completes_iff.mpr ⟨rfl, rfl⟩, .refl _⟩

private theorem seq_atomic_seed {S : Type} {p q : S → S → Unit → Prop} {word : Trace S}
    (h : (Command.seq (Behavior.atomic p) (Behavior.atomic q)).accepts word ()) :
    ∃ s m n t, p s m () ∧ q n t () ∧ Reduces [(s, m), (n, t)] word := by
  obtain ⟨left, right, result, hp, hq, hword⟩ := Behavior.bind_accepts_iff.mp h
  cases result
  obtain ⟨s, m, hp, hleft⟩ := Behavior.atomic_accepts_iff.mp hp
  obtain ⟨n, t, hq, hright⟩ := Behavior.atomic_accepts_iff.mp hq
  exact ⟨s, m, n, t, hp, hq, (hleft.append hright).trans hword⟩

private def Preserves {S : Type} (P : S → Prop) (word : Trace S) : Prop :=
  ∀ pair ∈ word, P pair.1 → P pair.2

private theorem preserves_of_reduces {S : Type} {P : S → Prop} {raw word : Trace S}
    (reduction : Reduces raw word) (holds : Preserves P raw) : Preserves P word := by
  induction reduction with
  | refl => exact holds
  | tail _ step ih =>
      cases step with
      | stutter pre post s =>
        intro pair mem hp
        rcases List.mem_append.mp mem with before | atOrAfter
        · exact ih pair (List.mem_append_left _ before) hp
        · rcases List.mem_cons.mp atOrAfter with rfl | after
          · exact hp
          · exact ih pair (List.mem_append_right _ after) hp
      | mumble pre post s t u =>
        intro pair mem hp
        rcases List.mem_append.mp mem with before | atOrAfter
        · exact ih pair (List.mem_append_left _ before) hp
        · rcases List.mem_cons.mp atOrAfter with rfl | after
          · have ht := ih (s, t) (by simp) hp
            exact ih (t, u) (by simp) ht
          · exact ih pair (List.mem_append_right _
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ after))) hp

private theorem leftThenRight_rejected : ¬ (Command.seq writeRight writeLeft).accepts leftThenRight () := by
  intro h
  obtain ⟨s, m, n, t, ⟨hx, hy⟩, _, reduction⟩ := seq_atomic_seed h
  have run : Runs (false, false) [(s, m), (n, t)] (true, true) :=
    Runs.of_reduces reduction (.cons (.cons (.nil _)))
  cases run with
  | cons rest =>
    cases rest with
    | cons last =>
      cases last
      have hm : m = (false, true) := Prod.ext hx.symm hy
      subst m
      have preserves := preserves_of_reduces (P := fun p => p = (true, false)) reduction
        (by simp [Preserves])
      have impossible := preserves ((true, false), (true, true)) (by simp [leftThenRight]) rfl
      cases impossible

/-- Two disjoint writes have equal endpoint relations and different open behaviors. -/
theorem disjointWrites_separate_observations :
    ∃ p q : Command (Bool × Bool),
      endpoints (Command.seq p q) = endpoints (Command.seq q p) ∧
      Command.seq p q ≠ Command.seq q p := by
  refine ⟨writeLeft, writeRight, disjointWrites_same_endpoints, ?_⟩
  intro equal
  exact leftThenRight_rejected (equal ▸ leftThenRight_accepted)

end Silmaril.Proofs.Semantics.Brookes.Word.Regression
