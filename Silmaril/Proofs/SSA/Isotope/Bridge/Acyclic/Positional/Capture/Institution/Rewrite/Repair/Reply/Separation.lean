module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Model.Defs

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply

private theorem prepend_eq {A : Type} {e f : Event} {x y : Outcome A}
    (h : prepend e x = prepend f y) : e = f ∧ x = y := by
  have words : e :: x.2.toList = f :: y.2.toList := congrArg (fun z => z.2.toList) h
  obtain ⟨head, suffix⟩ := List.cons.inj words
  have result := congrArg (fun z : Outcome A => z.1) h
  change x.1 = y.1 at result
  exact ⟨head, Prod.ext result (FreeMonoid.ext suffix)⟩

private theorem mem_prepend {A : Type} {e f : Event} {x : Outcome A}
    {s : Set (Outcome A)} : prepend e x ∈ prepend f '' s ↔ e = f ∧ x ∈ s := by
  constructor
  · rintro ⟨y, hy, eq⟩
    obtain ⟨rfl, rfl⟩ := prepend_eq eq
    exact ⟨rfl, hy⟩
  · rintro ⟨rfl, hx⟩
    exact ⟨x, hx, rfl⟩

theorem afterReply_outcomesWith_proof {R A : Type} (success : R → A) (request right : Bool) (l r : Normal R) :
    afterReply request right ((Normal.ask request l r).outcomesWith success) =
      (if right then r else l).outcomesWith success := by
  cases right <;> ext x <;>
    simp only [afterReply, Set.mem_preimage, Normal.outcomesWith, Set.mem_union, mem_prepend] <;> simp

private inductive Root (A : Type) where
  | ret (result : A)
  | stop (fault : Bool)
  | emit (bit : Bool)
  | ask (request : Bool)

private def root {R A : Type} (success : R → A) : Normal R → Root A
  | .ret r => .ret (success r)
  | .stop fault => .stop fault
  | .emit bit _ => .emit bit
  | .ask req _ _ => .ask req

private def observationRoot {A : Type} (x : Outcome A) : Root A :=
  match x.2.toList with
  | [] => match x.1 with
    | .ok a => .ret a
    | .error fault => .stop fault
  | .emit bit :: _ => .emit bit
  | .answer req _ :: _ => .ask req

private theorem outcomes_nonempty {R A : Type} (success : R → A) (p : Normal R) :
    (p.outcomesWith success).Nonempty := by
  induction p with
  | ret r => exact ⟨_, rfl⟩
  | stop fault => exact ⟨_, rfl⟩
  | emit bit next ih => exact ih.image _
  | ask req l r ihl ihr => exact (ihl.image (prepend (.answer req false))).mono Set.subset_union_left

private theorem root_of_mem {R A : Type} (success : R → A) (p : Normal R) {x : Outcome A}
    (h : x ∈ p.outcomesWith success) : observationRoot x = root success p := by
  cases p with
  | ret r =>
    obtain rfl : x = (.ok (success r), 1) := h
    rfl
  | stop fault =>
    obtain rfl : x = (.error fault, 1) := h
    rfl
  | emit bit next =>
    obtain ⟨y, _, rfl⟩ := h
    rfl
  | ask req l r =>
    rcases h with ⟨y, _, rfl⟩ | ⟨y, _, rfl⟩ <;> rfl

private theorem root_eq_of_outcomes {R A : Type} (success : R → A) {p q : Normal R}
    (h : p.outcomesWith success = q.outcomesWith success) : root success p = root success q := by
  obtain ⟨x, hx⟩ := outcomes_nonempty success p
  exact (root_of_mem success p hx).symm.trans (root_of_mem success q (h ▸ hx))

theorem outcomesWith_injective_proof {R A : Type} (success : R → A) (hs : Function.Injective success) :
    Function.Injective (Normal.outcomesWith success) := by
  intro p
  induction p with
  | ret r =>
    intro q h
    have eq := root_eq_of_outcomes success h
    cases q with
    | ret r' => exact congrArg Normal.ret (hs (Root.ret.inj eq))
    | stop | emit | ask => cases eq
  | stop fault =>
    intro q h
    have eq := root_eq_of_outcomes success h
    cases q <;> cases eq
    rfl
  | emit bit next ih =>
    intro q h
    have eq := root_eq_of_outcomes success h
    cases q <;> cases eq
    rename_i next'
    apply congrArg (Normal.emit bit)
    apply ih
    ext x
    simpa only [Normal.outcomesWith, mem_prepend, true_and] using
      Set.ext_iff.mp h (prepend (.emit bit) x)
  | ask req l r ihl ihr =>
    intro q h
    have eq := root_eq_of_outcomes success h
    cases q <;> cases eq
    congr 1
    · apply ihl
      simpa only [afterReply_outcomesWith_proof, Bool.false_eq_true, ite_false] using
        congrArg (afterReply req false) h
    · apply ihr
      simpa only [afterReply_outcomesWith_proof, ite_true] using congrArg (afterReply req true) h

theorem afterReply_outcomes_proof {A : Type} (a : A) (request right : Bool) (l r : Normal) :
    afterReply request right ((Normal.ask request l r).outcomes a) =
      (if right then r else l).outcomes a :=
  afterReply_outcomesWith_proof (fun _ => a) request right l r

theorem outcomes_injective_proof {A : Type} (a : A) :
    Function.Injective (Normal.outcomes a) :=
  outcomesWith_injective_proof (fun _ => a) (by intro x y _; exact Subsingleton.elim x y)

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply
