module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.Model
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.Reduction

/-! # Congruence, soundness and the polling fragment of live Bit loops -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithAdministrativeReturns
open Paper.WithAdministrativeReturns.WithGuardedTablePacking (Valid)
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open Paper.WithCaseBind.BitQuery (signature Exits model Trace modelCoherent Event)
open Paper.WithCaseBind.BitQuery.RequestTree
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
  (packedReadbackRep)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value instructions)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit bit answer)
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Paper.Extension.Singleton (ofRegion ofType ofRegion_eq_iff)
open Silmaril.Semantics.NondeterministicTrace (Tagged Finite)
open CategoryTheory

local notation "J" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.J (m := Trace)
local notation "M" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.types
noncomputable local instance : InstructionModel J M signature.Instr := instructions model
local instance : RegionTypingCoherent (Φ := signature.Instr) J M := modelCoherent
local notation "N" => WithGuardedTablePacking.Step (τ := Ty Empty) (Φ := signature.Instr) false

set_option backward.isDefEq.respectTransparency false

section Monad

variable {A B : Type}

theorem mem_pure {b : B} {r : Except Bool B} {v : Word} :
    (r, v) ∈ (pure b : Trace B).outcomes ↔ r = .ok b ∧ v = 1 := by
  change (r, v) ∈ ({(Except.ok b, 1)} : Set (Except Bool B × Word)) ↔ _
  simp only [Set.mem_singleton_iff, Prod.mk.injEq]

/-- One unfolding of the iterator on complete observations. -/
theorem iter_unfold (f : A → Trace (B ⊕ A)) (a : A) {r : Except Bool B} {w : Word} :
    (r, w) ∈ (Silmaril.Elgot.iter f a).outcomes ↔
      (∃ t, r = .error t ∧ (.error t, w) ∈ (f a).outcomes) ∨
      (∃ b, r = .ok b ∧ (.ok (Sum.inl b), w) ∈ (f a).outcomes) ∨
      ∃ next u v, (.ok (Sum.inr next), u) ∈ (f a).outcomes ∧
        (r, v) ∈ (Silmaril.Elgot.iter f next).outcomes ∧ u * v = w := by
  have fx : Silmaril.Elgot.iter f a = f a >>= Sum.elim pure (Silmaril.Elgot.iter f) :=
    congrFun (Silmaril.Elgot.ExceptT.fixpoint f) a
  rw [fx, Tagged.mem_bind]
  constructor
  · rintro (err | ⟨x, u, v, hx, hk, rfl⟩)
    · exact .inl err
    · rcases x with b | next
      · obtain ⟨rfl, rfl⟩ := mem_pure.1 hk
        exact .inr (.inl ⟨b, rfl, (mul_one u).symm ▸ hx⟩)
      · exact .inr (.inr ⟨next, u, v, hx, hk, rfl⟩)
  · rintro (err | ⟨b, rfl, hb⟩ | ⟨next, u, v, hx, hk, rfl⟩)
    · exact .inl err
    · exact .inr ⟨.inl b, w, 1, hb, mem_pure.2 ⟨rfl, rfl⟩, mul_one w⟩
    · exact .inr ⟨.inr next, u, v, hx, hk, rfl⟩

/-- Complete observations of the iterator satisfy every invariant closed
under one step. -/
theorem iter_induction (f : A → Trace (B ⊕ A)) (K : A → Set (Except Bool B × Word))
    (error : ∀ a t w, (Except.error t, w) ∈ (f a).outcomes → (Except.error t, w) ∈ K a)
    (ret : ∀ a b w, (Except.ok (Sum.inl b), w) ∈ (f a).outcomes → (Except.ok b, w) ∈ K a)
    (again : ∀ a next u r v, (Except.ok (Sum.inr next), u) ∈ (f a).outcomes →
      (r, v) ∈ K next → (r, u * v) ∈ K a)
    (a : A) : (Silmaril.Elgot.iter f a).outcomes ⊆ K a := by
  have least : (Finite.unfoldLoop (Silmaril.Elgot.ExceptT.body f)).lfp ≤ K := by
    apply OrderHom.lfp_le
    intro a ⟨r, w⟩ h
    rw [Tagged.unfold_eq_bind, Tagged.mem_bind] at h
    rcases h with ⟨t, rfl, ht⟩ | ⟨x, u, v, hx, hk, rfl⟩
    · exact error a t w ht
    · rcases x with b | next
      · obtain ⟨rfl, rfl⟩ := mem_pure.1 hk
        exact (mul_one u).symm ▸ ret a b u hx
      · exact again a next u r v hx hk
  intro obs h
  exact least a (congrFun (Tagged.iter_eq_lfp f) a ▸ h)

end Monad

theorem of_mul_ne_one (e : Event) (t : Word) : FreeMonoid.of e * t ≠ 1 := by
  intro h
  have l := congrArg FreeMonoid.toList h
  simp at l

theorem of_eq_of_mul {x y : Event} {t : Word} (h : FreeMonoid.of x = FreeMonoid.of y * t) :
    x = y ∧ t = 1 := by
  have l : [x] = y :: FreeMonoid.toList t := by simpa using congrArg FreeMonoid.toList h
  obtain ⟨rfl, nil⟩ := List.cons.inj l
  exact ⟨rfl, by simpa using congrArg FreeMonoid.ofList nil.symm⟩

theorem state_cases (s : value State) : ∃ g, s = Sum.inl (bit g) := by
  rcases s with (x | x) | e
  · exact ⟨false, rfl⟩
  · exact ⟨true, rfl⟩
  · exact e.elim

/-! ## Congruence and soundness -/

theorem packed_of_key {p q : Program} (h : p.tree.key = q.tree.key) :
    ofRegion N p.typed.packExits = ofRegion N q.typed.packExits :=
  congrArg (WithGuardedTablePacking.fromAdministrativeReturns false).map ((p.packed_eq_iff_key q).2 h)

theorem step_of_key {p q : Program} (h : p.tree.key = q.tree.key) : stepArrow p = stepArrow q := by
  rw [stepArrow_eq, stepArrow_eq, packed_of_key h]

theorem key_of_step {p q : Program} (h : stepArrow p = stepArrow q) : p.tree.key = q.tree.key := by
  have same : ∀ s, stepModel p s = stepModel q s := by
    intro s
    rw [← step_run p s, ← step_run q s, h]
  apply key_of_outcomes
  intro env
  have all : env = fun _ : Fin 1 => env 0 := funext fun i => congrArg env (Fin.eq_zero i)
  rw [all, ← stepModel_outcomes, ← stepModel_outcomes, same]

theorem loop_of_key {p q : Program} (h : p.tree.key = q.tree.key) :
    WithGuardedTablePacking.Eqv false [State] (loopRegion p) (loopRegion q) [Bit] := by
  apply (ofRegion_eq_iff N (loop_typed p) (loop_typed q)).1
  change loopArrow p = loopArrow q
  rw [loopArrow_eq, loopArrow_eq, step_of_key h]

theorem observations_of_valid {p q : Program}
    (h : Valid (loop_typed p).hasType (loop_typed q).hasType) (g : Bool) :
    loopObservations p g = loopObservations q g := by
  have eq := h J M (fun _ _ => ⟨rfl, rfl⟩)
  unfold loopObservations denoteSingletonRegion
  rw [eq]

theorem observations_of_eqv {p q : Program}
    (h : WithGuardedTablePacking.Eqv false [State] (loopRegion p) (loopRegion q) [Bit]) (g : Bool) :
    loopObservations p g = loopObservations q g :=
  observations_of_valid (valid_of_eqv false h _ _) g

/-- The literal loop is a one-row guarded table, so it has a packed
single-feedback dispatcher in this quotient. -/
theorem loop_packed (p : Program) :
    ∃ (R : Fin 1 → Ty Empty) (e : Region signature.Instr) (blocks : Fin 1 → Region signature.Instr)
      (he : ValueBranches [State] e (List.ofFn R ++ [Bit]))
      (hb : ∀ i, ValueBranches [R i, State] (blocks i) (List.ofFn R ++ [Bit])),
      loopRegion p = .cfg e 1 blocks ∧
        WithGuardedTablePacking.Eqv false [State] (loopRegion p) (packedReadbackRep R he hb).val [Bit] := by
  obtain ⟨e, blocks, table⟩ : ∃ e blocks, loopRegion p = Region.cfg e 1 blocks := ⟨_, _, rfl⟩
  have typed := loop_typed p
  rw [table] at typed
  cases typed with
  | cfg R he hb =>
    refine ⟨R, e, blocks, he, hb, table, ?_⟩
    rw [table]
    exact WithGuardedTablePacking.pack false R he hb

/-! ## Trees of polls and spinning programs -/

theorem terminal_false (b : Bool) : terminal false b = (Sum.inl (bit b) : value Bit ⊕ value State) := rfl

theorem terminal_true (b : Bool) :
    terminal true b = (Sum.inr (Sum.inl (bit b)) : value Bit ⊕ value State) := rfl

theorem ask_leaf_outcomes (l fl fr g : Bool) (y : Except Bool Result) (u : Word) :
    (y, u) ∈ (Tree.ask l (.read 0) (.ret fl 0) (.ret fr 0) : Tree 1).outcomes (fun _ => g) ↔
      ∃ tag pl, y = .ok (terminal (if tag then fr else fl) pl) ∧
        u = FreeMonoid.of (event l g (tag, pl)) := by
  constructor
  · rintro ⟨⟨tag, pl⟩, tail, hmem, hw⟩
    cases tag
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (show (y, tail) = (.ok (terminal fl pl), 1) from hmem)
      exact ⟨false, pl, rfl, hw.symm.trans (mul_one _)⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (show (y, tail) = (.ok (terminal fr pl), 1) from hmem)
      exact ⟨true, pl, rfl, hw.symm.trans (mul_one _)⟩
  · rintro ⟨tag, pl, rfl, rfl⟩
    refine ⟨(tag, pl), 1, ?_, mul_one _⟩
    cases tag
    · exact (rfl : (Except.ok (terminal fl pl), (1 : Word)) = (Except.ok (terminal fl pl), 1))
    · exact (rfl : (Except.ok (terminal fr pl), (1 : Word)) = (Except.ok (terminal fr pl), 1))

theorem poll_tree (a : Poll) :
    a.program.tree = .ask a.label (.read 0) (.ret a.returnRight 0) (.ret (!a.returnRight) 0) := by
  obtain ⟨l, rr⟩ := a
  cases rr <;> rfl

theorem poll_outcomes (a : Poll) (g : Bool) (y : Except Bool Result) (u : Word) :
    (y, u) ∈ a.program.tree.outcomes (fun _ => g) ↔
      ∃ tag pl, y = .ok (terminal (if tag then !a.returnRight else a.returnRight) pl) ∧
        u = FreeMonoid.of (event a.label g (tag, pl)) := by
  rw [poll_tree]
  exact ask_leaf_outcomes _ _ _ _ _ _

theorem flag_self (rr : Bool) : (if rr then !rr else rr) = false := by cases rr <;> rfl

theorem flag_not (rr : Bool) : (if !rr then !rr else rr) = true := by cases rr <;> rfl

theorem tag_of_return {rr tag pl : Bool} {b : value Bit}
    (h : (Except.ok (Sum.inl b) : Except Bool (value Bit ⊕ value State)) =
      .ok (terminal (if tag then !rr else rr) pl)) : tag = rr := by
  cases tag <;> cases rr <;> first | rfl | cases h

/-! ## Polls -/

theorem oneRound (a : Poll) (g b : Bool) :
    (Except.ok (bit b), FreeMonoid.of (event a.label g (a.returnRight, b))) ∈
      loopObservations a.program g := by
  rw [loopObservations_eq, iter_unfold]
  refine .inr (.inl ⟨bit b, rfl, ?_⟩)
  rw [stepModel_outcomes]
  exact (poll_outcomes a g _ _).2 ⟨a.returnRight, b, by rw [flag_self]; rfl, rfl⟩

theorem twoRounds (a : Poll) (g s b : Bool) :
    (Except.ok (bit b), FreeMonoid.of (event a.label g (!a.returnRight, s)) *
      FreeMonoid.of (event a.label s (a.returnRight, b))) ∈ loopObservations a.program g := by
  rw [loopObservations_eq, iter_unfold]
  refine .inr (.inr ⟨Sum.inl (bit s), _, _, ?_, ?_, rfl⟩)
  · rw [stepModel_outcomes]
    exact (poll_outcomes a g _ _).2 ⟨!a.returnRight, s, by rw [flag_not]; rfl, rfl⟩
  · rw [← loopObservations_eq]
    exact oneRound a s b

/-- The first event of a complete run, and its tag when it is the only one. -/
def Head (a : Poll) (obs : Except Bool (value Bit) × Word) : Prop :=
  ∃ e tail, obs.2 = FreeMonoid.of e * tail ∧ e.label = a.label ∧ (tail = 1 → e.right = a.returnRight)

theorem head (a : Poll) (g : Bool) {obs : Except Bool (value Bit) × Word}
    (h : obs ∈ loopObservations a.program g) : Head a obs := by
  rw [loopObservations_eq] at h
  refine iter_induction (stepModel a.program) (fun _ => {obs | Head a obs}) ?_ ?_ ?_ _ h
  · intro s t w hw
    obtain ⟨g, rfl⟩ := state_cases s
    rw [stepModel_outcomes] at hw
    obtain ⟨tag, pl, hy, -⟩ := (poll_outcomes a g _ _).1 hw
    cases hy
  · intro s b w hw
    obtain ⟨g, rfl⟩ := state_cases s
    rw [stepModel_outcomes] at hw
    obtain ⟨tag, pl, hy, rfl⟩ := (poll_outcomes a g _ _).1 hw
    show Head a _
    exact ⟨event a.label g (tag, pl), 1, (mul_one _).symm, rfl, fun _ => tag_of_return hy⟩
  · intro s next u r v hu hv
    obtain ⟨g, rfl⟩ := state_cases s
    rw [stepModel_outcomes] at hu
    obtain ⟨tag, pl, -, rfl⟩ := (poll_outcomes a g _ _).1 hu
    obtain ⟨e, tail, hv, -, -⟩ := hv
    show Head a _
    exact ⟨event a.label g (tag, pl), v, rfl, rfl,
      fun one => (of_mul_ne_one e tail (hv.symm.trans one)).elim⟩

theorem poll_eq_of_observations {a b : Poll}
    (h : loopObservations a.program false = loopObservations b.program false) : a = b := by
  have mem := oneRound a false false
  rw [h] at mem
  obtain ⟨e, tail, hw, hl, hr⟩ := head b false mem
  obtain ⟨rfl, one⟩ := of_eq_of_mul hw
  obtain ⟨la, ra⟩ := a
  obtain ⟨lb, rb⟩ := b
  cases (show la = lb from hl)
  cases (show ra = rb from hr one)
  rfl

theorem spells_observations {p : Program} {a : Poll} (h : Spells p a) (g : Bool) :
    loopObservations p g = loopObservations a.program g :=
  observations_of_eqv (loop_of_key h) g

theorem key_of_observations {p q : Program} {a b : Poll} (hp : Spells p a) (hq : Spells q b)
    (h : ∀ g, loopObservations p g = loopObservations q g) : p.tree.key = q.tree.key := by
  have ab : a = b := poll_eq_of_observations
    ((spells_observations hp false).symm.trans ((h false).trans (spells_observations hq false)))
  subst ab
  exact hp.trans hq.symm

/-! ## Loops with no complete run -/

theorem empty_of_repeats (p : Program)
    (h : ∀ g y u, (y, u) ∈ p.tree.outcomes (fun _ => g) →
      ∃ s : value State, y = .ok (Sum.inr s : value Bit ⊕ value State))
    (g : Bool) : loopObservations p g = ∅ := by
  rw [loopObservations_eq]
  refine Set.eq_empty_of_subset_empty (iter_induction (stepModel p) (fun _ => ∅) ?_ ?_ ?_ _)
  · intro s t w hw
    obtain ⟨g, rfl⟩ := state_cases s
    rw [stepModel_outcomes] at hw
    obtain ⟨_, hy⟩ := h g _ _ hw
    cases hy
  · intro s b w hw
    obtain ⟨g, rfl⟩ := state_cases s
    rw [stepModel_outcomes] at hw
    obtain ⟨_, hy⟩ := h g _ _ hw
    cases hy
  · intro s next u r v _ hv
    exact hv.elim

theorem spin_tree : spin.tree = .ret true 0 := rfl

theorem askSpin_tree (l : Bool) : (askSpin l).tree = .ask l (.read 0) (.ret true 0) (.ret true 0) := rfl

theorem spin_observations (g : Bool) : loopObservations spin g = ∅ :=
  empty_of_repeats spin (fun g y u h =>
    ⟨Sum.inl (bit g), (Prod.mk.inj (show (y, u) = (.ok (terminal true g), 1) from h)).1⟩) g

theorem askSpin_observations (l g : Bool) : loopObservations (askSpin l) g = ∅ :=
  empty_of_repeats (askSpin l) (fun g y u h => by
    rw [askSpin_tree] at h
    obtain ⟨tag, pl, hy, -⟩ := (ask_leaf_outcomes _ _ _ _ _ _).1 h
    exact ⟨Sum.inl (bit pl), by cases tag <;> exact hy⟩) g

theorem askSpin_key_ne (l : Bool) : (askSpin l).tree.key ≠ spin.tree.key := by
  rw [askSpin_tree, spin_tree]
  intro h
  cases h

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop
