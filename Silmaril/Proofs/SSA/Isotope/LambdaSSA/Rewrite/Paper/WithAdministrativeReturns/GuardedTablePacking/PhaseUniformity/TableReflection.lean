module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.TableMorphism
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.ClassSeparation

/-! # Complete runs of a table of polls determine its stream of polls -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.TableModel

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithAdministrativeReturns
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open Paper.WithCaseBind.BitQuery (signature Trace model modelCoherent Event)
open Paper.WithCaseBind.BitQuery.RequestTree
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value instructions)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit bit)
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Semantics.NondeterministicTrace (Tagged)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop

local notation "J" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.J (m := Trace)
local notation "M" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.types

noncomputable local instance : InstructionModel J M signature.Instr := instructions model
local instance : RegionTypingCoherent (Φ := signature.Instr) J M := modelCoherent

set_option backward.isDefEq.respectTransparency false

theorem poll_ext {a b : Poll} (hl : a.label = b.label) (hr : a.returnRight = b.returnRight) : a = b := by
  cases a
  cases b
  cases hl
  cases hr
  rfl

theorem tag_of_repeat {rr tag pl : Bool} {s : value State}
    (h : (Except.ok (Sum.inr s) : Except Bool (value Bit ⊕ value State)) =
      .ok (terminal (if tag then !rr else rr) pl)) : tag = !rr := by
  cases tag <;> cases rr <;> first | rfl | cases h

/-- A poll row has one event. Its reply tag says whether the row returned
or repeated, and a repeat goes to the row's successor. -/
theorem poll_step_cases {K : Nat} (t : Table K) (i : Fin (K + 1)) (a : Poll) (h : t.prog i = a.program)
    (g : Bool) {y : Except Bool (value Bit ⊕ value (States K))} {w : Word}
    (hm : (y, w) ∈ (t.stepM (injVal K i (Sum.inl (bit g)))).outcomes) :
    ∃ tag pl, w = FreeMonoid.of (event a.label g (tag, pl)) ∧
      ((tag = a.returnRight ∧ ∃ b, y = .ok (Sum.inl b)) ∨
        (tag = !a.returnRight ∧ ∃ s', y = .ok (Sum.inr (injVal K (t.next i) s')))) := by
  rw [step_run, h, Tagged.mem_bind] at hm
  rcases hm with ⟨t', rfl, ht⟩ | ⟨x, u, v, hx, hk, rfl⟩
  · rw [WithGuardedTablePacking.BitLoop.stepModel_outcomes] at ht
    obtain ⟨tag, pl, hy, -⟩ := (poll_outcomes a g _ _).1 ht
    cases hy
  · rw [WithGuardedTablePacking.BitLoop.stepModel_outcomes] at hx
    obtain ⟨tag, pl, hy, rfl⟩ := (poll_outcomes a g _ _).1 hx
    rcases x with b | s
    · obtain ⟨rfl, rfl⟩ := mem_pure.1 hk
      exact ⟨tag, pl, mul_one _, .inl ⟨tag_of_return hy, b, rfl⟩⟩
    · obtain ⟨rfl, rfl⟩ := mem_pure.1 hk
      exact ⟨tag, pl, mul_one _, .inr ⟨tag_of_repeat hy, s, rfl⟩⟩

variable {K : Nat} (poll : Fin (K + 1) → Poll) (next : Fin (K + 1) → Fin (K + 1))

/-- Every complete run of a table of polls has a trail as its request word. -/
theorem trail_of_obs (i : Fin (K + 1)) (g : Bool) {obs : Except Bool (value Bit) × Word}
    (h : obs ∈ (Table.ofPolls poll next).observations i g) :
    Table.Trail poll next i (FreeMonoid.toList obs.2) := by
  rw [observations_eq] at h
  refine iter_induction (Table.ofPolls poll next).stepM
    (fun v => {obs | ∀ i s, v = injVal K i s → Table.Trail poll next i (FreeMonoid.toList obs.2)})
    ?_ ?_ ?_ _ h i _ rfl
  · intro v t' w hw i s hv
    subst hv
    obtain ⟨g, rfl⟩ := state_cases s
    obtain ⟨tag, pl, -, hc⟩ := poll_step_cases (Table.ofPolls poll next) i (poll i) rfl g hw
    rcases hc with ⟨-, b, hb⟩ | ⟨-, s', hs⟩
    · cases hb
    · cases hs
  · intro v b w hw i s hv
    subst hv
    obtain ⟨g, rfl⟩ := state_cases s
    obtain ⟨tag, pl, rfl, hc⟩ := poll_step_cases (Table.ofPolls poll next) i (poll i) rfl g hw
    rcases hc with ⟨ht, -⟩ | ⟨-, s', hs⟩
    · exact ⟨rfl, .inl ⟨ht, rfl⟩⟩
    · cases hs
  · intro v nxt u r v' hu hv i s hvi
    subst hvi
    obtain ⟨g, rfl⟩ := state_cases s
    obtain ⟨tag, pl, rfl, hc⟩ := poll_step_cases (Table.ofPolls poll next) i (poll i) rfl g hu
    rcases hc with ⟨-, b, hb⟩ | ⟨ht, s', hs⟩
    · cases hb
    · cases hs
      exact ⟨rfl, .inr ⟨ht, hv (next i) s' rfl⟩⟩

/-- The run that repeats `n` times and then returns is a complete run. -/
theorem run_mem : ∀ (n : Nat) (i : Fin (K + 1)) (g : Bool),
    (Except.ok (bit false), Table.runWord poll next n i g) ∈ (Table.ofPolls poll next).observations i g
  | 0, i, g => by
    rw [observations_eq, iter_unfold]
    refine .inr (.inl ⟨bit false, rfl, ?_⟩)
    rw [step_run, Tagged.mem_bind]
    refine .inr ⟨Sum.inl (bit false), _, 1, ?_, mem_pure.2 ⟨rfl, rfl⟩, mul_one _⟩
    rw [WithGuardedTablePacking.BitLoop.stepModel_outcomes]
    exact (poll_outcomes (poll i) g _ _).2 ⟨(poll i).returnRight, false, by rw [flag_self]; rfl, rfl⟩
  | n + 1, i, g => by
    have tail := run_mem n (next i) false
    rw [observations_eq] at tail
    rw [observations_eq, iter_unfold]
    refine .inr (.inr ⟨injVal K (next i) (Sum.inl (bit false)), _, _, ?_, tail, rfl⟩)
    rw [step_run, Tagged.mem_bind]
    refine .inr ⟨Sum.inr (Sum.inl (bit false)), _, 1, ?_, mem_pure.2 ⟨rfl, rfl⟩, mul_one _⟩
    rw [WithGuardedTablePacking.BitLoop.stepModel_outcomes]
    exact (poll_outcomes (poll i) g _ _).2 ⟨!(poll i).returnRight, false, by rw [flag_not]; rfl, rfl⟩

theorem runWord_ne_nil : ∀ (n : Nat) (i : Fin (K + 1)) (g : Bool),
    FreeMonoid.toList (Table.runWord poll next n i g) ≠ []
  | 0, _, _ => List.cons_ne_nil _ _
  | _ + 1, _, _ => List.cons_ne_nil _ _

variable {K' : Nat} (poll' : Fin (K' + 1) → Poll) (next' : Fin (K' + 1) → Fin (K' + 1))

/-- If the word of the `n`-repeat run of one table is a trail of another,
the two tables run the same poll in round `n`. -/
theorem poll_of_trail : ∀ (n : Nat) (i : Fin (K + 1)) (i' : Fin (K' + 1)) (g : Bool),
    Table.Trail poll' next' i' (FreeMonoid.toList (Table.runWord poll next n i g)) →
    poll (next^[n] i) = poll' (next'^[n] i')
  | 0, i, i', g, h => by
    have h' : (poll i).label = (poll' i').label ∧
        (((poll i).returnRight = (poll' i').returnRight ∧ ([] : List Event) = []) ∨
          ((poll i).returnRight = !(poll' i').returnRight ∧ Table.Trail poll' next' (next' i') [])) := h
    rcases h' with ⟨hl, ⟨hr, -⟩ | ⟨-, bad⟩⟩
    · exact poll_ext hl hr
    · exact bad.elim
  | n + 1, i, i', g, h => by
    have h' : (poll i).label = (poll' i').label ∧
        (((!(poll i).returnRight) = (poll' i').returnRight ∧
            FreeMonoid.toList (Table.runWord poll next n (next i) false) = []) ∨
          ((!(poll i).returnRight) = !(poll' i').returnRight ∧
            Table.Trail poll' next' (next' i') (FreeMonoid.toList (Table.runWord poll next n (next i) false)))) := h
    rcases h' with ⟨-, ⟨-, empty⟩ | ⟨-, tail⟩⟩
    · exact (runWord_ne_nil poll next n (next i) false empty).elim
    · exact poll_of_trail n (next i) (next' i') false tail

/-- Equal complete runs give equal streams of polls. -/
theorem polls_of_observations (i : Fin (K + 1)) (i' : Fin (K' + 1))
    (h : (Table.ofPolls poll next).observations i false = (Table.ofPolls poll' next').observations i' false)
    (n : Nat) : poll (next^[n] i) = poll' (next'^[n] i') := by
  have mem := run_mem poll next n i false
  rw [h] at mem
  exact poll_of_trail poll next poll' next' n i i' false (trail_of_obs poll' next' i' false mem)

theorem observations_of_valid {K₁ K₂ : Nat} {t : Table K₁} {t' : Table K₂} {i : Fin (K₁ + 1)}
    {i' : Fin (K₂ + 1)} (h : WithGuardedTablePacking.Valid (t.entered_typed i).hasType (t'.entered_typed i').hasType) (g : Bool) :
    t.observations i g = t'.observations i' g := by
  have eq := h J M (fun _ _ => ⟨rfl, rfl⟩)
  unfold Table.observations denoteSingletonRegion
  rw [eq]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.TableModel
