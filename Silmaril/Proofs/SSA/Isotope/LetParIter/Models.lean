module

public import Silmaril.SSA.Isotope.LetParIter.Models.Defs

/-! Denotation calculations for the typed example programs. -/

public section

-- The calculations reduce interpreted type codes to their concrete Lean types.
set_option backward.isDefEq.respectTransparency false

namespace Silmaril.Isotope.LetParIter.Proofs.Models

open scoped Silmaril.Elgot.Nondet

namespace ReadOnly

open LetParIter.Models.ReadOnly

theorem readPair_mem (r : Env) (a b : Nat) :
    (a, b) ∈ (LetParIter.Models.ReadOnly.denote readPair PUnit.unit PUnit.unit).run r ↔
      a ∈ r.1 ∧ b ∈ r.2 := by
  simp only [LetParIter.Models.ReadOnly.denote, readPair, LetParIter.denote, Parallel.evalPar]
  change (a, b) ∈ id <$> Elgot.Part.parallelPairing.pair
    ((pure () : Part Unit) >>= fun _ => r.1) ((pure () : Part Unit) >>= fun _ => r.2) ↔ _
  simp only [pure_bind, id_map, Elgot.Part.mem_pair]

private def body (right : Part Nat) : Nat → Part (Nat ⊕ Nat)
  | 0 => Sum.inl <$> right
  | n + 1 => Part.some (.inr n)

private theorem iter_body (right : Part Nat) (n : Nat) : Elgot.iter (body right) n = right := by
  induction n with
  | zero =>
      rw [congrFun (Elgot.Part.fixpoint (body right)) 0]
      simp only [body, ← bind_pure_comp, bind_assoc, pure_bind, Sum.elim_inl, bind_pure]
  | succ n ih =>
      rw [congrFun (Elgot.Part.fixpoint (body right)) (n + 1)]
      change ((pure (.inr n) : Part (Nat ⊕ Nat)) >>= Sum.elim pure (Elgot.iter (body right))) = right
      simpa only [pure_bind, Sum.elim_inr] using ih

private theorem seed_run (r : Env) :
    (LetParIter.Models.ReadOnly.denote countSeed PUnit.unit PUnit.unit).run r = r.1 := by
  simp only [LetParIter.Models.ReadOnly.denote, countSeed, LetParIter.denote]
  change ((pure () : Part Unit) >>= fun _ => r.1) = _
  rw [pure_bind]

private theorem step_run (r : Env) (n : Nat) :
    (LetParIter.Models.ReadOnly.denote countStep PUnit.unit (PUnit.unit, n)).run r = body r.2 n := by
  simp only [LetParIter.Models.ReadOnly.denote, countStep, LetParIter.denote]
  rw [_root_.ReaderT.run_bind, _root_.ReaderT.run_bind, _root_.ReaderT.run_pure, pure_bind]
  change ((pure (countdown n) : Part (Nat ⊕ Nat)) >>= _) = _
  rw [pure_bind]
  cases n with
  | zero =>
      change (((pure () : Part Unit) >>= (fun _ => r.2)) >>= fun b => pure (Sum.inl b)) = _
      rw [pure_bind, bind_pure_comp]
      rfl
  | succ n =>
      change ((pure n : Part Nat) >>= fun k => pure (Sum.inr k)) = _
      rw [pure_bind]
      rfl

theorem countAndRead_run (r : Env) :
    (LetParIter.Models.ReadOnly.denote countAndRead PUnit.unit PUnit.unit).run r =
      (r.1 >>= fun _ => r.2) := by
  simp only [LetParIter.Models.ReadOnly.denote, countAndRead, LetParIter.denote, Parallel.evalIter]
  change ((LetParIter.Models.ReadOnly.denote countSeed PUnit.unit PUnit.unit).run r >>=
    Elgot.iter (fun n : Nat =>
      (LetParIter.Models.ReadOnly.denote countStep PUnit.unit (PUnit.unit, n)).run r >>= pure)) = _
  simp only [seed_run, bind_pure, step_run]
  exact bind_congr (iter_body r.2)

end ReadOnly

namespace Choice

open LetParIter.Models.Choice

open Elgot

theorem choosePair_mem (a b c d x y : Nat) :
    (x, y) ∈ₘ LetParIter.Models.Choice.denote (choosePair a b c d) PUnit.unit PUnit.unit ↔
      (x = a ∨ x = b) ∧ (y = c ∨ y = d) := by
  simp only [LetParIter.Models.Choice.denote, choosePair, LetParIter.denote, Parallel.evalPar]
  change (x, y) ∈ₘ id <$> Nondet.parallelPairing.pair
    ((pure () : SetM Unit) >>= fun _ => (show SetM Nat from ({a, b} : Set Nat)))
    ((pure () : SetM Unit) >>= fun _ => (show SetM Nat from ({c, d} : Set Nat))) ↔ _
  simp only [pure_bind, id_map, Nondet.mem_pair]
  change x ∈ ({a, b} : Set Nat) ∧ y ∈ ({c, d} : Set Nat) ↔ _
  simp

private theorem step_return {n b : Nat} (h : Sum.inl b ∈ₘ step n) : b = 10 ∨ b = 20 := by
  change Sum.inl b ∈ ({Sum.inl (if n = 0 then 10 else 20), Sum.inr 0} : Set (Nat ⊕ Nat)) at h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sum.inl.injEq,
    reduceCtorEq, or_false] at h
  split at h <;> simp [h]

private theorem runs_return {n b : Nat} (h : Nondet.Runs step n b) : b = 10 ∨ b = 20 := by
  induction h with
  | done h => exact step_return h
  | more _ _ ih => exact ih

private theorem seed_denote :
    LetParIter.Models.Choice.denote chooseSeed PUnit.unit PUnit.unit = ({1, 2} : Set Nat) := by
  simp only [LetParIter.Models.Choice.denote, chooseSeed, LetParIter.denote]
  change ((pure () : SetM Unit) >>= fun _ => (show SetM Nat from ({1, 2} : Set Nat))) = _
  rw [pure_bind]

private theorem step_denote (n : Nat) :
    LetParIter.Models.Choice.denote chooseStep PUnit.unit (PUnit.unit, n) = step n := by
  simp only [LetParIter.Models.Choice.denote, chooseStep, LetParIter.denote]
  change (((pure n : SetM Nat) >>= step) >>= _) = _
  rw [pure_bind]
  conv_rhs => rw [← bind_pure (step n)]
  apply bind_congr
  intro s
  cases s with
  | inl a =>
      change ((pure a : SetM Nat) >>= fun b => pure (Sum.inl b)) = _
      rw [pure_bind]
  | inr a =>
      change ((pure a : SetM Nat) >>= fun b => pure (Sum.inr b)) = _
      rw [pure_bind]

theorem chooseLoop_outcomes :
    LetParIter.Models.Choice.denote chooseLoop PUnit.unit PUnit.unit = ({10, 20} : Set Nat) := by
  simp only [LetParIter.Models.Choice.denote, chooseLoop, LetParIter.denote, Parallel.evalIter]
  change (LetParIter.Models.Choice.denote chooseSeed PUnit.unit PUnit.unit >>=
    Elgot.iter (fun n : Nat =>
      LetParIter.Models.Choice.denote chooseStep PUnit.unit (PUnit.unit, n) >>= pure)) = _
  simp only [seed_denote, bind_pure, step_denote]
  apply Nondet.ext
  intro b
  rw [Nondet.mem_bind_iff]
  change (∃ n, n ∈ ({1, 2} : Set Nat) ∧ Nondet.Runs step n b) ↔ b ∈ ({10, 20} : Set Nat)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  refine ⟨fun ⟨_, _, hrun⟩ => runs_return hrun, ?_⟩
  rintro (rfl | rfl)
  · exact ⟨1, Or.inl rfl, .more (Or.inr rfl) (.done (Or.inl rfl))⟩
  · exact ⟨2, Or.inr rfl, .done (Or.inl rfl)⟩

end Choice

end Silmaril.Isotope.LetParIter.Proofs.Models
