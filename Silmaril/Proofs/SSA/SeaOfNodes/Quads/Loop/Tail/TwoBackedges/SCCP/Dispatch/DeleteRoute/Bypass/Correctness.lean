module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Proofs

open Diamond (Model Signature ValueSort dataPorts sortValue)
open Diamond.SCCP (Fact TupleCovers)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open Blocks (Bank)
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}
variable {m : Model.{u, v, w} Op} {p : Program Op regs out}
variable {concrete : Bank (regs := regs) m}

private theorem header_return_iff (extra : Nat)
    (run : Nat → Bank (regs := regs) m → Option (sortValue m.value out))
    (zero : ∀ old, run 0 old = none)
    (step : ∀ fuel {via count old}, p.Arrives m concrete via count old →
      run (fuel + 1) old =
        match p.step m old with
        | .inl value => some value
        | .inr (_, next) => run (fuel - extra) next)
    (fuel : Nat) {via : Incoming} {count : Nat} {old : Bank (regs := regs) m}
    (arrived : p.Arrives m concrete via count old) (result : sortValue m.value out) :
    run fuel old = some result ↔ ∃ n, ReturnsAfter p m n old result ∧ (extra + 1) * n + 1 ≤ fuel := by
  induction fuel using Nat.strong_induction_on generalizing via count old with
  | ind fuel smaller =>
    cases fuel with
    | zero =>
      rw [zero]
      exact ⟨by simp, by rintro ⟨n, _, budget⟩; omega⟩
    | succ fuel =>
      rw [step fuel arrived]
      cases taken : p.step m old with
      | inl value =>
        constructor
        · intro same
          cases same
          exact ⟨0, .exit taken, by simp⟩
        · rintro ⟨n, trace, _⟩
          cases trace with
          | exit actual =>
            rw [taken] at actual
            cases actual
            rfl
          | feedback actual _ => rw [taken] at actual; cases actual
      | inr tagged =>
        obtain ⟨side, next⟩ := tagged
        rw [smaller (fuel - extra) (by omega) (.feedback arrived taken)]
        constructor
        · rintro ⟨n, trace, budget⟩
          refine ⟨n + 1, .feedback taken trace, ?_⟩
          rw [Nat.mul_succ]
          omega
        · rintro ⟨n, trace, budget⟩
          cases trace with
          | exit actual => rw [taken] at actual; cases actual
          | feedback actual rest =>
            rw [taken] at actual
            cases actual
            refine ⟨_, rest, ?_⟩
            rw [Nat.mul_succ] at budget
            omega

private theorem entry_return_iff (extra : Nat)
    (entryRun : Nat → Option (sortValue m.value out))
    (run : Nat → Bank (regs := regs) m → Option (sortValue m.value out))
    (entry_zero : entryRun 0 = none)
    (entry_step : ∀ fuel, entryRun (fuel + 1) = run fuel (p.preheader.eval m concrete))
    (zero : ∀ old, run 0 old = none)
    (step : ∀ fuel {via count old}, p.Arrives m concrete via count old →
      run (fuel + 1) old =
        match p.step m old with
        | .inl value => some value
        | .inr (_, next) => run (fuel - extra) next)
    (fuel : Nat) (result : sortValue m.value out) :
    entryRun fuel = some result ↔
      ∃ n, ReturnsAfter p m n (p.preheader.eval m concrete) result ∧ (extra + 1) * n + 2 ≤ fuel := by
  cases fuel with
  | zero =>
    rw [entry_zero]
    exact ⟨by simp, by rintro ⟨n, _, budget⟩; omega⟩
  | succ fuel =>
    rw [entry_step, header_return_iff extra run zero step fuel (.entry : p.Arrives m concrete _ _ _) result]
    constructor <;> rintro ⟨n, trace, budget⟩ <;> exact ⟨n, trace, by omega⟩

private theorem trace_unique {old : Bank (regs := regs) m} {n k : Nat}
    {a b : sortValue m.value out}
    (first : ReturnsAfter p m n old a) (second : ReturnsAfter p m k old b) :
    n = k ∧ a = b := by
  induction first generalizing k with
  | exit taken =>
    cases second with
    | exit actual => exact ⟨rfl, Sum.inl.inj (taken.symm.trans actual)⟩
    | feedback actual _ => cases taken.symm.trans actual
  | feedback taken _ ih =>
    cases second with
    | exit actual => cases taken.symm.trans actual
    | feedback actual rest =>
      cases Sum.inr.inj (taken.symm.trans actual)
      obtain ⟨count, value⟩ := ih rest
      exact ⟨congrArg (· + 1) count, value⟩

private theorem result_at (observed : Option (sortValue m.value out)) (cost fuel : Nat)
    (spec : ∀ value, observed = some value ↔
      ∃ n, ReturnsAfter p m n (p.preheader.eval m concrete) value ∧ cost * n + 2 ≤ fuel)
    {n : Nat} {result : sortValue m.value out}
    (trace : ReturnsAfter p m n (p.preheader.eval m concrete) result) :
    observed = if cost * n + 2 ≤ fuel then some result else none := by
  by_cases enough : cost * n + 2 ≤ fuel
  · simp only [enough, ite_true]
    exact (spec result).mpr ⟨n, trace, enough⟩
  · simp only [enough, ite_false]
    cases actual : observed with
    | none => rfl
    | some value =>
      obtain ⟨count, seen, bound⟩ := (spec value).mp actual
      have same := (trace_unique trace seen).1
      exact False.elim (enough (same.symm ▸ bound))

variable [BankDecidableEq m.value (dataPorts regs)]
variable {input : Tuple (Fact m.value) (dataPorts regs)}

theorem bypass_header (checked : Checked m p input) (covered : TupleCovers input concrete)
    (fuel : Nat) {via : Incoming} {count : Nat} {old : Bank (regs := regs) m}
    (arrived : p.Arrives m concrete via count old) :
    (bypass checked).runFrom m (fuel + 1) 1 old =
      match p.step m old with
      | .inl value => some value
      | .inr (_, next) => (bypass checked).runFrom m (fuel - 1) 1 next := by
  let current := p.header.eval m old
  have header : (bypass checked).runFrom m (fuel + 1) 1 old =
      if (current.get p.again).down then (bypass checked).runFrom m fuel 2 current
      else some (current.get p.result) := by
    simp only [Tail.Source.runFrom,
      show bypass checked 1 = ⟨p.header, .branch p.again (.jump 2) (.ret p.result)⟩ from rfl,
      Tail.Terminator.select, current]
    by_cases next : ((p.header.eval m old).get p.again).down = true <;> simp [next]
  rw [header]
  by_cases continues : (current.get p.again).down = true
  · rw [DeleteRoute.feedback_arrival checked covered arrived continues]
    simp only [continues, ite_true]
    cases fuel <;> rfl
  · have stopped : p.step m old = .inl (current.get p.result) := by
      simp [Program.step, current, continues]
    rw [stopped]
    simp [continues]

theorem run_bypass_iff (checked : Checked m p input) (covered : TupleCovers input concrete)
    (fuel : Nat) (result : sortValue m.value out) :
    (bypass checked).runFrom m fuel 0 concrete = some result ↔
      ∃ n, ReturnsAfter p m n (p.preheader.eval m concrete) result ∧ 2 * n + 2 ≤ fuel :=
  entry_return_iff (concrete := concrete) 1 (fun fuel => (bypass checked).runFrom m fuel 0 concrete)
    (fun fuel bank => (bypass checked).runFrom m fuel 1 bank) rfl (fun _ => rfl) (fun _ => rfl)
    (fun fuel {_via _count _old} arrived => bypass_header checked covered fuel arrived) fuel result

theorem run_compact_iff (checked : Checked m p input) (covered : TupleCovers input concrete)
    (fuel : Nat) (result : sortValue m.value out) :
    (compact checked).runFrom m fuel 0 concrete = some result ↔
      ∃ n, ReturnsAfter p m n (p.preheader.eval m concrete) result ∧ 3 * n + 2 ≤ fuel := by
  rw [DeleteRoute.runFrom_eq checked covered]
  exact entry_return_iff (concrete := concrete) 2 (fun fuel => p.source.runFrom m fuel 0 concrete)
    (fun fuel bank => p.source.runFrom m fuel 1 bank)
    rfl (fun fuel => p.source_entry m fuel concrete) (fun _ => rfl)
    (fun fuel {_via _count old} _ => p.source_header m fuel old) fuel result

theorem return_budgets (checked : Checked m p input) (covered : TupleCovers input concrete)
    {count : Nat} {result : sortValue m.value out}
    (trace : ReturnsAfter p m count (p.preheader.eval m concrete) result) (fuel : Nat) :
    (compact checked).runFrom m fuel 0 concrete = (if 3 * count + 2 ≤ fuel then some result else none) ∧
      (bypass checked).runFrom m fuel 0 concrete = (if 2 * count + 2 ≤ fuel then some result else none) :=
  ⟨result_at _ 3 fuel (run_compact_iff checked covered fuel) trace,
    result_at _ 2 fuel (run_bypass_iff checked covered fuel) trace⟩

theorem feedback_budget_eq (checked : Checked m p input) (covered : TupleCovers input concrete) (limit : Nat) :
    (bypass checked).runFrom m (2 * limit + 2) 0 concrete =
      (compact checked).runFrom m (3 * limit + 2) 0 concrete := by
  apply Option.eq_of_eq_some
  intro result
  rw [run_bypass_iff checked covered, run_compact_iff checked covered]
  constructor <;> rintro ⟨count, trace, budget⟩ <;> exact ⟨count, trace, by omega⟩

theorem returns_iff (checked : Checked m p input) (covered : TupleCovers input concrete)
    (result : sortValue m.value out) :
    (∃ fuel, (bypass checked).runFrom m fuel 0 concrete = some result) ↔
      ∃ fuel, (compact checked).runFrom m fuel 0 concrete = some result := by
  constructor
  · rintro ⟨fuel, returned⟩
    obtain ⟨count, trace, _⟩ := (run_bypass_iff checked covered fuel result).mp returned
    exact ⟨3 * count + 2, (run_compact_iff checked covered _ result).mpr ⟨count, trace, le_rfl⟩⟩
  · rintro ⟨fuel, returned⟩
    obtain ⟨count, trace, _⟩ := (run_compact_iff checked covered fuel result).mp returned
    exact ⟨2 * count + 2, (run_bypass_iff checked covered _ result).mpr ⟨count, trace, le_rfl⟩⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Proofs
