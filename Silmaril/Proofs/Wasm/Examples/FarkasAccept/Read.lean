module

public import Silmaril.Wasm.Examples.FarkasAccept.Defs
public import Silmaril.Logic.LinArith.Carrier.Thms
public import Silmaril.Wasm.Logic.Memory.Thms

@[expose] public section

/-!
# What the acceptor reads, and why the loaded rows refute the system

The acceptor feeds the inequalities of `systemAt B p n` to the checker in order, each as
`row(y, bound)` followed by `entry(j, a)` per coefficient pair; the checker prepends
(`Cmd.apply`), so each loaded row is an inequality of the system with its coefficients
reversed. `Sub S rs` records exactly this, for every row: whatever the multipliers are, the rows
the checker holds come from `S` (`Sub.cons`, `Sub.nil`). `infeasible_of_sub`: if they carry a
valid certificate (`WRows.IsCert`), then `S` has no solution over any ordered field
(`Infeasible`), since a solution of `S` would solve the loaded system (reversing a list of
coefficients does not change the sum).

The readings: `decC B p k` (the first `k` decoded pairs at `p`, `decC_succ`), `mem_systemAt`,
and the 64-bit words of memory (`load_dw`). A Silmaril addition.
-/

namespace Silmaril.Proofs.Wasm.Examples.FarkasAccept

open Silmaril.Wasm Silmaril.Wasm.Execution
open Silmaril.Wasm.Examples.FarkasAccept
open Silmaril.Logic.LinArith
open Silmaril.Logic.LinArith.Carrier

/-- The first `k` coefficient pairs at `p`, decoded (`IneqW.decode`). -/
def decC (B : ByteArray) (p k : Nat) : List (ℕ × ℤ) :=
  (coeffsAt B p k).map fun q => (q.1.toNat, q.2.toInt)

theorem decC_zero (B : ByteArray) (p : Nat) : decC B p 0 = [] := rfl

theorem decC_succ (B : ByteArray) (p k : Nat) :
    decC B p (k + 1) = decC B p k ++
      [((Silmaril.Wasm.Logic.Words.wd B (p + 16 * k)).toNat, (dw B (p + 16 * k + 8)).toInt)] := by
  simp [decC, coeffsAt, List.range_succ]

theorem decode_ineqAt (B : ByteArray) (a : Nat) :
    (ineqAt B a).decode = ⟨decC B (Silmaril.Wasm.Logic.Words.wd B a).toNat
      (Silmaril.Wasm.Logic.Words.wd B (a + 4)).toNat, (dw B (a + 8)).toInt⟩ := rfl

theorem mem_systemAt {B : ByteArray} {p n i : Nat} (hi : i < n) :
    ineqAt B (p + 16 * i) ∈ systemAt B p n :=
  List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩

/-- **The loaded rows come from `S`**: every row is an inequality of `S` with its coefficients
reversed. -/
def Sub (S : SystemW) (rs : WRows) : Prop :=
  ∀ p ∈ rs, ∃ r ∈ S, p.2.coeffs = r.decode.coeffs.reverse ∧ p.2.bound = r.decode.bound

theorem Sub.nil (S : SystemW) : Sub S [] := fun _ hp => absurd hp List.not_mem_nil

theorem Sub.cons {S : SystemW} {rs : WRows} (h : Sub S rs) {r : IneqW} (hr : r ∈ S) (y : ℤ) :
    Sub S ((y, ⟨r.decode.coeffs.reverse, r.decode.bound⟩) :: rs) := by
  intro p hp
  rcases List.mem_cons.1 hp with rfl | hp
  · exact ⟨r, hr, rfl, rfl⟩
  · exact h p hp

/-- **A certificate for rows from `S` refutes `S`.** -/
theorem infeasible_of_sub {S : SystemW} {rs : WRows} (h : Sub S rs) (hc : rs.IsCert) :
    S ∈ Infeasible := by
  intro K _ _ _ ⟨x, hx⟩
  apply hc.not_feasible (K := K)
  refine ⟨x, fun r hr => ?_⟩
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
  obtain ⟨r', hr', hco, hb⟩ := h p hp
  have hs := hx r'.decode (List.mem_map_of_mem hr')
  unfold Ineq.Sat Ineq.eval at hs ⊢
  rw [hco, hb, List.map_reverse, List.sum_reverse]
  exact hs

/-! ## 64-bit words -/

theorem load_dw {B : ByteArray} {a : Nat} (h : a + 8 ≤ B.size) :
    Memory.load B a 8 = some (dw B a) := by
  simp only [dw, Silmaril.Wasm.Logic.Core.load_eq h, Option.getD_some]

end Silmaril.Proofs.Wasm.Examples.FarkasAccept
