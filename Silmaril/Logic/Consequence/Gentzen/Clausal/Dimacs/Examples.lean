module

public import Silmaril.Logic.Consequence.Gentzen.Clausal.Dimacs.Thms

/-!
# Examples: signed clauses through DIMACS and LRAT

Atoms `V := x | y`, variables `x ↦ 1`, `y ↦ 2` (`vx`).

* `src`, the four clauses over `x, y`, has the DIMACS image `LRAT.fourClauses`
  (`encode_src`) and the stream `1 2 0 -1 2 0 1 -2 0 -1 -2 0` (`write_src`). The existing
  kernel-checked LRAT proof (`LRAT.fourClauses_check`, by `decide`) refutes `src` under every
  valuation in every model type (`src_unsat`), also through the stream (`src_unsat_stream`).
* **Collision**: with every atom on variable `1`, `[[x], [¬y]]` is satisfiable but its image
  `[[1], [-1]]` has an accepted LRAT refutation (`collision`). The image is not coherent; this
  shows why the transfer needs a hypothesis such as `Coherent.injOn`, not that injectivity is
  necessary for every formula.
* **No converse**: in the model type `Unit` whose only model makes every atom true, `[[¬x]]` is
  unsatisfiable while its coherent image `[[-1]]` is satisfiable (`converse_fails`).
* **The terminator**: mapping an atom to `0` gives the clause `[0]`, which is not coherent and
  whose stream is not read back (`zero_not_coherent`).
-/

@[expose] public section

namespace Silmaril.Consequence.Gentzen.Clausal.Dimacs.Examples

open Silmaril.Logic.SAT Signed

/-- Two atoms. -/
inductive V where
  | x
  | y
  deriving DecidableEq, Repr

open V

/-- `x ↦ 1`, `y ↦ 2`. -/
def vx : V → Nat
  | .x => 1
  | .y => 2

/-- All four clauses over `x, y`. -/
def src : List (List (Signed V)) :=
  [[pos x, pos y], [neg x, pos y], [pos x, neg y], [neg x, neg y]]

theorem src_coherent : Coherent vx src := by decide

theorem encode_src : encode vx src = LRAT.fourClauses := by decide

theorem write_src : Dimacs.write (encode vx src) = [1, 2, 0, -1, 2, 0, 1, -2, 0, -1, -2, 0] := by
  decide

theorem src_unsat {M : Type} (τ : M → V → Prop) : CnfUnsat (signedSat τ) src :=
  signedSat_cnfUnsat_of_lrat τ src_coherent (encode_src ▸ LRAT.fourClauses_check)

theorem src_unsat_stream {M : Type} (τ : M → V → Prop) : CnfUnsat (signedSat τ) src :=
  cnfUnsat_of_lrat_stream (signedSat_negSound τ) src_coherent
    (proof := LRAT.fourClausesProof) (by decide)

/-- LRAT acceptance of the image, as a CNF acceptor. -/
example : lratAccepts (encode vx src) := ⟨_, encode_src ▸ LRAT.fourClauses_check⟩

/-! ## A collision -/

/-- Every atom on variable `1`. -/
def vOne : V → Nat := fun _ => 1

/-- `x ∧ ¬y`. -/
def col : List (List (Signed V)) := [[pos x], [neg y]]

/-- The valuation making exactly `x` true. -/
def onlyX : (V → Prop) → V → Prop := fun m a => m a

theorem collision :
    ¬ Coherent vOne col ∧ CnfSat (signedSat onlyX) (fun a => a = x) col ∧
      LRAT.check (encode vOne col) [.add 3 [] [1, 2]] = true := by
  refine ⟨by decide, ?_, by decide⟩
  intro K hK
  simp only [col, List.mem_cons, List.not_mem_nil, or_false] at hK
  rcases hK with rfl | rfl
  · exact ⟨pos x, List.mem_singleton_self _, (rfl : x = x)⟩
  · exact ⟨neg y, List.mem_singleton_self _, fun h => V.noConfusion h⟩

/-! ## The converse fails for a restricted model type -/

/-- One model, making every atom true. -/
def allTrue : Unit → V → Prop := fun _ _ => True

theorem converse_fails :
    Coherent vx [[neg x]] ∧ CnfUnsat (signedSat allTrue) [[neg x]] ∧
      (encode vx [[neg x]]).Sat := by
  refine ⟨by decide, ?_, ⟨fun _ => false, by decide⟩⟩
  intro m hm
  obtain ⟨c, hc, hs⟩ := hm [neg x] List.mem_cons_self
  rw [List.mem_singleton] at hc
  subst hc
  exact hs trivial

/-! ## The terminator is reserved -/

theorem zero_not_coherent :
    ¬ Coherent (fun _ => 0) [[pos x]] ∧ encode (fun _ => 0) [[pos x]] = [[0]] ∧
      Dimacs.cnf (Dimacs.write (encode (fun _ => 0) [[pos x]])) ≠ encode (fun _ => 0) [[pos x]] := by
  decide

end Silmaril.Consequence.Gentzen.Clausal.Dimacs.Examples
