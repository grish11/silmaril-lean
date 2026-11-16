module

public import Silmaril.Logic.Consequence.Gentzen.Clausal.Dimacs.Defs
public import Silmaril.Logic.Consequence.Gentzen.Clausal.Thms
public import Silmaril.Logic.Consequence.Refutation.CNF.Thms
public import Silmaril.Logic.SAT.CNF.Thms
public import Silmaril.Logic.SAT.LRAT.Thms
import Silmaril.Proofs.Logic.Consequence.Gentzen.Clausal.Dimacs

/-!
# Clausal acceptors over DIMACS: the existing CNF, DIMACS and LRAT APIs, and the signed image

**Existing DIMACS formulas as clausal acceptors.**

* `cnfUnsat_litSat_iff`: `CnfUnsat litSat F ↔ SAT.CNF.Unsat F`; so `SAT.CNF.Unsat` is
  `CnfClosed` (`cnfClosed_unsat`).
* `cnfUnsat_toCNF_iff`: on clauses without `0` (`Refutation.CNF.WClause`), it is also the
  existing `Refutation.Unsat csat` of `Silmaril.Logic.Consequence.Refutation.CNF`.
* `lratAccepts_sound`: LRAT acceptance is a sound CNF acceptor (`LRAT.check_sound`). Soundness
  is all that is claimed: no closure law or completeness of the checker is stated.

**The signed image** (`encLit`, `encode`, `Coherent`):

* `encLit_neg`: the sign flip commutes with the image, for every `v`.
* `encode_zero_free` (`Coherent`): no clause of the image contains the terminator `0`, so the
  DIMACS stream of the image reads back exactly (`read_write_encode`, through the existing
  `Dimacs.read`).
* **`sat_encode`**: for `sat : M → Signed A → Prop` with `NegSound sat (-·)` (a model of `neg a`
  is not a model of `pos a`) and `Coherent v F`, a model of `F` in `M` gives an assignment
  satisfying `encode v F`.
* **`cnfUnsat_of_encode`**: hence an unsatisfiable image means `F` has no model in `M`; and
  **`cnfUnsat_of_lrat`**, `cnfUnsat_of_lrat_stream`: an accepted LRAT proof of the image (or of
  the formula read from its DIMACS stream) proves `F` unsatisfiable in `M`, through
  `LRAT.check_sound`. `signedSat_cnfUnsat_of_lrat` instantiates `sat := signedSat τ` for any
  valuation `τ : M → A → Prop`.

The converse (`F` unsatisfiable in `M` ⇒ image unsatisfiable) is not claimed: it fails when `M`
does not realize every valuation (`…Dimacs.Examples.converse_fails`).
-/

@[expose] public section

namespace Silmaril.Consequence.Gentzen.Clausal

open Silmaril.Logic.SAT

universe u v

/-! ## DIMACS formulas and LRAT -/

theorem cnfSat_litSat_iff {τ : Assignment} {F : Silmaril.Logic.SAT.CNF} :
    CnfSat litSat τ F ↔ F.eval τ = true :=
  Proofs.Logic.Consequence.Gentzen.Clausal.Dimacs.cnfSat_litSat_iff

theorem cnfUnsat_litSat_iff {F : Silmaril.Logic.SAT.CNF} : CnfUnsat litSat F ↔ F.Unsat :=
  Proofs.Logic.Consequence.Gentzen.Clausal.Dimacs.cnfUnsat_litSat_iff

theorem cnfClosed_unsat : CnfClosed Silmaril.Logic.SAT.CNF.Unsat := by
  have : CnfUnsat litSat = Silmaril.Logic.SAT.CNF.Unsat := funext fun _ => propext cnfUnsat_litSat_iff
  exact this ▸ cnfUnsat_closed

theorem cnfUnsat_toCNF_iff (Γ : List Refutation.CNF.WClause) :
    CnfUnsat litSat (Refutation.CNF.toCNF Γ) ↔ Refutation.Unsat Refutation.CNF.csat Γ := by
  rw [cnfUnsat_litSat_iff, Refutation.CNF.unsat_iff]

/-- LRAT acceptance is a sound CNF-UNSAT acceptor. -/
theorem lratAccepts_sound : CnfSound litSat lratAccepts :=
  fun _ ⟨_, h⟩ => cnfUnsat_litSat_iff.2 (LRAT.check_sound h)

/-! ## The DIMACS image of signed clauses -/

variable {A : Type u} {v : A → Nat} {F : List (List (Signed A))}

theorem encLit_neg (v : A → Nat) (x : Signed A) : encLit v (-x) = -encLit v x :=
  Proofs.Logic.Consequence.Gentzen.Clausal.Dimacs.encLit_neg v x

theorem encode_zero_free (hc : Coherent v F) : ∀ K ∈ encode v F, (0 : Lit) ∉ K :=
  Proofs.Logic.Consequence.Gentzen.Clausal.Dimacs.encode_zero_free hc

theorem read_write_encode (hc : Coherent v F) :
    Dimacs.read (Dimacs.write (encode v F)) = (encode v F, []) :=
  Dimacs.read_write (encode_zero_free hc)

theorem cnf_write_encode (hc : Coherent v F) : Dimacs.cnf (Dimacs.write (encode v F)) = encode v F :=
  Dimacs.cnf_write (encode_zero_free hc)

section Transfer

variable {M : Type v} {sat : M → Signed A → Prop}

/-- Source satisfiable in `M` ⇒ image satisfiable. -/
theorem sat_encode (hn : NegSound sat (fun x => -x)) (hc : Coherent v F) {m : M}
    (hm : CnfSat sat m F) : (encode v F).Sat :=
  Proofs.Logic.Consequence.Gentzen.Clausal.Dimacs.sat_encode hn hc hm

/-- Image unsatisfiable ⇒ source unsatisfiable in `M`. -/
theorem cnfUnsat_of_encode (hn : NegSound sat (fun x => -x)) (hc : Coherent v F)
    (hu : (encode v F).Unsat) : CnfUnsat sat F :=
  fun _ hm => CNF.not_sat_of_unsat hu (sat_encode hn hc hm)

/-- An accepted LRAT refutation of the image refutes the source in `M`. -/
theorem cnfUnsat_of_lrat (hn : NegSound sat (fun x => -x)) (hc : Coherent v F)
    {proof : List LRAT.Step} (h : LRAT.check (encode v F) proof = true) : CnfUnsat sat F :=
  cnfUnsat_of_encode hn hc (LRAT.check_sound h)

/-- The same, for the formula read from the DIMACS stream of the image. -/
theorem cnfUnsat_of_lrat_stream (hn : NegSound sat (fun x => -x)) (hc : Coherent v F)
    {proof : List LRAT.Step}
    (h : LRAT.check (Dimacs.cnf (Dimacs.write (encode v F))) proof = true) : CnfUnsat sat F :=
  cnfUnsat_of_lrat hn hc (cnf_write_encode hc ▸ h)

end Transfer

/-- Signed literals under any valuation of atoms: an accepted LRAT refutation of the image
refutes the source. -/
theorem signedSat_cnfUnsat_of_lrat {M : Type v} (τ : M → A → Prop) (hc : Coherent v F)
    {proof : List LRAT.Step} (h : LRAT.check (encode v F) proof = true) :
    CnfUnsat (signedSat τ) F :=
  cnfUnsat_of_lrat (signedSat_negSound τ) hc h

end Silmaril.Consequence.Gentzen.Clausal
