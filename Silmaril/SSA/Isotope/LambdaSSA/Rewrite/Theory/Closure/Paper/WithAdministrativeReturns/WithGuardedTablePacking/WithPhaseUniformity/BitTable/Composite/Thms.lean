module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Nest.Compile.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.CompositeTables

/-! # A two-request program written as one step

No seed is added. Nothing here is inferred from a model.

## Default Paper

These are equations of arrows of default Paper. They use no opt-in rule.

* `case_inl_reduce`, `case_inr_reduce`: a branch with an injected payload
  followed by a case is the branch followed by the selected arm, for
  regions with one variable.
* `bitState_unpack`: packing a Bit as a state and unpacking it is the
  identity. This is the native pack and unpack roundtrip.
* `duoProgram_step_arrow`: the written step of `duoProgram l₁ l₂` is the
  step of its first request chained into its second. The two reply arms
  of the first request are reduced in one variable, moved under the
  request by substitution of variables, and joined by the case rule.
* `chain_routerRoute`: the chain followed by a routing is the routing
  whose return leaves send the second request.
* `duoRouter_arrow_source`: so the table whose rows are the two-request
  programs and the table of literal request trees have the same entered
  loops at every entry.

## The opt-in quotient

* `duoProgram_stepFactors`: `StepFactors` holds for `duoProgram`. It is
  the image of `duoProgram_step_arrow`.
* `duoRouter_eqv_duoSource`: the two tables are equal at every entry in
  `WithPhaseUniformity`.
* `duoRouter_complete`: two tables of two-request programs are equal at
  given entries exactly when they are valid in every supported model.
  This uses `LTable.eqv_iff_valid`, which depends on the phase-uniformity
  quotient and the request-prefix model. It is not a statement about
  default Paper.

`duoRouter_eqv_source` and `duoRouter_eqv_iff_valid` are the earlier
forms with `StepFactors` as a hypothesis. They remain for programs whose
factoring is supplied separately.

## Scope

The program has a second request that is selected by the first reply's
tag and queried with the first reply's payload; its results are the
second reply's or the first reply's payload. A leaf that returns a Bit
kept across the second request is not covered here; `Composite.Capture`
treats the first reply's payload. No statement is made for the whole
grammar of written programs, and nothing is claimed about packed
dispatchers in general.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (seqValueBranches caseValueBranches)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (ofRegion ofType)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking
  (Valid.symm Valid.trans)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity

variable {K K₁ K₂ : Nat}

/-! ## A case on an injected payload, at a one-variable boundary -/

section Reduce

variable {X A B D : Ty Empty} {t : Tm signature.Instr} {l r : Region signature.Instr}

/-- A branch with a left-injected payload followed by a case is the
branch followed by the left arm, in default Paper. -/
theorem case_inl_reduce (ht : Tm.BranchValue [X] t A) (hl : ValueBranches [A] l [D])
    (hr : ValueBranches [B] r [D]) :
    ofRegion (seqValueBranches (ValueBranches.br (ℓ := 0) (L := [Silmaril.coprod A B]) rfl (.inl ht))
        (caseValueBranches hl hr)) =
      ofRegion (seqValueBranches (ValueBranches.br (ℓ := 0) (L := [A]) rfl ht) hl) :=
  Tables.case_inl_arrow ht hl hr

/-- The same for a right-injected payload. -/
theorem case_inr_reduce (ht : Tm.BranchValue [X] t B) (hl : ValueBranches [A] l [D])
    (hr : ValueBranches [B] r [D]) :
    ofRegion (seqValueBranches (ValueBranches.br (ℓ := 0) (L := [Silmaril.coprod A B]) rfl (.inr ht))
        (caseValueBranches hl hr)) =
      ofRegion (seqValueBranches (ValueBranches.br (ℓ := 0) (L := [B]) rfl ht) hr) :=
  Tables.case_inr_arrow ht hl hr

end Reduce

/-- The chain into `p₂` followed by the routing `a`, in default Paper. -/
theorem chain_routerRoute (K : Nat) (p₂ : Program) (a : Bool → Bool → Act K) :
    ofRegion (chain_typed p₂) ≫ ofRegion (routerRoute_typed K a) =
      ofRegion (genRoute_typed fun x y => treeRegion_typed K (duoKids K p₂ a x y)) :=
  Tables.chain_route K p₂ a

/-- If every written step factors, the table of two-request programs
equals the table of literal request trees at every entry. -/
theorem duoRouter_eqv_source (l₁ l₂ : Fin (K + 1) → Bool) (act : Fin (K + 1) → Bool → Bool → Act K)
    (fac : ∀ i, StepFactors (duoProgram (l₁ i) (l₂ i)) (labelPoll (l₁ i)).program (labelPoll (l₂ i)).program)
    (j : Fin (K + 1)) :
    Eqv false [State] ((duoRouter l₁ l₂ act).entered j) ((duoSource l₁ l₂ act).entered j) [Bit] :=
  Tables.duo_table_eqv l₁ l₂ act fac j

/-- Under that hypothesis, two such tables are equal at given entries
exactly when they are valid in every supported model. -/
theorem duoRouter_eqv_iff_valid (l₁ l₂ : Fin (K₁ + 1) → Bool) (act : Fin (K₁ + 1) → Bool → Bool → Act K₁)
    (m₁ m₂ : Fin (K₂ + 1) → Bool) (act' : Fin (K₂ + 1) → Bool → Bool → Act K₂)
    (fac : ∀ i, StepFactors (duoProgram (l₁ i) (l₂ i)) (labelPoll (l₁ i)).program (labelPoll (l₂ i)).program)
    (fac' : ∀ i, StepFactors (duoProgram (m₁ i) (m₂ i)) (labelPoll (m₁ i)).program (labelPoll (m₂ i)).program)
    (i₁ : Fin (K₁ + 1)) (i₂ : Fin (K₂ + 1)) :
    Eqv false [State] ((duoRouter l₁ l₂ act).entered i₁) ((duoRouter m₁ m₂ act').entered i₂) [Bit] ↔
      Valid ((duoRouter l₁ l₂ act).entered_typed i₁).hasType
        ((duoRouter m₁ m₂ act').entered_typed i₂).hasType :=
  ⟨fun e => valid_of_eqv false e _ _,
    fun v => (duoRouter_eqv_source l₁ l₂ act fac i₁).trans
      (((LTable.eqv_iff_valid (duoSource l₁ l₂ act) (duoSource m₁ m₂ act') i₁ i₂).2
        (Valid.trans (Valid.symm (valid_of_eqv false (duoRouter_eqv_source l₁ l₂ act fac i₁) _ _))
          (Valid.trans v (valid_of_eqv false (duoRouter_eqv_source m₁ m₂ act' fac' i₂) _ _)))).trans
        (duoRouter_eqv_source m₁ m₂ act' fac' i₂).symm)⟩

/-! ## The factoring, proved -/

/-- Packing a Bit as a state and unpacking it is the identity, in default
Paper. -/
theorem bitState_unpack :
    ofRegion bitState_typed ≫ ofRegion unpack_typed = 𝟙 (ofType (Φ := signature.Instr) Bit) :=
  Tables.pack_unpack

/-- The written step of the two-request program is the step of its first
request chained into its second, as arrows of default Paper. -/
theorem duoProgram_step_arrow (l₁ l₂ : Bool) :
    ofRegion (step_typed (duoProgram l₁ l₂)) =
      ofRegion (chainedStep_typed (labelPoll l₁).program (labelPoll l₂).program) :=
  Tables.duo_step_arrow l₁ l₂

/-- So the factoring holds in the opt-in quotient. -/
theorem duoProgram_stepFactors (l₁ l₂ : Bool) :
    StepFactors (duoProgram l₁ l₂) (labelPoll l₁).program (labelPoll l₂).program :=
  Tables.duo_stepFactors l₁ l₂

/-- The table of two-request programs and the table of literal request
trees have the same entered loops, as arrows of default Paper. -/
theorem duoRouter_arrow_source (l₁ l₂ : Fin (K + 1) → Bool) (act : Fin (K + 1) → Bool → Bool → Act K)
    (j : Fin (K + 1)) :
    ofRegion ((duoRouter l₁ l₂ act).entered_typed j) = ofRegion ((duoSource l₁ l₂ act).entered_typed j) :=
  Tables.duo_table_arrow l₁ l₂ act j

/-- They are equal at every entry in the opt-in quotient. -/
theorem duoRouter_eqv_duoSource (l₁ l₂ : Fin (K + 1) → Bool) (act : Fin (K + 1) → Bool → Bool → Act K)
    (j : Fin (K + 1)) :
    Eqv false [State] ((duoRouter l₁ l₂ act).entered j) ((duoSource l₁ l₂ act).entered j) [Bit] :=
  duoRouter_eqv_source l₁ l₂ act (fun i => duoProgram_stepFactors (l₁ i) (l₂ i)) j

/-- Two tables of two-request programs are equal at given entries exactly
when they are valid in every supported model. -/
theorem duoRouter_complete (l₁ l₂ : Fin (K₁ + 1) → Bool) (act : Fin (K₁ + 1) → Bool → Bool → Act K₁)
    (m₁ m₂ : Fin (K₂ + 1) → Bool) (act' : Fin (K₂ + 1) → Bool → Bool → Act K₂) (i₁ : Fin (K₁ + 1))
    (i₂ : Fin (K₂ + 1)) :
    Eqv false [State] ((duoRouter l₁ l₂ act).entered i₁) ((duoRouter m₁ m₂ act').entered i₂) [Bit] ↔
      Valid ((duoRouter l₁ l₂ act).entered_typed i₁).hasType
        ((duoRouter m₁ m₂ act').entered_typed i₂).hasType :=
  duoRouter_eqv_iff_valid l₁ l₂ act m₁ m₂ act' (fun i => duoProgram_stepFactors (l₁ i) (l₂ i))
    (fun i => duoProgram_stepFactors (m₁ i) (m₂ i)) i₁ i₂

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
