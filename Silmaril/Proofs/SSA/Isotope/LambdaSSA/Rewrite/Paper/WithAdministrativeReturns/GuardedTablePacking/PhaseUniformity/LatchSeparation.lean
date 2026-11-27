module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.LatchSource
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.ComputedReturns

/-! # Default Paper does not reduce the two-block source to one loop

An observer that validates every equation of default Paper marks an
endless local path through a table with at least two rows, and leaves an
endless path through a one-block loop unmarked. The two-block source has
such a path; the one-header source, the loop on pairs and the packed
readback do not.

The observer also respects the two seeds that the administrative-return
quotient adds to the unary-return quotient, so the separation holds
there too.
-/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.LatchSeparation

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
open Paper.WithCaseBind.BitQuery (signature)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer
  (Val ValTy Result Frame loopResult finish enter path step terminates cfgRun)
open scoped Paper.BoundSimulation.Obstruction BoundSimulation.Obstruction.Observer.CanonicalUnit
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer (EnvTy)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer
  (TermObservation SameWith evalRegionWith evalTermWith paper_same evalReturnRegion evalTerm_subst evalValue
   RealizesWith value_not_computed extension_same unary_fusion_same)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingComputedCallFeedback (observe env env_typed)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.ComputedReturns (unaryExtension_same)

/-- Every request receives the right reply with a fixed payload, and
endless local paths through tables with at least two rows are marked. -/
private def observation : TermObservation (α := Empty) signature.Instr where
  evaluateCallOperand := true
  wideFeedback := true
  callResult
    | .ask _ => some (.inr (.inl .unit))
  callResult_typed p _ _ h := by
    cases p
    cases Option.some.inj h
    exact .inr (.inl .unit)

local notation "see" => observe observation

/-- A path that alternates between two frames never leaves the table. -/
private theorem cycle_finish {n : Nat} {bs : Fin n → Val → Result} {mark : Bool}
    (a b : Fin n × Val) (ab : step bs (.inr a) = .inr b) (ba : step bs (.inr b) = .inr a) :
    finish bs (.inr a) mark = loopResult mark := by
  classical
  have visits (k : Nat) : path bs (.inr a) k = .inr a ∨ path bs (.inr a) k = .inr b := by
    induction k with
    | zero => exact .inl rfl
    | succ k ih =>
      rcases ih with h | h
      · exact .inr (by rw [path, h, ab])
      · exact .inl (by rw [path, h, ba])
  have noExit : ¬ ∃ r, terminates bs (.inr a) r := by
    rintro ⟨r, k, terminal⟩
    rcases visits k with eq | eq <;> rw [eq] at terminal <;> cases terminal
  rw [finish, dite_eq_right noExit]

/-- The input with both Bits equal to the payload of the reply. -/
private def start : Val := .pair (.inl .unit) (.inl .unit)

private theorem start_typed : ValTy start Pair := .pair (.inl .unit) (.inl .unit)

/-- The two-block source alternates between its header and its back-edge
block: a marked endless path. -/
private theorem source_seen (l : Bool) : see (latchSource l) start = .fault := by
  rw [latchSource_eq]
  change cfgRun 2 (fun i v => evalRegionWith observation (latchBlocks l i)
    (Semantics.extend (env start) v)) (.jump 0 start) true = .fault
  exact cycle_finish (0, start) (1, start) rfl rfl

/-- The one-header source repeats its header: an unmarked endless path. -/
private theorem header_seen (l : Bool) : see (pairSource l) start = .diverges := by
  rw [pairSource_eq]
  change cfgRun 1 (fun _ v => evalRegionWith observation
    ((flatBlock l).renameVars (Silmaril.DeBruijn.lift Nat.succ))
    (Semantics.extend (env start) v)) (.jump 0 start) false = .diverges
  exact cycle_finish (0, start) (0, start) rfl rfl

/-- The loop on pairs repeats its body: an unmarked endless path. -/
private theorem loop_seen (l : Bool) : see (loopRegion Pair (pairBody l)) start = .diverges := by
  change cfgRun 1 (fun _ v => evalRegionWith observation
    ((SyntacticCategory.iterationBody (pairBody l)).renameVars (Silmaril.DeBruijn.lift Nat.succ))
    (Semantics.extend (env start) v)) (.jump 0 start) false = .diverges
  exact cycle_finish (0, start) (0, start) rfl rfl

private theorem same {Γ L : List (Ty Empty)} {r s : Region signature.Instr} (h : Paper.Eqv Γ r s L) :
    SameWith observation Γ r s :=
  paper_same h

/-- Default Paper does not prove the two-block source equal to the loop
on pairs, for any labels. -/
theorem source_ne_loop (l l' : Bool) :
    ¬ Paper.Eqv [Pair] (latchSource l) (loopRegion Pair (pairBody l')) [Bit] := by
  intro e
  have o : see (latchSource l) start = see (loopRegion Pair (pairBody l')) start :=
    same e (env start) (env_typed start_typed)
  rw [source_seen, loop_seen] at o
  cases o

/-- Default Paper does not prove the two-block source equal to the
one-header source, for any labels. -/
theorem source_ne_header (l l' : Bool) :
    ¬ Paper.Eqv [Pair] (latchSource l) (pairSource l') [Bit] := by
  intro e
  have o : see (latchSource l) start = see (pairSource l') start :=
    same e (env start) (env_typed start_typed)
  rw [source_seen, header_seen] at o
  cases o

/-- The table-packing equation at the two-block source is not an
equation of default Paper: the packed readback is the loop on pairs there. -/
theorem source_ne_readback (l l' : Bool) :
    ¬ Paper.Eqv [Pair] (latchSource l) (latchReadback l').val [Bit] :=
  fun e => source_ne_loop l l' (e.trans (Tables.latch_readback_loop l'))

/-- On the readback side everything is one loop in default Paper: the
packed readback is the one-header source. -/
theorem readback_header (l : Bool) : Paper.Eqv [Pair] (latchReadback l).val (pairSource l) [Bit] :=
  (Tables.latch_readback_loop l).trans (Tables.source_loop l).symm

/-- The same separation in the unary-return quotient. -/
theorem source_ne_loop_unary (l l' : Bool) :
    ¬ Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.Eqv false [Pair]
      (latchSource l) (loopRegion Pair (pairBody l')) [Bit] := by
  intro e
  have o : see (latchSource l) start = see (loopRegion Pair (pairBody l')) start :=
    unaryExtension_same (obs := observation) false rfl rfl rfl e (env start) (env_typed start_typed)
  rw [source_seen, loop_seen] at o
  cases o

/-! ## The seeds of the administrative-return quotient -/

section Administrative

universe u v w
variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)] {ε : Type w} [HasEff Φ ε] (pe : ε)

/-- Constructor β at an operand does not change the observed operand:
the observer evaluates a case on a constructor to the selected arm. -/
private theorem operandBeta_same {obs : TermObservation (α := α) Φ} (caseUnmarked : obs.caseTerm = false)
    (binderUnmarked : obs.boundUnaryLet = false) {Γ : List (Ty α)} {a b : Tm Φ} {D : Ty α}
    (h : Paper.WithConstructorCaseOperands.OperandBeta (τ := Ty α) (Φ := Φ) Γ a b D) {env : Nat → Val}
    (he : EnvTy Γ env) :
    evalTermWith (α := α) obs a env = evalTermWith (α := α) obs b env := by
  cases h with
  | left ha hl hr =>
    obtain ⟨w, ew, _⟩ := evalValue (observation := obs) ha he
    rw [evalTerm_subst (observation := obs) _ (RealizesWith.single ew (value_not_computed ha))]
    simp [evalTermWith, caseUnmarked, binderUnmarked, ew]
  | right ha hl hr =>
    obtain ⟨w, ew, _⟩ := evalValue (observation := obs) ha he
    rw [evalTerm_subst (observation := obs) _ (RealizesWith.single ew (value_not_computed ha))]
    simp [evalTermWith, caseUnmarked, binderUnmarked, ew]

/-- Constructor β at the operand of a primitive preserves the observation. -/
private theorem constructorOperand_same {obs : TermObservation (α := α) Φ} (caseUnmarked : obs.caseTerm = false)
    (evaluate : obs.evaluateCallOperand = true) (binderUnmarked : obs.boundUnaryLet = false)
    {Γ L : List (Ty α)} {r s : Region Φ} (h : Paper.WithConstructorCaseOperands.Step Γ r s L) :
    SameWith obs Γ r s := by
  cases h with
  | letCall p h hk =>
    intro env he
    have e := operandBeta_same caseUnmarked binderUnmarked h he
    simp only [evalRegionWith, evalTermWith, evaluate, ↓reduceIte, e]
    rfl
  | caseCall p h hout hl hr =>
    intro env he
    have e := operandBeta_same caseUnmarked binderUnmarked h he
    simp only [evalRegionWith, evalTermWith, evaluate, ↓reduceIte, e]

/-- Splitting a returned case preserves the observation. -/
private theorem letCase_same {obs : TermObservation (α := α) Φ} (caseUnmarked : obs.caseTerm = false)
    (binderUnmarked : obs.boundUnaryLet = false) {Γ L : List (Ty α)} {r s : Region Φ}
    (h : Paper.WithLetCase.Step Γ r s L) : SameWith obs Γ r s := by
  cases h with
  | @split A B D e a b he ha hb =>
    intro env _
    simp only [Paper.RetainedLet.returnOnce, evalRegionWith, evalTermWith, caseUnmarked, binderUnmarked,
      Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    cases evalTermWith obs e env with
    | none => rfl
    | some v => cases v <;> rfl

/-- A returned call is sequenced after its operand (copy of the unary-return case). -/
private theorem computedCall_same' {obs : TermObservation (α := α) Φ} (evaluate : obs.evaluateCallOperand = true)
    {Γ L : List (Ty α)} {r s : Region Φ}
    (step : Paper.WithComputedCallReturns.Step Γ r s L) : SameWith obs Γ r s := by
  cases step with
  | @seq a p ha =>
    intro env he
    let call : Tm.HasType (instrSrc p :: Γ) (.op p (.var 0)) (instrTrg p) := .op (.var rfl)
    rw [evalReturnRegion (observation := obs) (.op ha) he, evalReturnRegion (observation := obs) (.let₁ ha call) he]
    simp only [evalTermWith, evaluate, ↓reduceIte]
    cases evalTermWith obs a env <;> rfl

/-- The observer respects every seed of the administrative-return
quotient, when case terms and bound unary lets are unmarked and operands
of primitives are evaluated. -/
private theorem administrative_same {obs : TermObservation (α := α) Φ} (caseUnmarked : obs.caseTerm = false)
    (evaluate : obs.evaluateCallOperand = true) (binderUnmarked : obs.boundUnaryLet = false)
    {Γ L : List (Ty α)} {r s : Region Φ}
    (eq : Paper.WithAdministrativeReturns.Eqv pe Γ r s L) : SameWith obs Γ r s :=
  extension_same (fun seed => seed.elim
    (fun unary => unary.elim
      (fun e => e.elim
        (Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingComputedCallFeedback.withTriplingSeed_same
          pe caseUnmarked)
        (computedCall_same' evaluate))
      (unary_fusion_same binderUnmarked))
    (fun added => added.elim (constructorOperand_same caseUnmarked evaluate binderUnmarked)
      (letCase_same caseUnmarked binderUnmarked))) eq

end Administrative

/-- The administrative-return quotient does not prove the two-block
source equal to the loop on pairs, for any labels. -/
theorem source_ne_loop_admin (l l' : Bool) :
    ¬ Paper.WithAdministrativeReturns.Eqv false [Pair] (latchSource l) (loopRegion Pair (pairBody l')) [Bit] := by
  intro e
  have o : see (latchSource l) start = see (loopRegion Pair (pairBody l')) start :=
    administrative_same (obs := observation) false rfl rfl rfl e (env start) (env_typed start_typed)
  rw [source_seen, loop_seen] at o
  cases o

/-- Nor equal to the one-header source. -/
theorem source_ne_header_admin (l l' : Bool) :
    ¬ Paper.WithAdministrativeReturns.Eqv false [Pair] (latchSource l) (pairSource l') [Bit] :=
  fun e => source_ne_loop_admin l l' (e.trans (.paper (Tables.source_loop l')))

/-- The table-packing equation at the two-block source is not an
equation of the administrative-return quotient. -/
theorem source_ne_readback_admin (l l' : Bool) :
    ¬ Paper.WithAdministrativeReturns.Eqv false [Pair] (latchSource l) (latchReadback l').val [Bit] :=
  fun e => source_ne_loop_admin l l' (e.trans (.paper (Tables.latch_readback_loop l')))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.LatchSeparation
