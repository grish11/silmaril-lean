module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback.Live.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.ComputedReturns

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.LiveTable

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns (Step)
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
  (Readback readback_iff_eqv packedReadbackRep dispatcherRep orderedRow entry_route carryExit)
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback.Live
open CfgEta.TypeCategory (seqValueBranches caseValueBranches)
open CfgEta.TypeCategory.Retained (distributorRegion_typed)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer
  (Val ValTy Result Frame loopResult finish enter path step terminates cfgRun mapOut one)
open scoped Paper.BoundSimulation.Obstruction BoundSimulation.Obstruction.Observer.CanonicalUnit
open _root_.Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer (TermObservation SameWith evalRegionWith evalTermWith evalReturnRegion
  extension_same unary_fusion_same)
open ComputedReturns (unaryExtension_same)
open TriplingComputedCallFeedback (observe env env_typed route observe_seq observe_body
  observe_iterate observe_case_left observe_case_right)

private def observation : TermObservation (α := Atom) Op where
  evaluateCallOperand := true
  wideFeedback := true
  callResult
    | .enter => some .unit
    | .poll => some (.inl .unit)
  callResult_typed p _ _ h := by
    cases p <;> cases Option.some.inj h
    · exact .base
    · exact .inl .unit

local notation "see" => observe observation
local notation "ExitTy" => Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback.Live.Result

set_option backward.isDefEq.respectTransparency false

private theorem same {Γ L : List (Ty Atom)} {r s : Region Op}
    (h : Paper.Extension.Eqv (Step (τ := Ty Atom) (Φ := Op) false) Γ r s L) :
    SameWith observation Γ r s :=
  unaryExtension_same false rfl rfl rfl h

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

private theorem written_seen : see written .unit = .fault := by
  change cfgRun 2 (fun i v => evalRegionWith observation (rows i)
    (Semantics.extend (env .unit) v)) (.jump 0 .unit) true = .fault
  exact cycle_finish (0, .unit) (1, .unit) rfl rfl

private theorem dispatcher_left {X A D : Ty Atom} {L : LCtx (Ty Atom)}
    (rows : ∀ i : Fin (A :: L).length,
      {r : Region Op // ValueBranches [product X ((A :: L).get i)] r [D]})
    {x a : Val} (hx : ValTy x X) (ha : ValTy a A) :
    see (dispatcherRep X (A :: L) rows).val (.pair x (.inl a)) =
      see (rows 0).val (.pair x a) := by
  rw [dispatcherRep]
  change see (compLSubst (fun _ => CfgEta.TypeCategory.Retained.distributorRegion)
    (fun _ => _) 0) _ = _
  rw [observe_seq (observation := observation) (distributorRegion_typed (Φ := Op) X A (packedExitType L)) (.pair hx (.inl ha))]
  exact observe_case_left (observation := observation) _ _ _

private theorem dispatcher_right {X A D : Ty Atom} {L : LCtx (Ty Atom)}
    (rows : ∀ i : Fin (A :: L).length,
      {r : Region Op // ValueBranches [product X ((A :: L).get i)] r [D]})
    {x a : Val} (hx : ValTy x X) (ha : ValTy a (packedExitType L)) :
    see (dispatcherRep X (A :: L) rows).val (.pair x (.inr a)) =
      see (dispatcherRep X L (fun i => rows i.succ)).val (.pair x a) := by
  rw [dispatcherRep]
  change see (compLSubst (fun _ => CfgEta.TypeCategory.Retained.distributorRegion)
    (fun _ => _) 0) _ = _
  rw [observe_seq (observation := observation) (distributorRegion_typed (Φ := Op) X A (packedExitType L)) (.pair hx (.inr ha))]
  exact observe_case_right (observation := observation) _ _ _

private noncomputable def dispatcher :=
  dispatcherRep Payload (List.ofFn labels) (orderedRow labels rows_typed)

private def state₀ : Val := .pair .unit (.inl .unit)
private def state₁ : Val := .pair .unit (.inr (.inl .unit))

private theorem state₀_typed : ValTy state₀ (product Payload (packedExitType (List.ofFn labels))) :=
  .pair .base (.inl .base)

private theorem state₁_typed : ValTy state₁ (product Payload (packedExitType (List.ofFn labels))) :=
  .pair .base (.inr (.inl .unit))

private theorem step₀ : see dispatcher.val state₀ = .jump 0 (.inr state₁) := by
  change see (dispatcherRep Payload [Payload, Silmaril.unit] (orderedRow labels rows_typed)).val
    (.pair .unit (.inl .unit)) = _
  rw [dispatcher_left _ (.base : ValTy .unit Payload) (.base : ValTy .unit Payload)]
  rfl

private theorem step₁ : see dispatcher.val state₁ = .jump 0 (.inr state₀) := by
  change see (dispatcherRep Payload [Payload, Silmaril.unit] (orderedRow labels rows_typed)).val
    (.pair .unit (.inr (.inl .unit))) = _
  rw [dispatcher_right (L := [Silmaril.unit]) _ (.base : ValTy .unit Payload) (.inl .unit)]
  exact (dispatcher_left (X := Payload) (A := Silmaril.unit) (L := [])
    (fun i => orderedRow labels rows_typed i.succ) (.base : ValTy .unit Payload) .unit).trans rfl

private theorem packed_seen {e : Region Op}
    (he : ValueBranches [Payload] e (List.ofFn labels ++ [ExitTy]))
    (entered : see (e.lsubst (carryExit 0 2)) .unit = .jump 0 (.inr state₀)) :
    see (packedReadbackRep labels he rows_typed).val .unit = .diverges := by
  let P := product Payload (packedExitType (List.ofFn labels))
  let body := SyntacticCategory.iterationBody dispatcher.val
  let iteration := SyntacticCategory.iterateRegion P dispatcher.val
  change see (compLSubst (fun _ => e.lsubst _) (fun _ =>
    .case (.var 0) _ (iteration.renameVars (Silmaril.DeBruijn.lift Nat.succ))) 0) .unit = _
  rw [observe_seq (entry_route labels he) (.base : ValTy .unit Payload), entered]
  refine (observe_case_right (observation := observation) (.br 0 (.var 0)) iteration state₀).trans ?_
  dsimp only [iteration]
  rw [observe_iterate]
  have ab : see body state₀ = .jump 0 state₁ := by
    rw [observe_body dispatcher.property state₀_typed, step₀]
    rfl
  have ba : see body state₁ = .jump 0 state₀ := by
    rw [observe_body dispatcher.property state₁_typed, step₁]
    rfl
  change finish (fun (_ : Fin 1) => see body) (.inr (0, state₀)) false = .diverges
  exact cycle_finish (0, state₀) (0, state₁)
    (by simp only [step, ab]; rfl) (by simp only [step, ba]; rfl)

private theorem separate {e : Region Op}
    (he : ValueBranches [Payload] e
      (List.ofFn labels ++ [ExitTy]))
    (source : see (.cfg e 2 rows) .unit = .fault)
    (entered : see (e.lsubst (carryExit 0 2)) .unit = .jump 0 (.inr state₀)) :
    ¬ Readback false labels he rows_typed := by
  intro eq
  have typed := (readback_iff_eqv false labels he rows_typed).mp eq
  have observed := same typed (env .unit) (env_typed (.base : ValTy .unit Payload))
  change see (.cfg e 2 rows) .unit = see (packedReadbackRep labels he rows_typed).val .unit at observed
  rw [source, packed_seen he entered] at observed
  cases observed

theorem readback_fails : ¬ Readback false labels entry_typed rows_typed :=
  separate entry_typed written_seen rfl

theorem constructorEntry_readback_fails :
    ¬ Readback false labels
      (.br (ℓ := 0) rfl (.var (i := 0) rfl : Tm.BranchValue [Payload] (.var 0 : Tm Op) Payload))
      rows_typed := by
  apply separate _ _ rfl
  change cfgRun 2 (fun i v => evalRegionWith observation (rows i)
    (Semantics.extend (env .unit) v)) (.jump 0 .unit) true = .fault
  exact cycle_finish (0, .unit) (1, .unit) rfl rfl

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.LiveTable
