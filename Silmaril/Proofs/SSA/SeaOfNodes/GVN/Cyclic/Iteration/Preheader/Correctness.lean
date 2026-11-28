module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.Defs
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader

open Silmaril.SSA.SeaOfNodes
open GVN.Cyclic.Iteration.Preheader
open GVN.Cyclic
open GVN.Cyclic.Builder (Built build?)
open GVN.Cyclic.Builder.Preheader (Native optimize? optimize_count optimize_none_iff prepare prepare_builds)
open Diamond (Ty ValueSort)
open scoped Pure.WordNormalize

variable {inputs carried : List (ValueSort Unit)} {entrySigs headerSigs : List (List (Ty Unit))}
variable {out : ValueSort Unit}

theorem run_entry (fuel : Nat) (loop : Native inputs carried entrySigs headerSigs out) :
    let final := (run fuel loop).rewrite.graph
    final.preheader = loop.preheader ∧ final.phiInputs .entry = loop.phiInputs .entry := by
  induction fuel generalizing headerSigs with
  | zero => exact ⟨rfl, rfl⟩
  | succ fuel ih =>
    cases found : GVN.Cyclic.Builder.Preheader.optimize? loop with
    | none =>
      rw [run_succ fuel loop, found]
      exact ⟨rfl, rfl⟩
    | some next =>
      have ⟨preheader, entry⟩ := GVN.Cyclic.Builder.Preheader.optimize_entry found
      have ⟨tailPreheader, tailEntry⟩ := ih next.graph
      rw [run_succ fuel loop, found]
      exact ⟨tailPreheader.trans preheader, tailEntry.trans entry⟩

theorem normalize_saturated (loop : Native inputs carried entrySigs headerSigs out) :
    let prepared := prepare (normalize loop).rewrite.graph
    ∃ built : Built prepared, build? prepared = some built ∧
      ∀ proposal ∈ Pass.proposals built.view,
        Pass.tryProposal? built.view (GVN.Cyclic.FixedPoint.normalize built.graph) proposal = none := by
  let final := (normalize loop).rewrite.graph
  obtain ⟨built, builtEq⟩ := prepare_builds final
  have stopped : optimize? final = none :=
    GVN.Cyclic.Iteration.runWith_stops_of_fuel optimize? (fun found => optimize_count found)
      headerSigs.length loop (Nat.le_refl _)
  exact ⟨built, builtEq, (optimize_none_iff built builtEq).mp stopped⟩

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader
