module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved

open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF (Cfg)
open Loop.MLIR.CF (TargetOp evalOp)

variable {Input extra widths : List Width} {saved carried result w : Width}

theorem Slots.find?_origin {slots : Slots widths} {origin : Nat} {ref : Var widths w}
    (found : slots.find? origin = some ⟨w, ref⟩) : slots.origin ref = origin :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Slots.find?_origin found

theorem Slots.find?_exists {slots : Slots widths} {origin : Nat} (found : origin ∈ slots.origins) :
    ∃ ref, slots.find? origin = some ref :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Slots.find?_exists found

/-- Removal from the header and insertion into the saved prefix preserve
the full inventory of original identities. -/
theorem promote_perm (slots : Slots widths) {header : List Nat} {index origin : Nat}
    (atIndex : header[index]? = some origin) :
    ((Slots.cons (w := w) origin slots).origins ++ header.eraseIdx index).Perm (slots.origins ++ header) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Saved.promote_perm slots atIndex

/-- A typed capture reads the same value in the leading preheader scope
as in the header's saved packet and immutable inputs, for any latch value. -/
theorem origins_agree (values : Env widths) (latch : BitVec carried.val) (input : Env Input) :
    CapturesAgree (origins (carried := carried) widths) ((values.append (.cons latch .nil)).append input)
      (values.append input) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Saved.origins_agree values latch input

/-- A captured immutable reference agrees with the input under any saved prefix. -/
theorem immutableOrigins_agree (values : Env widths) (input : Env Input) :
    CapturesAgree (immutableOrigins widths) (values.append input) input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Saved.immutableOrigins_agree values input

theorem immutableOrigins_cut (ref : Var (widths ++ Input) w) {captured : Var Input w}
    (found : immutableOrigins widths ref = .inl captured) : definitionCut widths ref = 0 :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Saved.immutableOrigins_cut ref found

theorem prefixRef_get (ref : Var widths w) (values : Env widths) (suffix : Env Input) :
    (values.append suffix).get (prefixRef Input ref) = values.get ref :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Saved.prefixRef_get ref values suffix

/-- A saved header argument resolves to the same typed slot in the preheader. -/
theorem origins_prefixRef (ref : Var widths w) :
    origins (carried := carried) widths (prefixRef Input (prefixRef [carried] ref)) =
      .inl (prefixRef Input ref) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Saved.origins_prefixRef ref

/-- A previously saved definition stays at its earlier cut after another save. -/
theorem definitionCut_there {new : Width} (ref : Var (widths ++ Input) w) :
    definitionCut (new :: widths) (.there ref) = definitionCut widths ref :=
  Nat.succ_sub_succ_eq_sub _ _

variable {base : Cfg TargetOp (SourceLabel carried result) Input [result]}
variable {source : Cfg TargetOp (Label saved carried result extra) Input [result]}
variable {target : Cfg TargetOp (Label saved carried result (w :: extra)) Input [result]}
variable {input : Env Input} {values : Env (extra ++ [saved])} {value : BitVec w.val}

/-- A proved single-step remapping extends the invariant for the actual
entry and feedback packets and preserves exact exits. -/
theorem extend_routes
    (prior : RoutesWith base source input values) (step : StepRoutes source target input values value) :
    RoutesWith base target input (extra := w :: extra) (.cons value values) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Saved.extend_routes prior step

theorem extend_run_eq
    (prior : RoutesWith base source input values) (step : StepRoutes source target input values value)
    (fuel : Nat) : target.run evalOp fuel input = source.run evalOp fuel input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Saved.extend_run_eq prior step fuel

/-- After a checked splice, move the resolved identity to the new saved
slot and extend the packet invariant with the result of that same edit. -/
theorem Invariant.extend {inventory header : List Nat} {slots : Slots (extra ++ [saved])}
    {index origin : Nat} (prior : Invariant base source inventory header slots input values)
    (selected : header[index]? = some origin) (step : StepRoutes source target input values value) :
    Invariant base target (extra := w :: extra) inventory (header.eraseIdx index) (.cons origin slots)
      input (.cons value values) :=
  ⟨(promote_perm slots selected).trans prior.partition, extend_routes prior.routes step⟩

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved
