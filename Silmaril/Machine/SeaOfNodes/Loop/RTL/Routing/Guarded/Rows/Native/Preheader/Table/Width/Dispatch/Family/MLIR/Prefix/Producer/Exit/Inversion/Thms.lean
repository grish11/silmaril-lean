module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer.Exit.Thms

import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer.Exit.Inversion.Execution

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer.Exit.Inversion

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame Opcode packValues)
open Silmaril.Machine.RTL.SSA (StepsNWithin toLambdaSSA)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg model)
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (evalOp)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

variable {old new tests : Nat} {entrySigs sigs : List (List PortTy)}
variable {mapping : InputMap old new} {source : Family.Source old old entrySigs sigs tests}
variable {origins : List (HeaderWord new old sigs)}

/-- Invert a terminating CF run from a matched header into positional feedbacks and the first taken exit. -/
theorem from_header (compiled : Compiled mapping source origins) (input : WordTuple new) (mem : Memory)
    (fuel : Nat) (value : Word) (carried : WordTuple old) (before : Frame Reg)
    (matched : ArgsMatch before (appendTuple carried input))
    (observed : compiled.setup.cf.runFrom evalOp fuel (wordEnv input) (headerFrame _ _ carried) =
      some (.cons value .nil)) :
    ∃ slots finish after,
      source.ReturnsAlong (mapping.pull input) slots carried value ∧
      Realized compiled.setup input mem slots carried before finish after ∧
      Taken compiled input mem finish after value ∧ cfCost slots + 2 ≤ fuel :=
  Proofs.from_header compiled input mem fuel value carried before matched observed

/-- Derive the initial RTL frame match from the checked entry and recover the reached CF, RTL and explicit-Φ cuts. -/
theorem from_entry (compiled : Compiled mapping source origins) (input : WordTuple new) (mem : Memory)
    (fuel : Nat) (value : Word)
    (observed : compiled.setup.cf.run evalOp fuel (wordEnv input) = some (.cons value .nil)) :
    let initial := source.primary.initial model (mapping.pull input)
    ∃ slots finish before after,
      compiled.rtl.start 0 (words input) mem =
        some ⟨⟨0, 0, 0⟩, bindWords 0 Frame.empty input, [], mem⟩ ∧
      StepsNWithin compiled.rtl [] (entrySigs.length + 1)
        ⟨⟨0, 0, 0⟩, bindWords 0 Frame.empty input, [], mem⟩ ⟨⟨0, 1, 0⟩, before, [], mem⟩ ∧
      source.ReturnsAlong (mapping.pull input) slots initial value ∧
      Realized compiled.setup input mem slots initial before finish after ∧
      Taken compiled input mem finish after value ∧ cfCost slots + 2 + 1 ≤ fuel :=
  Proofs.from_entry compiled input mem fuel value observed

/-- Reflect an actual CF return into bounded RTL and the canonical typed λSSA exit, with all memory preserved. -/
theorem reflect (compiled : Compiled mapping source origins) (input : WordTuple new) (mem : Memory)
    (fuel : Nat) (value : Word)
    (observed : compiled.setup.cf.run evalOp fuel (wordEnv input) = some (.cons value .nil))
    (env : Silmaril.Isotope.LambdaSSA.Semantics.Env Word) (entry : env 0 = packValues (words input)) :
    ∃ slots, source.ReturnsAlong (mapping.pull input) slots (source.primary.initial model (mapping.pull input)) value ∧
      cfCost slots + 2 + 1 ≤ fuel ∧
      compiled.rtl.runMain (entrySigs.length + 1 + (rtlCost sigs.length slots + (sigs.length + 2)))
        0 (words input) mem = .returned [value] mem ∧
      compiled.setup.cf.run evalOp (cfCost slots + 2 + 1) (wordEnv input) = some (.cons value .nil) ∧
      Eval (Opcode.step (sigs := [⟨new, 1⟩]) compiled.rtl.oracle) env
        (toLambdaSSA [⟨new, 1⟩] (lowerFunc (mapCaptures mapping source))) mem 0 (packValues [value]) mem :=
  Proofs.reflect compiled input mem fuel value observed env entry

/-- Recover the actual entry path, ordered Φ packets and first exit from an RTL
return. Both runners use the costs of the recovered path in their own units. -/
theorem from_rtl (compiled : Compiled mapping source origins) (input : WordTuple new)
    (initial final : Memory) (fuel : Nat) (returned : List Word)
    (observed : compiled.rtl.runMain fuel 0 (words input) initial = .returned returned final) :
    let bank := source.primary.initial model (mapping.pull input)
    ∃ slots value before finish after,
      returned = [value] ∧ final = initial ∧
      source.ReturnsAlong (mapping.pull input) slots bank value ∧
      rtlFuel entrySigs sigs slots ≤ fuel ∧
      compiled.rtl.start 0 (words input) initial =
        some ⟨⟨0, 0, 0⟩, bindWords 0 Frame.empty input, [], initial⟩ ∧
      StepsNWithin compiled.rtl [] (entrySigs.length + 1)
        ⟨⟨0, 0, 0⟩, bindWords 0 Frame.empty input, [], initial⟩ ⟨⟨0, 1, 0⟩, before, [], initial⟩ ∧
      Realized compiled.setup input initial slots bank before finish after ∧
      Taken compiled input initial finish after value ∧
      compiled.rtl.runMain (rtlFuel entrySigs sigs slots) 0 (words input) initial = .returned returned final ∧
      compiled.setup.cf.run evalOp (cfCost slots + 2 + 1) (wordEnv input) = some (.cons value .nil) :=
  Proofs.from_rtl compiled input initial final fuel returned observed

/-- Reflect an actual machine return to exit zero under the packed capture binding. -/
theorem region_of_rtl (compiled : Compiled mapping source origins) (input : WordTuple new)
    (initial final : Memory) (fuel : Nat) (returned : List Word)
    (observed : compiled.rtl.runMain fuel 0 (words input) initial = .returned returned final)
    (env : Silmaril.Isotope.LambdaSSA.Semantics.Env Word) (entry : env 0 = packValues (words input)) :
    Eval (Opcode.step (sigs := [⟨new, 1⟩]) compiled.rtl.oracle) env
      (toLambdaSSA [⟨new, 1⟩] (lowerFunc (mapCaptures mapping source))) initial 0 (packValues returned) final :=
  Proofs.region_of_rtl compiled input initial final fuel returned observed env entry

/-- A bounded RTL return exists exactly when an ordered dispatch route
(the positional Φ observations recorded by `Realized`) reaches a taken
exit with the same word. That single witness also supplies a matching
bounded CF return, with full memory preserved by both backends. This
consolidates the actual-run forward law (`Exit.returns`/`after_prefix`)
and its converse (`from_rtl`) into one public existence statement. -/
theorem returns_iff (compiled : Compiled mapping source origins) (input : WordTuple new) (mem : Memory)
    (value : Word) :
    (∃ fuel, compiled.rtl.runMain fuel 0 (words input) mem = .returned [value] mem) ↔
    ∃ slots before finish after,
      source.ReturnsAlong (mapping.pull input) slots (source.primary.initial model (mapping.pull input)) value ∧
      Realized compiled.setup input mem slots (source.primary.initial model (mapping.pull input)) before finish after ∧
      Taken compiled input mem finish after value ∧
      compiled.rtl.runMain (rtlFuel entrySigs sigs slots) 0 (words input) mem = .returned [value] mem ∧
      compiled.setup.cf.run evalOp (cfCost slots + 2 + 1) (wordEnv input) = some (.cons value .nil) :=
  Proofs.returns_iff compiled input mem value

/-- For a fixed result word, a successful bounded CF run exists exactly
when an independent, separately-bounded RTL run exists returning the
same singleton with the initial memory preserved. Composes the
fixed-value CF inversion (`from_entry`/`Exit.from_return_path`) with the
actual RTL iff (`returns_iff`); neither direction treats a single
insufficient budget as evidence of nonreturn. -/
theorem cf_returns_iff (compiled : Compiled mapping source origins) (input : WordTuple new) (mem : Memory)
    (value : Word) :
    (∃ fuel, compiled.setup.cf.run evalOp fuel (wordEnv input) = some (.cons value .nil)) ↔
    (∃ fuel, compiled.rtl.runMain fuel 0 (words input) mem = .returned [value] mem) :=
  Proofs.cf_returns_iff compiled input mem value

/-- Under the packed-capture entry side condition, a bounded CF return
exists for a fixed result word exactly when the canonical λSSA Region has
a finite evaluation returning the corresponding packed singleton, with
the initial memory preserved. The forward direction reuses the existing
reflection (`reflect`); the converse reuses the existing two-directional
`Phi.region_return_iff` and `Family.rtl_return_iff` to recover the native
dispatch route, then crosses back to CF with `cf_returns_iff`. -/
theorem region_returns_iff (compiled : Compiled mapping source origins) (input : WordTuple new) (mem : Memory)
    (value : Word) (env : Silmaril.Isotope.LambdaSSA.Semantics.Env Word) (entry : env 0 = packValues (words input)) :
    (∃ fuel, compiled.setup.cf.run evalOp fuel (wordEnv input) = some (.cons value .nil)) ↔
    Eval (Opcode.step (sigs := [⟨new, 1⟩]) compiled.rtl.oracle) env
      (toLambdaSSA [⟨new, 1⟩] (lowerFunc (mapCaptures mapping source))) mem 0 (packValues [value]) mem :=
  Proofs.region_returns_iff compiled input mem value env entry

/-- A bounded CF return exists for the typed input and initial memory
exactly when the abstract native source has some finite return along an
ordered dispatch route. This is the CF side of the existing RTL-oracle
law (`Family.rtl_return_iff`) for this checked family. -/
theorem returns_exists_iff (compiled : Compiled mapping source origins) (input : WordTuple new) (mem : Memory) :
    (∃ fuel value, compiled.setup.cf.run evalOp fuel (wordEnv input) = some (.cons value .nil)) ↔
    ∃ slots value, source.ReturnsAlong (mapping.pull input) slots
      (source.primary.initial model (mapping.pull input)) value :=
  Proofs.returns_exists_iff compiled input mem

/-- Both actual backends agree on finite-return existence: the RTL oracle's
unbounded native relation returns some word exactly when the emitted CF
returns at some bounded budget. -/
theorem rtl_oracle_iff (compiled : Compiled mapping source origins) (input : WordTuple new) (mem : Memory) :
    (∃ returned final, compiled.rtl.oracle 0 (words input) mem returned final) ↔
    (∃ fuel value, compiled.setup.cf.run evalOp fuel (wordEnv input) = some (.cons value .nil)) :=
  Proofs.rtl_oracle_iff compiled input mem

/-- Absence of any finite return agrees across the RTL oracle and the
emitted CF, at every budget; neither side is read off a single
insufficient run. -/
theorem no_return_iff (compiled : Compiled mapping source origins) (input : WordTuple new) (mem : Memory) :
    (¬ ∃ returned final, compiled.rtl.oracle 0 (words input) mem returned final) ↔
    (¬ ∃ fuel value, compiled.setup.cf.run evalOp fuel (wordEnv input) = some (.cons value .nil)) :=
  Proofs.no_return_iff compiled input mem

/-- Under the packed-capture entry side condition, absence of any finite
return also agrees with the canonical λSSA Region, composing the existing
two-directional `Phi.region_no_return_iff` with `no_return_iff`. -/
theorem region_no_return_iff (compiled : Compiled mapping source origins) (input : WordTuple new) (mem : Memory)
    (env : Silmaril.Isotope.LambdaSSA.Semantics.Env Word) (entry : env 0 = packValues (words input)) :
    (¬ ∃ value final, Eval (Opcode.step (sigs := [⟨new, 1⟩]) compiled.rtl.oracle) env
      (toLambdaSSA [⟨new, 1⟩] (lowerFunc (mapCaptures mapping source))) mem 0 value final) ↔
    (¬ ∃ fuel value, compiled.setup.cf.run evalOp fuel (wordEnv input) = some (.cons value .nil)) :=
  Proofs.region_no_return_iff compiled input mem env entry

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer.Exit.Inversion
