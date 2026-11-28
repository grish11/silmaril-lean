module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer.Exit.Thms

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer.Exit.Inversion.Proofs

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame Opcode packValues)
open Silmaril.Machine.RTL.SSA (Prog StepsNWithin toLambdaSSA run_returned)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg model)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.MLIR.CF (i64)
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (evalOp TargetOp)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

variable {old new tests : Nat} {entrySigs sigs : List (List PortTy)}
variable {mapping : InputMap old new} {source : Family.Source old old entrySigs sigs tests}
variable {origins : List (HeaderWord new old sigs)}

private theorem return_after_transfers {live : Nat}
    {cfg : Cfg TargetOp (Label live old tests) (wordsTy new) [i64]}
    {input : Silmaril.MLIR.Arith.Env (wordsTy new)} {start finish count}
    (path : Transfers cfg input count start finish)
    {fuel : Nat} {result : Silmaril.MLIR.Arith.Env [i64]}
    (observed : cfg.runFrom evalOp fuel input start = some result) :
    ∃ remaining, fuel = count + remaining ∧ cfg.runFrom evalOp remaining input finish = some result := by
  induction path generalizing fuel with
  | refl _ => exact ⟨fuel, (Nat.zero_add fuel).symm, observed⟩
  | next step _ ih =>
    cases fuel with
    | zero => cases observed
    | succ fuel =>
      unfold Cfg.runFrom at observed
      rw [Cfg.runBlock, step] at observed
      obtain ⟨remaining, spent, ran⟩ := ih observed
      exact ⟨remaining, by omega, ran⟩

private theorem invert_exit {compiled : Compiled mapping source origins} {input : WordTuple new}
    {mem : Memory} {carried : WordTuple old} {before : Frame Reg} {expected value : Word}
    (exit : Taken compiled input mem carried before expected) (fuel : Nat)
    (observed : compiled.setup.cf.runFrom evalOp fuel (wordEnv input) (headerFrame _ _ carried) =
      some (.cons value .nil)) :
    expected = value ∧ 2 ≤ fuel := by
  cases fuel with
  | zero => cases observed
  | succ fuel =>
    unfold Cfg.runFrom at observed
    rw [Cfg.runBlock, exit.cfBranch] at observed
    cases fuel with
    | zero => cases observed
    | succ fuel =>
      change compiled.setup.cf.runBlock evalOp (wordEnv input) (fuel + 1) (compiled.setup.cf.block .exit)
        ((Silmaril.MLIR.Arith.Env.cons (w := i64) expected .nil).append (wordEnv input)) =
        some (.cons value .nil) at observed
      rw [Cfg.runBlock, exit.cfReturn] at observed
      cases observed
      exact ⟨rfl, by omega⟩

theorem from_header (compiled : Compiled mapping source origins) (input : WordTuple new) (mem : Memory)
    (fuel : Nat) (value : Word) (carried : WordTuple old) (before : Frame Reg)
    (matched : ArgsMatch before (appendTuple carried input))
    (observed : compiled.setup.cf.runFrom evalOp fuel (wordEnv input) (headerFrame _ _ carried) =
      some (.cons value .nil)) :
    ∃ slots finish after,
      source.ReturnsAlong (mapping.pull input) slots carried value ∧
      Realized compiled.setup input mem slots carried before finish after ∧
      Taken compiled input mem finish after value ∧ cfCost slots + 2 ≤ fuel := by
  induction fuel using Nat.strongRecOn generalizing carried before with
  | ind fuel ih =>
    cases step : source.step (mapping.pull input) carried with
    | inl expected =>
      have exit := Exit.taken compiled input mem carried before expected matched step
      obtain ⟨rfl, bound⟩ := invert_exit exit fuel observed
      exact ⟨[], carried, before, .exit step, .stop matched, exit, bound⟩
    | inr pair =>
      obtain ⟨slot, next⟩ := pair
      obtain ⟨middle, visit⟩ :=
        Prefix.visit_correct compiled.setup input mem before matched (header_match compiled input carried) step
      obtain ⟨remaining, spent, ran⟩ := return_after_transfers visit.cfPath observed
      obtain ⟨_, _, cut, _, _⟩ := visit.cut
      obtain ⟨slots, finish, after, sourcePath, path, exit, bound⟩ :=
        ih remaining (by omega) next middle cut.rebound ran
      refine ⟨slot :: slots, finish, after, .feedback step sourcePath, .visit visit path, exit, ?_⟩
      simp only [cfCost, List.map_cons, List.sum_cons] at bound ⊢
      omega

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
      Taken compiled input mem finish after value ∧ cfCost slots + 2 + 1 ≤ fuel := by
  cases fuel with
  | zero => cases observed
  | succ fuel =>
    unfold Cfg.run at observed
    rw [Cfg.runBlock, Producer.entry_frame compiled input] at observed
    obtain ⟨started, before, entered, matched⟩ := Family.entry_packet mapping source compiled.accepted input mem
    obtain ⟨slots, finish, after, path, feedback, exit, bound⟩ :=
      from_header compiled input mem fuel value _ before matched observed
    exact ⟨slots, finish, before, after, started, entered, path, feedback, exit, Nat.succ_le_succ bound⟩

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
        (toLambdaSSA [⟨new, 1⟩] (lowerFunc (mapCaptures mapping source))) mem 0 (packValues [value]) mem := by
  obtain ⟨slots, _, _, _, _, _, path, _, _, bound⟩ := from_entry compiled input mem fuel value observed
  obtain ⟨rtl, cf, region⟩ := Exit.returns compiled input mem path env entry
  exact ⟨slots, path, bound, rtl, cf, region⟩

private theorem visitFuel_eq (sigs : List (List PortTy)) (slots : List (Fin (tests + 1))) :
    visitFuel sigs slots = rtlCost sigs.length slots + (sigs.length + 2) := by
  induction slots with
  | nil => simp [visitFuel, rtlCost]
  | cons slot slots ih =>
    simp only [visitFuel, rtlCost, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    omega

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
      compiled.setup.cf.run evalOp (cfCost slots + 2 + 1) (wordEnv input) = some (.cons value .nil) := by
  obtain ⟨slots, value, path, bound, shape, memory⟩ :=
    (Family.rtl_runMain_fuel_iff mapping source compiled.accepted input initial final returned fuel).mp observed
  subst returned
  subst final
  obtain ⟨before, finish, after, started, entered, feedback, exit, rtl, cf⟩ :=
    Exit.from_return_path compiled input initial path
  have exactFuel : rtlFuel entrySigs sigs slots =
      entrySigs.length + 1 + (rtlCost sigs.length slots + (sigs.length + 2)) :=
    congrArg ((entrySigs.length + 1) + ·) (visitFuel_eq sigs slots)
  exact ⟨slots, value, before, finish, after, rfl, rfl, path, bound, started, entered, feedback, exit,
    exactFuel.symm ▸ rtl, cf⟩

theorem region_of_rtl (compiled : Compiled mapping source origins) (input : WordTuple new)
    (initial final : Memory) (fuel : Nat) (returned : List Word)
    (observed : compiled.rtl.runMain fuel 0 (words input) initial = .returned returned final)
    (env : Silmaril.Isotope.LambdaSSA.Semantics.Env Word) (entry : env 0 = packValues (words input)) :
    Eval (Opcode.step (sigs := [⟨new, 1⟩]) compiled.rtl.oracle) env
      (toLambdaSSA [⟨new, 1⟩] (lowerFunc (mapCaptures mapping source))) initial 0 (packValues returned) final := by
  obtain ⟨started, _, _, _⟩ := Family.entry_packet mapping source compiled.accepted input initial
  have machine := observed
  rw [Prog.runMain, started] at machine
  exact (Phi.region_return_iff mapping source compiled.accepted input env entry initial final returned).mpr
    ⟨_, started, run_returned machine⟩

/-- A bounded RTL return exists exactly when an ordered dispatch route
(the positional Φ observations recorded by `Realized`) reaches a taken
exit with the same word. That single witness also supplies a matching
bounded CF return, with full memory preserved by both backends. -/
theorem returns_iff (compiled : Compiled mapping source origins) (input : WordTuple new) (mem : Memory)
    (value : Word) :
    (∃ fuel, compiled.rtl.runMain fuel 0 (words input) mem = .returned [value] mem) ↔
    ∃ slots before finish after,
      source.ReturnsAlong (mapping.pull input) slots (source.primary.initial model (mapping.pull input)) value ∧
      Realized compiled.setup input mem slots (source.primary.initial model (mapping.pull input)) before finish after ∧
      Taken compiled input mem finish after value ∧
      compiled.rtl.runMain (rtlFuel entrySigs sigs slots) 0 (words input) mem = .returned [value] mem ∧
      compiled.setup.cf.run evalOp (cfCost slots + 2 + 1) (wordEnv input) = some (.cons value .nil) := by
  constructor
  · rintro ⟨fuel, observed⟩
    obtain ⟨slots, value', before, finish, after, shape, _, route, _, _, _, realized, taken, rtl, cf⟩ :=
      from_rtl compiled input mem mem fuel [value] observed
    have hv : value' = value := (List.cons.inj shape).1.symm
    subst hv
    exact ⟨slots, before, finish, after, route, realized, taken, rtl, cf⟩
  · rintro ⟨slots, before, finish, after, route, realized, taken, rtl, cf⟩
    exact ⟨_, rtl⟩

/-- For a fixed result word, a successful bounded CF run exists exactly
when an independent, separately-bounded RTL run exists returning the
same singleton with the initial memory preserved. Composes the
fixed-value CF inversion (`from_entry`/`Exit.from_return_path`) with the
actual RTL iff (`returns_iff`); neither direction treats a single
insufficient budget as evidence of nonreturn. -/
theorem cf_returns_iff (compiled : Compiled mapping source origins) (input : WordTuple new) (mem : Memory)
    (value : Word) :
    (∃ fuel, compiled.setup.cf.run evalOp fuel (wordEnv input) = some (.cons value .nil)) ↔
    (∃ fuel, compiled.rtl.runMain fuel 0 (words input) mem = .returned [value] mem) := by
  constructor
  · rintro ⟨fuel, observed⟩
    obtain ⟨slots, finish, before, after, _, _, path, _, _, _⟩ := from_entry compiled input mem fuel value observed
    obtain ⟨before', finish', after', _, _, _, _, rtl, _⟩ := Exit.from_return_path compiled input mem path
    exact ⟨_, rtl⟩
  · intro observed
    obtain ⟨slots, before, finish, after, route, realized, taken, rtl, cf⟩ :=
      (returns_iff compiled input mem value).mp observed
    exact ⟨_, cf⟩

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
      (toLambdaSSA [⟨new, 1⟩] (lowerFunc (mapCaptures mapping source))) mem 0 (packValues [value]) mem := by
  constructor
  · rintro ⟨fuel, observed⟩
    obtain ⟨slots, _, _, _, _, region⟩ := reflect compiled input mem fuel value observed env entry
    exact region
  · intro region
    have oracleFact : compiled.rtl.oracle 0 (words input) mem [value] mem :=
      (Phi.region_return_iff mapping source compiled.accepted input env entry mem mem [value]).mp region
    obtain ⟨slots, v, path, shape, -⟩ :=
      (Family.rtl_return_iff mapping source compiled.accepted input mem mem [value]).mp oracleFact
    have hv : v = value := (List.cons.inj shape).1.symm
    obtain ⟨before, finish, after, _, _, _, _, rtl, _⟩ := Exit.from_return_path compiled input mem (hv ▸ path)
    exact (cf_returns_iff compiled input mem value).mpr ⟨_, rtl⟩

/-- A bounded CF return exists for the typed input and initial memory
exactly when the abstract native source has some finite return along an
ordered dispatch route. This is the CF side of the existing RTL-oracle
law (`Family.rtl_return_iff`) for this checked family. -/
theorem returns_exists_iff (compiled : Compiled mapping source origins) (input : WordTuple new) (mem : Memory) :
    (∃ fuel value, compiled.setup.cf.run evalOp fuel (wordEnv input) = some (.cons value .nil)) ↔
    ∃ slots value, source.ReturnsAlong (mapping.pull input) slots
      (source.primary.initial model (mapping.pull input)) value := by
  constructor
  · rintro ⟨fuel, value, observed⟩
    obtain ⟨slots, finish, before, after, _, _, path, _, _, _⟩ := from_entry compiled input mem fuel value observed
    exact ⟨slots, value, path⟩
  · rintro ⟨slots, value, path⟩
    obtain ⟨before, finish, after, _, _, _, _, _, cf⟩ := Exit.from_return_path compiled input mem path
    exact ⟨_, value, cf⟩

/-- Both actual backends agree on finite-return existence: the RTL oracle's
unbounded native relation returns some word exactly when the emitted CF
returns at some bounded budget. -/
theorem rtl_oracle_iff (compiled : Compiled mapping source origins) (input : WordTuple new) (mem : Memory) :
    (∃ returned final, compiled.rtl.oracle 0 (words input) mem returned final) ↔
    (∃ fuel value, compiled.setup.cf.run evalOp fuel (wordEnv input) = some (.cons value .nil)) := by
  constructor
  · rintro ⟨returned, final, run⟩
    obtain ⟨slots, value, path, -, -⟩ :=
      (Family.rtl_return_iff mapping source compiled.accepted input mem final returned).mp run
    exact (returns_exists_iff compiled input mem).mpr ⟨slots, value, path⟩
  · intro cfReturns
    obtain ⟨slots, value, path⟩ := (returns_exists_iff compiled input mem).mp cfReturns
    exact ⟨[value], mem,
      (Family.rtl_return_iff mapping source compiled.accepted input mem mem [value]).mpr ⟨slots, value, path, rfl, rfl⟩⟩

/-- Absence of any finite return agrees across the RTL oracle and the
emitted CF, at every budget; neither side is read off a single
insufficient run. -/
theorem no_return_iff (compiled : Compiled mapping source origins) (input : WordTuple new) (mem : Memory) :
    (¬ ∃ returned final, compiled.rtl.oracle 0 (words input) mem returned final) ↔
    (¬ ∃ fuel value, compiled.setup.cf.run evalOp fuel (wordEnv input) = some (.cons value .nil)) :=
  not_congr (rtl_oracle_iff compiled input mem)

/-- Under the packed-capture entry side condition, absence of any finite
return also agrees with the canonical λSSA Region, composing the existing
two-directional `Phi.region_no_return_iff` with `no_return_iff`. -/
theorem region_no_return_iff (compiled : Compiled mapping source origins) (input : WordTuple new) (mem : Memory)
    (env : Silmaril.Isotope.LambdaSSA.Semantics.Env Word) (entry : env 0 = packValues (words input)) :
    (¬ ∃ value final, Eval (Opcode.step (sigs := [⟨new, 1⟩]) compiled.rtl.oracle) env
      (toLambdaSSA [⟨new, 1⟩] (lowerFunc (mapCaptures mapping source))) mem 0 value final) ↔
    (¬ ∃ fuel value, compiled.setup.cf.run evalOp fuel (wordEnv input) = some (.cons value .nil)) :=
  (Phi.region_no_return_iff mapping source compiled.accepted input env entry mem).trans
    (no_return_iff compiled input mem)

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer.Exit.Inversion.Proofs
