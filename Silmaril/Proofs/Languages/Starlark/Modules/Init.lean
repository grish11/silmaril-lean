module

public import Silmaril.Languages.Starlark.Modules.Operational.Defs
public import Silmaril.Languages.Starlark.Functions.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules

open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (State)
open Silmaril.Languages.Starlark.Modules

private theorem eq_command_of_exec {program : Program} {host : Catalog} {s : State}
    {command : Command} {out : Result Unit} (h : Executes program host s command out) :
    runCommand program host command s = out := by
  cases h with
  | exec h =>
    have evaluated := (exec_iff_denoteBody _ _ _ _ _).mp h
    simp [runCommand, run, evaluated]
  | load => rfl

private theorem command_run (program : Program) (host : Catalog) (command : Command) (s : State) :
    Executes program host s command (runCommand program host command s) := by
  cases command with
  | exec code => exact .exec ((exec_iff_denoteBody _ _ _ _ _).mpr rfl)
  | load label imports => exact .load

private theorem eq_commands_of_run {program : Program} {host : Catalog} {s : State}
    {commands : List Command} {out : Result Unit} (h : Runs program host s commands out) :
    runCommands program host commands s = out := by
  induction h with
  | done => rfl
  | step h _ ih =>
    rw [runCommands, eq_command_of_exec h]
    exact ih
  | failed h => rw [runCommands, eq_command_of_exec h]

private theorem commands_run (program : Program) (host : Catalog) (commands : List Command)
    (s : State) : Runs program host s commands (runCommands program host commands s) := by
  induction commands generalizing s with
  | nil => exact .done
  | cons command rest ih =>
    rw [runCommands]
    have step := command_run program host command s
    cases h : runCommand program host command s with
    | error error next => exact .failed (h ▸ step)
    | ok result next =>
      cases result
      exact .step (h ▸ step) (ih next)

theorem eq_initialize_of_initializes {program : Program} {host : Catalog} {source : Source}
    {caller : State} {out : Result Published} (h : Initializes program host source caller out) :
    initializeModule program host source caller = out := by
  cases h with
  | reject rejected => simp [initializeModule, rejected]
  | run valid started => simp [initializeModule, valid, eq_commands_of_run started]

theorem initializes_initialize (program : Program) (host : Catalog) (source : Source)
    (caller : State) : Initializes program host source caller (initializeModule program host source caller) := by
  cases h : validateSource program source with
  | error error =>
    rw [initializeModule, h]
    exact .reject h
  | ok validated =>
    cases validated
    rw [initializeModule, h]
    exact .run h (commands_run program host source.commands (enter source caller))

end Silmaril.Proofs.Languages.Starlark.Modules
