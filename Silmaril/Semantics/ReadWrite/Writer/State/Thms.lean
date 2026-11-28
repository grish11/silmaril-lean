module

public import Silmaril.Semantics.ReadWrite.Writer.State.Defs
public import Silmaril.Semantics.ReadWrite.Writer.Thms
import Silmaril.Proofs.Semantics.ReadWrite.Writer.State

public section
namespace Silmaril.Semantics.ReadWrite

universe u
variable {Address Value State Result Next First Second Third : Type u}

namespace LoggedState

variable [Monoid First] [Monoid Second] [Monoid Third]

@[simp] theorem run_pure (result : Result) (initial : State) :
    run (pure result : LoggedState State First Result) initial = some ((result, initial), 1) := rfl

@[simp] theorem run_bind (action : LoggedState State First Result)
    (next : Result → LoggedState State First Next) (initial : State) :
    run (action >>= next) initial = (run action initial).bind fun ((result, middle), first) =>
      (run (next result) middle).map fun (outcome, last) => (outcome, first * last) := rfl

@[simp] theorem run_mapLog (f : First →* Second) (action : LoggedState State First Result)
    (initial : State) :
    run (mapLog f action) initial = (run action initial).map (Prod.map id f) := rfl

/-- Success or failure, the return value, and the final state agree after projection. -/
theorem run_mapLog_outcome (f : First →* Second) (action : LoggedState State First Result)
    (initial : State) :
    (run (mapLog f action) initial).map Prod.fst = (run action initial).map Prod.fst := by
  rw [run_mapLog]
  cases run action initial <;> rfl

@[simp] theorem mapLog_pure (f : First →* Second) (result : Result) :
    mapLog (State := State) f (pure result) = pure result :=
  StateT.ext fun initial => WriterLog.mapLog_pure f (result, initial)

@[simp] theorem mapLog_bind (f : First →* Second) (action : LoggedState State First Result)
    (next : Result → LoggedState State First Next) :
    mapLog f (action >>= next) = mapLog f action >>= fun result => mapLog f (next result) :=
  StateT.ext fun initial =>
    WriterLog.mapLog_bind f (StateT.run action initial) (fun (result, middle) => StateT.run (next result) middle)

theorem isMonadHom_mapLog (f : First →* Second) :
    Cslib.IsMonadHom (LoggedState State First) (LoggedState State Second) (mapLog f) :=
  .mk' (mapLog_pure f) (mapLog_bind f)

theorem mapLog_comp (g : Second →* Third) (f : First →* Second)
    (action : LoggedState State First Result) :
    mapLog (g.comp f) action = mapLog g (mapLog f action) :=
  StateT.ext fun initial => WriterLog.mapLog_comp g f (StateT.run action initial)

end LoggedState

@[simp] theorem Access.run_logOp_read (access : Access Address Value State) (address : Address)
    (initial : State) :
    LoggedState.run (access.logOp (.read address)) initial =
      (access.read initial address).map fun value =>
        ((value, initial), Trace.toLog [.read address value]) := rfl

@[simp] theorem Access.run_logOp_write (access : Access Address Value State) (address : Address)
    (value : Value) (initial : State) :
    LoggedState.run (access.logOp (.write address value)) initial =
      (access.write initial address value).map fun next =>
        ((PUnit.unit, next), Trace.toLog [.write address value]) := rfl

namespace Program

/-- Interpretation preserves the pure and bind operations of the access program. -/
theorem isMonadHom_interpret (access : Access Address Value State) :
    Cslib.IsMonadHom (Program Address Value) (LoggedState State (ValueLog Address Value))
      (fun program => Program.interpret program access) :=
  Cslib.FreeM.isMonadHom_liftM access.logOp

/-- Projecting after interpretation agrees with projecting the log of each operation. -/
theorem mapLog_interpret [Monoid Second] (f : ValueLog Address Value →* Second)
    (program : Program Address Value Result) (access : Access Address Value State) :
    LoggedState.mapLog f (program.interpret access) =
      program.liftM (fun op => LoggedState.mapLog f (access.logOp op)) :=
  (LoggedState.isMonadHom_mapLog f).map_freeMLiftM access.logOp program

/-- On success the log replays from the initial state to the returned state.
This applies to interpreted access programs, whose operations determine the
log. Replay consumes valued events. -/
theorem replays_of_run {program : Program Address Value Result} {access : Access Address Value State}
    {initial final : State} {result : Result} {log : ValueLog Address Value}
    (success : LoggedState.run (program.interpret access) initial = some ((result, final), log)) :
    Trace.Replays access (FreeMonoid.toList log) initial final :=
  Proofs.Semantics.ReadWrite.Writer.State.replays_of_run success

end Program

end Silmaril.Semantics.ReadWrite
