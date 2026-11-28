module

public import Silmaril.Semantics.ReadWrite.Writer.Defs
public import Cslib.Foundations.Control.Monad.Free

/-! Access programs interpreted in a stateful Writer with Option failure. -/

@[expose] public section
namespace Silmaril.Semantics.ReadWrite

universe u
variable {Address Value State Result First Second : Type u}

/-- State and chronological output over a failing computation. The standard
`StateT`, `WriterT` and `Option` instances supply the lawful monad. -/
abbrev LoggedState (State Log : Type u) := StateT State (WriterT Log Option)

/-- A failed run returns `none`, with no final state or prefix log. -/
def LoggedState.run [Monoid First] (action : LoggedState State First Result) (initial : State) :
    Option ((Result × State) × First) :=
  (StateT.run action initial).run

/-- Apply a monoid homomorphism to the log of a stateful Writer. -/
def LoggedState.mapLog [Monoid First] [Monoid Second] (f : First →* Second)
    (action : LoggedState State First Result) : LoggedState State Second Result :=
  fun state => WriterLog.mapLog f (StateT.run action state)

/-- The only effects available to an access program. A read returns its
observed value and a write returns a unit reply. -/
inductive AccessOp (Address Value : Type u) : Type u → Type u where
  | read (address : Address) : AccessOp Address Value Value
  | write (address : Address) (value : Value) : AccessOp Address Value PUnit

/-- The free monad over reads and writes, with no operations for independently
changing state or emitting a log. -/
abbrev Program (Address Value : Type u) := Cslib.FreeM (AccessOp Address Value)

def Program.read (address : Address) : Program Address Value Value :=
  .lift (.read address)

def Program.write (address : Address) (value : Value) : Program Address Value PUnit :=
  .lift (.write address value)

/-- Execute one backend operation and record a valued event on success. -/
def Access.logOp (access : Access Address Value State) :
    AccessOp Address Value Result → LoggedState State (ValueLog Address Value) Result
  | .read address => fun state => WriterT.mk ((access.read state address).map fun value =>
      ((value, state), Trace.toLog [.read address value]))
  | .write address value => fun state => WriterT.mk ((access.write state address value).map fun next =>
      ((⟨⟩, next), Trace.toLog [.write address value]))

/-- Execute a restricted program against an access backend. Successful runs
emit the valued trace used for replay. Erased logs cannot be used for replay. -/
def Program.interpret (program : Program Address Value Result) (access : Access Address Value State) :
    LoggedState State (ValueLog Address Value) Result :=
  program.liftM access.logOp

end Silmaril.Semantics.ReadWrite
