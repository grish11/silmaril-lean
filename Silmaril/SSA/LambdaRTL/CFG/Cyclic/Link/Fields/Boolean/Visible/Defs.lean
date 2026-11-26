module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Defs
public import Silmaril.Semantics.ITree.Trace.Finite.Silence.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Prod

/-! A one-field Boolean packet language with a visible unary application at
a block boundary. The primitive's complete reply domain is Bool. -/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible

open Silmaril.Elgot.ITree (Tree vis diverge ExchangePath)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.Bridge.NamedFlat (treeModel treeExitNumber)
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction (Primitive)
open Silmaril.Elgot.ITree.Finite (Event)

variable {F : Type} {a b : Nat}

inductive Instruction (F K : Type) where
  | jump (target : K)
  | branch (onTrue onFalse : K)
  | apply (symbol : F) (target : K)

/-- Every block consumes a single Boolean packet. A branch forwards it
and a primitive replaces its field with the actual reply. -/
structure Program (F : Type) (inputs outputs : Nat) where
  locals : Nat
  entry : Fin inputs → Label locals outputs
  block : Fin locals → Instruction F (Label locals outputs)

namespace Program

variable (program : Program F a b)

-- The named runner shares the weak tree carrier's universe. The finite
-- address and register encodings are lifted without changing their keys.
abbrev Register := ULift.{1} Nat
abbrev Address (program : Program F a b) := ULift.{1} (Label program.locals b)
abbrev State (program : Program F a b) := ULift.{1} (Label program.locals b × Bool)
abbrev Result (b : Nat) := ULift.{1} (Fin b × Bool)
abbrev Atom := PUnit.{2}

def states : Finset program.State :=
  (Finset.univ : Finset (Label program.locals b × Bool)).map ⟨ULift.up, ULift.up_injective⟩

theorem mem_states (state : program.State) : state ∈ program.states := by
  cases state
  simp [states]

def start (input : Fin a) (flag : Bool) : program.State := ⟨program.entry input, flag⟩

def step (state : program.State) : Silmaril.Elgot.ITree.Finite.Step (F × Bool) (Result b) program.State :=
  match state.down with
  | (.inr output, flag) => .inl (.result ⟨output, flag⟩)
  | (.inl index, flag) =>
    match program.block index with
    | .jump target => .inr ⟨target, flag⟩
    | .branch yes no => .inr ⟨if flag then yes else no, flag⟩
    | .apply symbol target => .inl (.request (symbol, flag) fun reply => ⟨target, reply⟩)

/-- The compiled fragment has no immediate silent stop instruction. Its
normalized no-root observations come from repeats in silent control. -/
theorem step_ne_stop (state : program.State) : program.step state ≠ .inl .stop := by
  rcases state with ⟨index | port, flag⟩
  · cases row : program.block index <;> simp [step, row]
  · simp [step]

def compiledBlock (instruction : Instruction F (Label program.locals b)) :
    Block Register program.Address F :=
  let packet : Register := ⟨0⟩
  let field : Register := ⟨1⟩
  let tail : Register := ⟨2⟩
  let unused : Register := ⟨3⟩
  ⟨packet, match instruction with
  | .jump target => .term (.br ⟨target⟩ (.var packet))
  | .branch yes no =>
    .let2 field tail (.val (.var packet)) (.term (.case (.val (.var field))
      unused (.br ⟨yes⟩ (.var packet)) unused (.br ⟨no⟩ (.var packet))))
  | .apply symbol target =>
    .let2 field tail (.val (.var packet)) (.let1 field (.app symbol (.var field))
      (.term (.br ⟨target⟩ (.pair (.var field) (.var tail)))))⟩

def compile (input : Fin a) : CFG Register program.Address F :=
  ⟨.term (.br ⟨program.entry input⟩ (.var ⟨0⟩)),
    (List.finRange program.locals).map fun i => (⟨.inl i⟩, program.compiledBlock (program.block i))⟩

def exits : List program.Address :=
  (List.finRange b).map fun i => ⟨.inr i⟩

def bit (flag : Bool) : Value Atom := if flag then .inl .unit else .inr .unit

def encode (flag : Bool) : Value Atom := .pair (bit flag) .unit

def renderResult (result : Result b) : Nat × Value Atom :=
  (result.down.1.val, encode result.down.2)

def store (flag : Bool) : Register → Value Atom :=
  upd (fun _ => .unit) ⟨0⟩ (encode flag)

def primitive : Primitive (Event (F × Bool)) F Atom := fun symbol value =>
  match value with
  | .inl .unit => vis (.ask (symbol, true)) (fun reply => pure (bit reply))
  | .inr .unit => vis (.ask (symbol, false)) (fun reply => pure (bit reply))
  | _ => diverge

/-- Number the named runner's public results in the shared external interface. -/
noncomputable def observe (input : Fin a) (flag : Bool) :
    Tree (Event (F × Bool)) (Nat × Value Atom) :=
  CFG.Cyclic.runSSA (treeModel.{0, 0} primitive) (program.compile input) (store flag) >>=
    fun result => pure (treeExitNumber program.exits result)

def refinementAt? [DecidableEq F] (right : Program F a b) (input : Fin a) (flag : Bool) : Bool :=
  Silmaril.Elgot.ITree.Finite.compare program.states right.states program.step right.step
    (program.start input flag) (right.start input flag)

/-- Check all public entries and all one-field Boolean packets. -/
def refinement? [DecidableEq F] (right : Program F a b) : Bool :=
  (List.finRange a).all fun input =>
    (packets 1).all fun packet => program.refinementAt? right input (packet 0)

/-- Check for a silent cycle after the recorded exchanges on this input. -/
def silentAfter? [DecidableEq F] (input : Fin a) (flag : Bool)
    (path : ExchangePath (Event (F × Bool))) : Bool :=
  Silmaril.Elgot.ITree.Finite.silentAfter? program.step program.states (program.start input flag) path

def refinementAtWithSilence? [DecidableEq F] (right : Program F a b) (input : Fin a) (flag : Bool) : Bool :=
  program.refinementAt? right input flag && right.refinementAt? program input flag

def refinementWithSilence? [DecidableEq F] (right : Program F a b) : Bool :=
  program.refinement? right && right.refinement? program

end Program

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible
