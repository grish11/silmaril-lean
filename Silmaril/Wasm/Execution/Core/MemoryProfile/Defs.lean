module

public import Silmaril.Wasm.Execution.Core.Intrinsic.OpSem.Defs

@[expose] public section

/-! # A fixed one-memory Core profile

This local policy accepts flat `i32` code: constants, addition, and full-width
loads and stores at memory index zero with zero alignment exponent and offset.
It is not a Wasm version or a binary-encoder judgment. Dynamic access bounds
belong to execution, not profile admission.
-/

namespace Silmaril.Wasm.Execution.Core.MemoryProfile

open Validation Numerics SingleThreaded Semantics.Operational

variable {height input output : Nat}

def index : MemIdx := ⟨0⟩
def load : Admin := .plain (.intLoad .i32 none index memarg0)
def store : Admin := .plain (.intStore .i32 none index memarg0)
def add : Admin := .plain (.intBinOp .i32 .add)
def word (bits : BitVec 32) : Val := .num ⟨.int .i32, bits⟩

def memoryType : MemoryType := ⟨.i32, ⟨1, none⟩⟩
def memory (bytes : ByteArray) : MemInst := ⟨memoryType, bytes⟩
def world (bytes : ByteArray) : Store Unit := { mems := [memory bytes] }
def frame : Frame := { module := { mems := [0] } }
def context : Context := { mems := [memoryType] }
def config (bytes : ByteArray) (code : List Admin) : Config Unit := ⟨world bytes, frame, code⟩

inductive Allowed : Admin → Prop where
  | word (bits : BitVec 32) : Allowed (word bits).toAdmin
  | add : Allowed add
  | load : Allowed load
  | store : Allowed store
  | trap : Allowed .trap

def InProfile (state : Config Unit) : Prop :=
  (∃ bytes, state.store = world bytes) ∧ state.frame = frame ∧ ∀ inst ∈ state.code, Allowed inst

def resultTypes (height : Nat) : List CValType := List.replicate height Ty.i32

def Admitted (height : Nat) (state : Config Unit) : Prop :=
  ConfigOk state (resultTypes height) ∧ InProfile state

/-- Policy UB is rejection of a state, not a Wasm step or a dynamic trap. -/
def semantics (oracle : GrowOracle) (height : Nat) : WithUB (Config Unit) Intrinsic.Completion :=
  (WithUB.ofOpSem (Intrinsic.rawOrdinary oracle)).enforce (Admitted height)

/-- A top-first stack of exactly `height` i32 words. -/
inductive Stack : Nat → Type where
  | nil : Stack 0
  | push {height : Nat} (bits : BitVec 32) (stack : Stack height) : Stack (height + 1)

def Stack.values : {height : Nat} → Stack height → List Val
  | _, .nil => []
  | _, .push bits stack => stack.values ++ [word bits]

/-- Stack effects are checked structurally, including for a program whose
execution will trap. Literal instructions are already Core values. -/
inductive Code : Nat → Nat → Type where
  | done {height : Nat} : Code height height
  | const {height output : Nat} (bits : BitVec 32) (tail : Code (height + 1) output) : Code height output
  | add {height output : Nat} (tail : Code (height + 1) output) : Code (height + 2) output
  | load {height output : Nat} (tail : Code (height + 1) output) : Code (height + 1) output
  | store {height output : Nat} (tail : Code height output) : Code (height + 2) output

def Code.erase : {input output : Nat} → Code input output → List Admin
  | _, _, .done => []
  | _, _, .const bits tail => (word bits).toAdmin :: tail.erase
  | _, _, .add tail => MemoryProfile.add :: tail.erase
  | _, _, .load tail => MemoryProfile.load :: tail.erase
  | _, _, .store tail => MemoryProfile.store :: tail.erase

def Code.start (code : Code input output) (stack : Stack input) (bytes : ByteArray) : Config Unit :=
  config bytes (vals stack.values ++ code.erase)

structure Answer where
  bytes : ByteArray
  result : Result

def Answer.erase (answer : Answer) : Config Unit := config answer.bytes answer.result.toAdmin

/-- Independent recursion on the typed tape, using Core's byte primitives.
`none` from a byte primitive is an OOB trap, not UB or fuel exhaustion. -/
def Code.eval : {input output : Nat} → Code input output → Stack input → ByteArray → Answer
  | _, _, .done, stack, bytes => ⟨bytes, .values stack.values⟩
  | _, _, .const bits tail, stack, bytes => tail.eval (.push bits stack) bytes
  | _, _, .add tail, .push right (.push left stack), bytes => tail.eval (.push (left + right) stack) bytes
  | _, _, .load tail, .push address stack, bytes =>
    match Memory.load bytes address.toNat 4 with
    | none => ⟨bytes, .trap⟩
    | some bits => tail.eval (.push bits stack) bytes
  | _, _, .store tail, .push bits (.push address stack), bytes =>
    match Memory.store bytes address.toNat (count := 4) bits with
    | none => ⟨bytes, .trap⟩
    | some after => tail.eval stack after

/-- Admission uses actual Core typing, separately from the tape's stack effects.
No page-count or instance validity assumption is inferred from execution. -/
structure Program (output : Nat) where
  bytes : ByteArray
  code : Code 0 output
  wellTyped : ConfigOk (code.start .nil bytes) (resultTypes output)

def opSem (oracle : GrowOracle) (output : Nat) :
    HasOpSem (Program output) (Config Unit) Intrinsic.Completion where
  initial program state := state = program.code.start .nil program.bytes
  semantics := semantics oracle output

end Silmaril.Wasm.Execution.Core.MemoryProfile
