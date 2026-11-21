module

public import Silmaril.Wasm.Execution.Core.Entry.Defs

@[expose] public section

namespace Silmaril.Wasm.Execution.Core.GlobalProfile

open Validation Numerics Semantics.Operational Intrinsic

def index : GlobalIdx := ⟨0⟩
def get : Admin := .plain (.globalGet index)
def set : Admin := .plain (.globalSet index)
def bin (op : IntBinOp) : Admin := .plain (.intBinOp .i32 op)
def type (mutability : Mutability) : CGlobalType := ⟨mutability, .i32⟩
def global (mutability : Mutability) (value : BitVec 32) : GlobalInst := ⟨type mutability, .i32 value⟩
def store (mutability : Mutability) (value : BitVec 32) : Store Empty := { globals := [global mutability value] }
def frame : Frame := { module := { globals := [0] } }
def context (mutability : Mutability) : Context := { globals := [type mutability] }
def config (mutability : Mutability) (value : BitVec 32) (code : List Admin) : Config Empty :=
  ⟨store mutability value, frame, code⟩

/-- A closed integer tape with one `i32` global. Mutable writes have a
different index from immutable reads. The caller supplies the initial word;
this experiment does not link imports or allocate a whole module. -/
inductive Code : Mutability → List IntType → List IntType → Type where
  | done {mutability stack} : Code mutability stack stack
  | const {mutability stack results} (value : BitVec 32) (tail : Code mutability (.i32 :: stack) results) :
      Code mutability stack results
  | get {mutability stack results} (tail : Code mutability (.i32 :: stack) results) : Code mutability stack results
  | set {stack results} (tail : Code .var stack results) : Code .var (.i32 :: stack) results
  | bin {mutability stack results} (op : IntBinOp) (tail : Code mutability (.i32 :: stack) results) :
      Code mutability (.i32 :: .i32 :: stack) results

variable {mutability : Mutability} {input output : List IntType}

def Code.erase : {mutability : Mutability} → {input output : List IntType} → Code mutability input output → List Admin
  | _, _, _, .done => []
  | _, _, _, .const value tail => (Val.i32 value).toAdmin :: tail.erase
  | _, _, _, .get tail => GlobalProfile.get :: tail.erase
  | _, _, _, .set tail => GlobalProfile.set :: tail.erase
  | _, _, _, .bin op tail => GlobalProfile.bin op :: tail.erase

def Code.start (code : Code mutability input output) (stack : Values input) (value : BitVec 32) : Config Empty :=
  config mutability value (vals stack.erase.reverse ++ code.erase)

structure Answer where
  globalValue : BitVec 32
  result : Result

def Answer.erase (answer : Answer) (mutability : Mutability) : Config Empty :=
  config mutability answer.globalValue answer.result.toAdmin

/-- Independent interpretation. A checked arithmetic failure retains the
global value at the trap, which may differ from the entry value. -/
def Code.eval : {mutability : Mutability} → {input output : List IntType} →
    Code mutability input output → Values input → BitVec 32 → Answer
  | _, _, _, .done, stack, value => ⟨value, .values stack.erase.reverse⟩
  | _, _, _, .const bits tail, stack, value => tail.eval (.cons (kind := .i32) bits stack) value
  | _, _, _, .get tail, stack, value => tail.eval (.cons (kind := .i32) value stack) value
  | _, _, _, .set tail, .cons bits stack, _ => tail.eval stack bits
  | _, _, _, .bin op tail, .cons right (.cons left stack), value =>
    match intBinOp .i32 op left right with
    | .ok bits => tail.eval (.cons (kind := .i32) bits stack) value
    | .error _ => ⟨value, .trap⟩

structure Program (mutability : Mutability) (results : List IntType) where
  value : BitVec 32
  code : Code mutability [] results

/-- The profile restriction here is a typed program-entry restriction. On
runtime configurations the only UB guard is actual Core `ConfigOk`. -/
def opSem (P : Profile) (mutability : Mutability) (results : List IntType) :
    HasOpSem (Program mutability results) (Config Empty) Completion where
  initial program state := state = program.code.start .nil program.value
  semantics := Entry.policy P SingleThreaded.Det.noHost (stackTypes results)

end Silmaril.Wasm.Execution.Core.GlobalProfile
