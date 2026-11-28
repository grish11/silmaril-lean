module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.MLIR.CF.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Phi.Defs

/-! Typed live word transport into the actual CF dispatcher chain for a resized RTL family. -/

@[expose] public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA (Func Prog Term step)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg PortTy)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.MLIR.CF (i64)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF
open Silmaril.SSA.SeaOfNodes.MLIR.Lowering (Scope lowerCode)
open Silmaril.SSA.RVSDG (Tuple Locals Origin extend)
open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.Pure (Operands)
open Silmaril.MLIR.CF (Cfg Block Terminator)

abbrev wordsTy (n : Nat) : List Width := List.replicate n i64

abbrev Program (captures bank : Nat) (entrySigs sigs : List (List (Diamond.Ty Width))) :=
  Bank.Program (wordsTy captures) (wordsTy bank) i64 entrySigs sigs

abbrev Live (captures bank : Nat) (sigs : List (List (Diamond.Ty Width))) :=
  List (Origin (Loop.headerPorts (Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.inputSorts (wordsTy captures)) (Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.inputSorts (wordsTy bank)))
    (extend [] sigs) (.value (.data i64)))

/-- The RTL register corresponding to a typed header origin. The resized
capture count fixes the shared numbering of captures and bank arguments. -/
def liveRegs {captures bank : Nat} {sigs : List (List (Diamond.Ty Width))}
    (live : Live captures bank sigs) : List Reg :=
  live.map (fun wire => register wire.address)

def liveOperands {args : List (Diamond.Ty Width)} {past : List (List (Diamond.Ty Width))}
    {Δ : List Width} (scope : Scope args past Δ) :
    (live : List (Origin args past (.value (.data i64)))) → Operands Δ (wordsTy live.length)
  | [] => .nil
  | wire :: rest => .cons (scope.resolveValue wire) (liveOperands scope rest)

/-- Snapshot the named words in order in the source producer environment. -/
def readLive {args : List (Diamond.Ty Width)} {past : List (List (Diamond.Ty Width))}
    (values : Tuple (Diamond.Val Silmaril.SSA.SeaOfNodes.MLIR.Word) args)
    (locals : Locals (Diamond.Val Silmaril.SSA.SeaOfNodes.MLIR.Word) past) :
    (wires : List (Origin args past (.value (.data i64)))) → Env (wordsTy wires.length)
  | [] => .nil
  | wire :: rest => .cons (Diamond.read Loop.MLIR.CF.model wire values locals) (readLive values locals rest)

/-- A row checks the complete feedback column and, for a conditional, the
selector and the exact continuation occurrence. -/
inductive Row (scope : List Reg) (bank tests : Nat) where
  | last (column : Phi.Packet scope bank)
  | test (selector : Fin scope.length) (column : Phi.Packet scope bank) (next : Fin (tests + 1))

variable {captures bank tests : Nat} {scope : List Reg}

def Row.column : Row scope bank tests → Phi.Packet scope bank
  | .last column | .test _ column _ => column

def Row.term (row : Row scope bank tests) : Term Reg :=
  match row with
  | .last column => .jump 1 column.registers
  | .test selector column next => .cond scope[selector] 1 column.registers (occurrence next).1 []

def checkTerm (scope : List Reg) (bank : Nat) (slot : Fin (tests + 1)) :
    Term Reg → Option (Row scope bank tests)
  | .jump target regs =>
    if target = 1 ∧ slot.val = tests then (Phi.checkPacket scope bank regs).map .last else none
  | .cond selector target regs next tail =>
    if later : slot.val + 1 < tests + 1 then
      if target = 1 ∧ next = (occurrence ⟨slot.val + 1, later⟩).1 ∧ tail = [] then
        if found : selector ∈ scope then
          (Phi.checkPacket scope bank regs).map
            (fun column => .test ⟨scope.idxOf selector, List.idxOf_lt_length_of_mem found⟩ column
              ⟨slot.val + 1, later⟩)
        else none
      else none
    else none
  | _ => none

def readRow (fn : Func Reg) (scope : List Reg) (bank : Nat) (slot : Fin (tests + 1)) :
    Option (Row scope bank tests) :=
  match fn.block? (occurrence slot).1 with
  | some ⟨[], [], term⟩ => checkTerm scope bank slot term
  | _ => none

/-- All positional RTL rows are admitted in the same explicit live scope. -/
structure Plan (fn : Func Reg) (scope : List Reg) (bank tests : Nat) : Type where
  present : ∀ slot : Fin (tests + 1), (readRow fn scope bank slot).isSome

def check (fn : Func Reg) (scope : List Reg) (bank tests : Nat) : Option (Plan fn scope bank tests) :=
  if good : ∀ slot : Fin (tests + 1), (readRow fn scope bank slot).isSome then some ⟨good⟩ else none

def Plan.row {fn : Func Reg} (plan : Plan fn scope bank tests) (slot : Fin (tests + 1)) :
    Row scope bank tests :=
  (readRow fn scope bank slot).get (plan.present slot)

inductive Label (live bank tests : Nat) : List Width → Type where
  | header : Label live bank tests (wordsTy bank)
  | exit : Label live bank tests [i64]
  | dispatch (slot : Fin (tests + 1)) : Label live bank tests (wordsTy live)

/-- A dispatcher can read only its explicit live arguments and the immutable captures. -/
def argAt {Γ : List Width} : (live : Nat) → Fin live → Var (wordsTy live ++ Γ) i64
  | 0, i => i.elim0
  | n + 1, i => Fin.cases .here (fun j => .there (argAt n j)) i

def project {Γ : List Width} (resolve : Fin scope.length → Var Γ i64) :
    {count : Nat} → Phi.Packet scope count → Operands Γ (wordsTy count)
  | _, .nil => .nil
  | _, .cons i rest => .cons (resolve i) (project resolve rest)

def forward {Γ : List Width} :
    (live : Nat) → (Fin live → Var Γ i64) → Operands Γ (wordsTy live)
  | 0, _ => .nil
  | live + 1, resolve => .cons (resolve 0) (forward live (fun i => resolve i.succ))

/-- The conditional uses `arith.cmpi ult` against zero, which tests the
same bit patterns as RTL's nonzero branch. -/
def dispatcher (live : Nat) (width : scope.length = live) (row : Row scope bank tests) :
    Block TargetOp (Label live bank tests) (wordsTy live ++ wordsTy captures) [i64] :=
  let value := fun i : Fin scope.length => argAt live (i.cast width)
  match row with
  | .last column => .terminator (.br ⟨.header, project value column⟩)
  | .test selector column next =>
    .letOp (.original (.constant (0 : Word))) .nil
      (.letOp (.ult i64) (.cons .here (.cons (.there (value selector)) .nil))
        (.terminator (.condBr .here
          ⟨.header, project (fun i => .there (.there (value i))) column⟩
          ⟨.dispatch next, forward live (fun i => .there (.there (argAt live i)))⟩)))

def wordList : {n : Nat} → Env (wordsTy n) → List Word
  | 0, .nil => []
  | _ + 1, .cons value rest => value :: wordList rest

/-- Relate every transported slot to the same pre-transfer RTL register file. -/
def Snapshot {Γ : List Width} {live : Nat} (width : scope.length = live)
    (env : Env (wordsTy live ++ Γ)) (frame : Frame Reg) : Prop :=
  ∀ i : Fin scope.length, frame.get scope[i] = some (env.get (argAt live (i.cast width)))

/-- Interpret the observed CF successor as the corresponding actual machine step.
The successful edge is occurrence zero of the current dispatcher, regardless of
how many other dispatchers target the header. -/
def StepAgreement (prog : Prog Reg) (slot : Fin (tests + 1)) (frame : Frame Reg) (mem : Memory)
    {live : Nat} (packet : Env (wordsTy live)) :
    Silmaril.MLIR.CF.Frame (Label live bank tests) ⊕ Env [i64] → Prop
  | .inl ⟨.header, values⟩ =>
    ∃ source target regs latched,
      prog.block? 0 (occurrence slot).1 = some source ∧
      source.term.args[(occurrence slot).2]? = some (1, regs) ∧
      frame.readAll regs = some (wordList values) ∧
      prog.block? 0 1 = some target ∧
      step prog ⟨⟨0, (occurrence slot).1, 0⟩, frame, [], mem⟩ =
        .running ⟨⟨0, 1, 0⟩, latched, [], mem⟩ ∧
      latched.readAll target.params = some (wordList values)
  | .inl ⟨.dispatch next, forwarded⟩ =>
    forwarded = packet ∧ ∃ source,
      prog.block? 0 (occurrence slot).1 = some source ∧
      source.term.args[1]? = some ((occurrence next).1, []) ∧
      step prog ⟨⟨0, (occurrence slot).1, 0⟩, frame, [], mem⟩ =
        .running ⟨⟨0, (occurrence next).1, 0⟩, frame, [], mem⟩
  | _ => False

variable {entrySigs sigs : List (List (Diamond.Ty Width))}

def headerTerm (g : Program captures bank entrySigs sigs) (live : Live captures bank sigs)
    {Δ : List Width}
    (names : Scope (Loop.headerPorts (Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.inputSorts (wordsTy captures)) (Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.inputSorts (wordsTy bank)))
      (extend [] sigs) Δ) : Terminator (Label live.length bank tests) [i64] Δ :=
  .condBr (names.resolveValue g.predicate) ⟨.dispatch 0, liveOperands names live⟩
    ⟨.exit, .cons (names.resolveValue g.result) .nil⟩

/-- Emit the canonical producer tables and put the live snapshot on the
header edge. Later blocks receive those words as real CF block arguments. -/
def lower {fn : Func Reg} (g : Program captures bank entrySigs sigs) (live : Live captures bank sigs)
    (plan : Plan fn (liveRegs live) bank tests) :
    Cfg TargetOp (Label live.length bank tests) (wordsTy captures) [i64] where
  entry := lowerCode Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.opcode g.preheader (entryScope _) (fun names =>
    .br ⟨.header, Bank.bankOperands names (g.phiInputs .entry)⟩)
  block
    | .header => lowerCode Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.opcode g.header (Bank.headerScope _ _) (headerTerm g live)
    | .exit => .terminator (.ret (.cons .here .nil))
    | .dispatch slot => dispatcher live.length (List.length_map ..) (plan.row slot)

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR
