module

public import Silmaril.Elf.Region.Defs
public import Silmaril.Semantics.Function.Defs
public import Silmaril.X86.Decompile.Functions

/-! # Candidate calls from file-backed executable ELF windows

`Plan` is a declared interface. An entry in `stubs` represents an explicit
PLT/external interpretation, not a dynamic-loader theorem. The runner does
not infer symbols, apply relocations, choose load bias, or read zero-fill.
Its abstract context is the source object, not a globally unique address.
-/

@[expose] public section
namespace Silmaril.Elf.Region.Calls
open Silmaril.Semantics.Function
open Silmaril.Machine.Region (BinaryObject ByteSource)
open Silmaril.X86 (Byte)
open Silmaril.X86.Decompile (FunctionSpec Decoded Partition Accepted)

structure Stub where
  address : Nat
  symbol : String
  deriving DecidableEq, BEq, Repr

abbrev signature : Signature := ⟨BinaryObject, Nat, Stub, Nat, FunctionSpec⟩

structure Plan where
  functions : List FunctionSpec
  stubs : List Stub
  tailSites : List Nat := []

inductive Gap where
  | missingWindow (entry : Nat)
  | unsupported (site : Nat)
  | unresolvedDirect (site target : Nat)
  | unclassifiedJump (site : Nat)
  | unclassifiedFallthrough (site target : Nat)
  deriving DecidableEq, Repr

inductive Parsed where
  | instruction (decoded : Decoded)
  | indirectCall (site : Nat)
  | indirectJump (site : Nat)
  | gap (site : Nat)
  deriving Repr

def readWindow (source : BinaryObject) (entry size : Nat) : Option (List Byte) := do
  if size = 0 ∨ 2 ^ 64 ≤ entry + size then none else
    (List.range size).mapM fun offset =>
      (source.codeByte ⟨.virtual, entry + offset⟩).map UInt8.toBitVec

/-- Exact encodings `FF D0` and `FF E0` keep their own syntactic observations
even though the selected interpreter does not implement them. Other missing
instructions leave a gap and stop the scan; bytes are never skipped. -/
def scan : Nat → Nat → List Byte → List Parsed
  | _, _, [] => []
  | 0, addr, _ => [.gap addr]
  | fuel + 1, addr, 0xff#8 :: 0xd0#8 :: rest => .indirectCall addr :: scan fuel (addr + 2) rest
  | fuel + 1, addr, 0xff#8 :: 0xe0#8 :: rest => .indirectJump addr :: scan fuel (addr + 2) rest
  | fuel + 1, addr, bytes =>
    match Silmaril.X86.Ext.decode bytes with
    | none => [.gap addr]
    | some (instr, size) =>
      if size = 0 ∨ bytes.length < size then [.gap addr] else
        .instruction ⟨addr, instr, size⟩ :: scan fuel (addr + size) (bytes.drop size)

/-- Ambiguous local aliases, duplicate stub declarations and collisions are
unresolved. A local stub is not silently identified with its foreign leaf. -/
def resolve (plan : Plan) (target : Nat) : Option (Node signature) :=
  match plan.functions.filter (fun spec => spec.entry == target),
      plan.stubs.filter (fun stub => stub.address == target) with
  | [_], [] => some (.localFn target)
  | [], [stub] => some (.foreign stub)
  | _, _ => none

inductive Finding where
  | direct (site : CallSite signature) (encodedTarget : Nat) (callee : Node signature)
  | indirect (site : CallSite signature)
  | gap (reason : Gap)

def reportDirect (plan : Plan) (site : CallSite signature) (dest : Nat) : Finding :=
  match resolve plan dest with
  | some callee => .direct site dest callee
  | none => .gap (.unresolvedDirect site.site dest)

def findings (plan : Plan) (body : FunctionSpec) : Parsed → List Finding
  | .gap addr => [.gap (.unsupported addr)]
  | .indirectCall addr => .indirect ⟨body.entry, addr, .invoke⟩ ::
      (if decide (body.Covers (addr + 2)) then [] else [.gap (.unclassifiedFallthrough addr (addr + 2))])
  | .indirectJump addr =>
    if plan.tailSites.contains addr then [.indirect ⟨body.entry, addr, .tail⟩]
    else [.gap (.unclassifiedJump addr)]
  | .instruction instr => instr.edges.flatMap fun edge => match edge with
    | .call dest => [reportDirect plan ⟨body.entry, instr.addr, .invoke⟩ dest]
    | .jump dest =>
      if plan.tailSites.contains instr.addr then [reportDirect plan ⟨body.entry, instr.addr, .tail⟩ dest]
      else if decide (body.Covers dest) then [] else [.gap (.unclassifiedJump instr.addr)]
    | .branch dest => if decide (body.Covers dest) then [] else [.gap (.unclassifiedJump instr.addr)]
    | .fallthrough dest => if decide (body.Covers dest) then [] else [.gap (.unclassifiedFallthrough instr.addr dest)]
    | _ => []

structure Row where
  body : FunctionSpec
  available : Bool
  findings : List Finding

def extractRow (source : BinaryObject) (plan : Plan) (body : FunctionSpec) : Row :=
  match readWindow source body.entry body.size with
  | none => ⟨body, false, [.gap (.missingWindow body.entry)]⟩
  | some bytes => ⟨body, true, (scan bytes.length body.entry bytes).flatMap (findings plan body)⟩

abbrev Inventory := List Row

def extract (source : BinaryObject) (plan : Plan) : Inventory :=
  plan.functions.map (extractRow source plan)

def rows (inventory : Inventory) : Decomposition signature :=
  fun name body => ∃ row ∈ inventory, row.available = true ∧ row.body = body ∧ row.body.entry = name

def IndirectAt (inventory : Inventory) (site : CallSite signature) : Prop :=
  ∃ row ∈ inventory, Finding.indirect site ∈ row.findings

/-- A client can preserve Top or provide a target upper bound at each observed
indirect site. To use a narrower bound for execution it must prove coverage. -/
def boundedAnalysis (inventory : Inventory) (targets : CallSite signature → Option (Set (Node signature))) :
    Analysis signature where
  direct site callee := ∃ row ∈ inventory, ∃ dest, Finding.direct site dest callee ∈ row.findings
  indirect site bound := bound = targets site ∧ IndirectAt inventory site

def analysis (inventory : Inventory) : Analysis signature := boundedAnalysis inventory fun _ => none

def ReadableRows (source : BinaryObject) (plan : Plan) (proposed : Decomposition signature) : Prop :=
  ∀ name body, proposed name body → body ∈ plan.functions ∧ body.entry = name ∧
    ∃ bytes, readWindow source body.entry body.size = some bytes

/-- Evidence of classification at a particular decoded location in a
declared window. It does not assert that the location is executed. -/
def FindingAt (source : BinaryObject) (plan : Plan) (finding : Finding) : Prop :=
  ∃ body ∈ plan.functions, ∃ bytes, readWindow source body.entry body.size = some bytes ∧
    ∃ item ∈ scan bytes.length body.entry bytes, finding ∈ findings plan body item

def asModel (source : BinaryObject) (inventory : Inventory) : Model signature :=
  bundle (fun context name body => context = source ∧ rows inventory name body)
    (fun context edge => context = source ∧ (analysis inventory).may edge) (fun _ _ => False)

/-- Wrapper over the existing stricter contiguous partition checker. This
profile rejects any unsupported instruction; it does not implement PLT or
indirect transfers that this checker does not understand. -/
def checkPartition (source : BinaryObject) (entry size : Nat) (plan : Partition) :
    Option (Except Silmaril.X86.Decompile.Reject Accepted) :=
  (readWindow source entry size).map fun bytes =>
    Silmaril.X86.Decompile.check ⟨entry, bytes⟩ plan bytes.length

def DirectEdge (inventory : Inventory) (source dest : Node signature) : Prop :=
  (directGraph (analysis inventory).may).edge source dest

def directArcs (inventory : Inventory) : List (Nat × Node signature) :=
  inventory.flatMap fun row => row.findings.filterMap fun finding => match finding with
    | .direct site _ callee => some (site.caller, callee)
    | _ => none

def arcSuccessors (arcs : List (Nat × Node signature)) : Node signature → List (Node signature)
  | .foreign _ => []
  | .localFn source => arcs.filterMap fun (caller, callee) =>
    if caller = source then some callee else none

abbrev successors (inventory : Inventory) := arcSuccessors (directArcs inventory)

def nodeEq : Node signature → Node signature → Bool
  | .localFn lhs, .localFn rhs => lhs == rhs
  | .foreign lhs, .foreign rhs => decide (lhs = rhs)
  | _, _ => false

def expandArcs (arcs : List (Nat × Node signature)) (seen : List (Node signature)) : List (Node signature) :=
  seen ++ (seen.flatMap (arcSuccessors arcs)).filter fun node => !seen.any (nodeEq node)

abbrev expand (inventory : Inventory) := expandArcs (directArcs inventory)

def reach (inventory : Inventory) (entry : Nat) (rounds : Nat) : List (Node signature) :=
  (expand inventory)^[rounds] [.localFn entry]

def nonemptyReach (inventory : Inventory) (entry : Nat) (rounds : Nat) : List (Node signature) :=
  (expand inventory)^[rounds] (successors inventory (.localFn entry))

def openAt (inventory : Inventory) (entry : Nat) : Bool :=
  let rows := inventory.filter fun row => row.body.entry == entry
  rows.length != 1 || rows.any fun row => row.findings.any fun finding => match finding with
    | .direct .. => false
    | _ => true

def stableArcs (arcs : List (Nat × Node signature)) (seen : List (Node signature)) : Bool :=
  (expandArcs arcs seen).length == seen.length

abbrev stable (inventory : Inventory) := stableArcs (directArcs inventory)

structure Report where
  knownVertices : List (Node signature)
  knownCalls : List (Nat × Node signature)
  knownFrontier : List Stub
  incomplete : Bool

/-- The finite runner computes known direct projections. It cannot enumerate
Top, future foreign identities, or evidence after a decode gap. A growing
frontier at the fuel limit also marks the result incomplete. -/
def query (inventory : Inventory) (entry rounds : Nat) : Report :=
  let seen := reach inventory entry rounds
  ⟨seen, (directArcs inventory).filter fun (caller, _) => seen.any (nodeEq (.localFn caller)),
    seen.filterMap fun node => match node with | .foreign stub => some stub | _ => none,
    !stable inventory seen || seen.any fun node => match node with
      | .localFn addr => openAt inventory addr
      | .foreign _ => false⟩

/-- Failure retains the partial direct graph and the fact that the caller
must not treat the may frontier as an empty or exact list. -/
def queryDirect (inventory : Inventory) (entry rounds : Nat) : Except Report Report :=
  let report := query inventory entry rounds
  if report.incomplete then .error report else .ok report

end Silmaril.Elf.Region.Calls
