module

public import Silmaril.Machine.SeaOfNodes.Diamond.RTL.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.Defs
public import Silmaril.SSA.SeaOfNodes.GVN.Defs
public import Silmaril.SSA.RVSDG.Isomorphism.Defs

/-! # Typed word columns and routed all-i64 RTL loops -/

@[expose] public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing

open Silmaril.Machine.Lir (Binop Word ofBool)
open Silmaril.Machine.RTL.SSA (Block Func Prog)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg WordOp emitOpsWith model word)
open Silmaril.SSA.RVSDG (Address Origin Port Tuple Wires extend)
open Silmaril.SSA.SeaOfNodes.Diamond (Dataflow Val dataPorts)
open Silmaril.SSA.SeaOfNodes.Loop (Graph Incoming appendTuple)
open Silmaril.SSA.SeaOfNodes.GVN (keepOrigin newest weaken)

abbrev wordPort : PortTy := .value word
abbrev wordSorts (n : Nat) := List.replicate n word
abbrev wordPorts (n : Nat) : List PortTy := dataPorts (wordSorts n)
abbrev WordTuple (n : Nat) := Tuple (Val model.value) (wordPorts n)
abbrev ArgumentColumn (scope arity : Nat) := Wires (wordPorts scope) [] (wordPorts arity)

/-- Header operand registers preserve the native argument positions. The
producer register namespace is separate from both banks of arguments. -/
def register : Address → Reg
  | .arg i => .arg i
  | .output i _ => .node i

/-- Emit the complete ordered operand column for a single transfer. -/
def emitColumn {args : List PortTy} {past : List (List PortTy)} {arity : Nat}
    (wires : Wires args past (wordPorts arity)) : List Reg :=
  wires.addresses.map register

def words : {n : Nat} → WordTuple n → List Word
  | 0, .nil => []
  | _ + 1, .cons head tail => head :: words tail

def argumentPort : (n : Nat) → Fin n → Port (wordPorts n) wordPort
  | 0, i => i.elim0
  | n + 1, i => Fin.cases .head (fun j => .tail (argumentPort n j)) i

/-- Check the arity and each source argument index before building typed
wires. Duplicate operand indices are valid. -/
def checkColumn (scope : Nat) : (arity : Nat) → List Nat → Option (ArgumentColumn scope arity)
  | 0, [] => some .nil
  | arity + 1, i :: rest =>
    if h : i < scope then
      (checkColumn scope arity rest).map (.cons (.arg (argumentPort scope ⟨i, h⟩)))
    else none
  | _, _ => none

/-- Extend the producer scope of an argument-only column. -/
def extendArguments {args users : List PortTy} (past : List (List PortTy))
    (wires : Wires args [] users) : Wires args past users :=
  wires.map fun _ wire => match wire with
    | .arg p => .arg p
    | .output i _ => i.elim0

abbrev headerSigs : List (List PortTy) := [[wordPort], [wordPort], [wordPort], [.value .predicate]]

theorem wordPorts_eq_replicate (n : Nat) : wordPorts n = List.replicate n wordPort := by
  simp [List.map_replicate]

theorem wordPorts_append (m n : Nat) : wordPorts (m + n) = wordPorts m ++ wordPorts n := by
  simp only [wordPorts_eq_replicate, List.replicate_add]

def prefixPort {pre tail : List PortTy} {t : PortTy} : Port pre t → Port (pre ++ tail) t
  | .head => .head
  | .tail p => .tail (prefixPort p)

def suffixPort {tail : List PortTy} {t : PortTy} :
    (pre : List PortTy) → Port tail t → Port (pre ++ tail) t
  | [], p => p
  | _ :: rest, p => .tail (suffixPort rest p)

/-- The counter occupies slot zero in each tuple. Payload routes may read
any visible argument. A typed result selects one of the carried payloads. -/
structure BankRoutes (payloads : Nat) where
  entry : ArgumentColumn (payloads + 1) payloads
  feedback : Wires (wordPorts (payloads + 1) ++ wordPorts (payloads + 1)) [] (wordPorts payloads)
  result : Fin payloads

def checkBankRoutes (payloads : Nat) (entry feedback : List Nat) (result : Nat) :
    Option (BankRoutes payloads) :=
  if valid : result < payloads then
    (checkColumn (payloads + 1) payloads entry).bind fun initial =>
      (checkColumn ((payloads + 1) + (payloads + 1)) payloads feedback).map fun next =>
        ⟨initial, wordPorts_append (payloads + 1) (payloads + 1) ▸ next, ⟨result, valid⟩⟩
  else none

def BankRoutes.resultPort {payloads : Nat} (r : BankRoutes payloads) :
    Port (wordPorts (payloads + 1)) wordPort :=
  .tail (argumentPort payloads r.result)

def counterPort (payloads : Nat) :
    Port (wordPorts (payloads + 1) ++ wordPorts (payloads + 1)) wordPort :=
  suffixPort (wordPorts (payloads + 1)) .head

/-- A total word instruction for a computed feedback destination. Its
operands and destination are payload slots. The counter has its own slot. -/
inductive FeedbackOp
  | add
  | sub

def FeedbackOp.source : FeedbackOp → WordOp [word, word] word
  | .add => .add
  | .sub => .sub

def FeedbackOp.target : FeedbackOp → Binop
  | .add => .add
  | .sub => .sub

def FeedbackOp.eval : FeedbackOp → Word → Word → Word
  | .add => BitVec.add
  | .sub => BitVec.sub

structure FeedbackSpec where
  operation : FeedbackOp
  destination : Nat
  left : Nat
  right : Nat

structure FeedbackUpdate (payloads : Nat) where
  operation : FeedbackOp
  destination : Fin payloads
  left : Fin payloads
  right : Fin payloads

def FeedbackSpec.check (spec : FeedbackSpec) (payloads : Nat) : Option (FeedbackUpdate payloads) :=
  if dest : spec.destination < payloads then
    if left : spec.left < payloads then
      if right : spec.right < payloads then
        some ⟨spec.operation, ⟨spec.destination, dest⟩, ⟨spec.left, left⟩, ⟨spec.right, right⟩⟩
      else none
    else none
  else none

def payloadPort (payloads : Nat) (p : Fin payloads) :
    Port (wordPorts (payloads + 1)) wordPort :=
  .tail (argumentPort payloads p)

def oldPayloadPort (payloads : Nat) (p : Fin payloads) :
    Port (wordPorts (payloads + 1) ++ wordPorts (payloads + 1)) wordPort :=
  suffixPort (wordPorts (payloads + 1)) (payloadPort payloads p)

def FeedbackUpdate.evalAt {fields arity : Nat} (update : FeedbackUpdate fields)
    (slot : Fin fields → Port (wordPorts arity) wordPort) (old : WordTuple arity) : Word :=
  update.operation.eval (old.get (slot update.left)) (old.get (slot update.right))

abbrev FeedbackUpdate.eval {payloads : Nat} (update : FeedbackUpdate payloads)
    (old : WordTuple (payloads + 1)) : Word :=
  update.evalAt (payloadPort payloads) old

/-- Decode every operation and require distinct destination slots. -/
def checkFeedbackRow (payloads : Nat) (specs : List FeedbackSpec) :
    Option (List (FeedbackUpdate payloads)) := do
  let updates ← specs.mapM (fun spec => spec.check payloads)
  if (updates.map FeedbackUpdate.destination).Nodup then some updates else none

def rowSigs {payloads : Nat} : List (FeedbackUpdate payloads) → List (List PortTy)
  | [] => []
  | _ :: rest => [wordPort] :: rowSigs rest

abbrev headerRowSigs {payloads : Nat} (updates : List (FeedbackUpdate payloads)) :=
  headerSigs ++ rowSigs updates

abbrev bankArgs (arity : Nat) := wordPorts arity ++ wordPorts arity
abbrev headerArgs (payloads : Nat) := bankArgs (payloads + 1)

def FeedbackUpdate.operandsAt {fields arity : Nat} (u : FeedbackUpdate fields)
    (slot : Fin fields → Port (wordPorts arity) wordPort)
    (past : List (List PortTy)) : Wires (bankArgs arity) past [wordPort, wordPort] :=
  .cons (.arg (suffixPort (wordPorts arity) (slot u.left)))
    (.cons (.arg (suffixPort (wordPorts arity) (slot u.right))) .nil)

abbrev FeedbackUpdate.operands {payloads : Nat} (u : FeedbackUpdate payloads)
    (past : List (List PortTy)) := u.operandsAt (payloadPort payloads) past

def rowSuffixAt {fields arity : Nat} (slot : Fin fields → Port (wordPorts arity) wordPort)
    (past : List (List PortTy)) :
    (updates : List (FeedbackUpdate fields)) → Dataflow WordOp (bankArgs arity) past (rowSigs updates)
  | [] => .nil
  | u :: rest => .cons u.operation.source (u.operandsAt slot past)
      (rowSuffixAt slot (past ++ [[wordPort]]) rest)

abbrev rowSuffix {payloads : Nat} (past : List (List PortTy)) :=
  rowSuffixAt (payloadPort payloads) past

def replaceWire {args users : List PortTy} {past : List (List PortTy)} {t : PortTy}
    (value : Origin args past t) (wires : Wires args past users) (slot : Port users t) :
    Wires args past users :=
  match slot, wires with
  | .head, .cons _ rest => .cons value rest
  | .tail slot, .cons w rest => .cons w (replaceWire value rest slot)

/-- Extend the feedback column as each producer is bound. Only the column
changes here. Every operation reads the original header arguments. -/
def rowColumnAt {fields : Nat} {args ports : List PortTy}
    (slot : Fin fields → Port ports wordPort) (past : List (List PortTy)) :
    (updates : List (FeedbackUpdate fields)) →
    Wires args past ports → Wires args (extend past (rowSigs updates)) ports
  | [], wires => wires
  | u :: rest, wires =>
    rowColumnAt slot (past ++ [[wordPort]]) rest
      (replaceWire (newest .head) (wires.map (fun _ wire => weaken [wordPort] wire))
        (slot u.destination))

abbrev rowColumn {payloads : Nat} (past : List (List PortTy))
    (updates : List (FeedbackUpdate payloads)) (wires : Wires (headerArgs payloads) past (wordPorts payloads)) :=
  rowColumnAt (argumentPort payloads) past updates wires

def BankRoutes.feedbackWithRow {payloads : Nat} (r : BankRoutes payloads)
    (updates : List (FeedbackUpdate payloads)) :
    Wires (headerArgs payloads) (extend [] (headerRowSigs updates)) (wordPorts (payloads + 1)) :=
  .cons (keepOrigin (past := headerSigs) (sigs := rowSigs updates) (rowSuffix headerSigs updates) (.output (1 : Fin 4) .head))
    (rowColumn headerSigs updates (extendArguments _ r.feedback))

def BankRoutes.graphWithRow {payloads : Nat} (r : BankRoutes payloads)
    (updates : List (FeedbackUpdate payloads)) :
    Graph WordOp (wordSorts (payloads + 1)) (wordSorts (payloads + 1)) []
      (headerRowSigs updates) word where
  preheader := .nil
  header :=
    .cons (.const 1) .nil
      (.cons .sub (.cons (.arg (counterPort payloads)) (.cons (.output (0 : Fin 1) .head) .nil))
        (.cons (.const 0) .nil
          (.cons .ne (.cons (.arg (counterPort payloads)) (.cons (.output (2 : Fin 3) .head) .nil))
            (rowSuffix headerSigs updates))))
  phiInputs
    | .entry => .cons (.arg .head) r.entry
    | .backedge => r.feedbackWithRow updates
  predicate := keepOrigin (past := headerSigs) (sigs := rowSigs updates) (rowSuffix headerSigs updates) (.output (3 : Fin 4) .head)
  result := .arg (suffixPort (wordPorts (payloads + 1)) r.resultPort)

/-- Native word-bank graphs with an empty preheader and one word result.
The header table and the two incoming columns determine the machine code. -/
abbrev BankGraph (arity : Nat) (sigs : List (List PortTy)) :=
  Graph WordOp (wordSorts arity) (wordSorts arity) [] sigs word

def bankIncoming {arity : Nat} {sigs : List (List PortTy)} (g : BankGraph arity sigs) :
    Incoming → List Reg
  | .entry => emitColumn (arity := arity) (g.phiInputs .entry)
  | .backedge => emitColumn (arity := arity) (g.phiInputs .backedge)

def paramRegs (base arity : Nat) : List Reg := (List.range' base arity).map Reg.arg

def bankPreheader {arity : Nat} {sigs : List (List PortTy)} (g : BankGraph arity sigs) : Block Reg :=
  ⟨paramRegs 0 arity, [], .jump 1 (bankIncoming g .entry)⟩

def bankHeader {arity : Nat} {sigs : List (List PortTy)} (g : BankGraph arity sigs) : Block Reg :=
  ⟨paramRegs arity arity, emitOpsWith (fun p => .arg p.index) g.header,
    .cond (register g.predicate.address) 1 (bankIncoming g .backedge) 2 [register g.result.address]⟩

def exitBlock : Block Reg := ⟨[.phi], [], .ret [.phi]⟩

def lowerBankFunc {arity : Nat} {sigs : List (List PortTy)} (g : BankGraph arity sigs) : Func Reg :=
  ⟨⟨arity, 1⟩, 0, [bankPreheader g, bankHeader g, exitBlock]⟩

def lowerBank {arity : Nat} {sigs : List (List PortTy)} (g : BankGraph arity sigs) : Prog Reg :=
  ⟨[lowerBankFunc g]⟩

def BankRoutes.incomingWithRow {payloads : Nat} (r : BankRoutes payloads)
    (updates : List (FeedbackUpdate payloads)) := bankIncoming (r.graphWithRow updates)

def BankRoutes.preheaderWithRow {payloads : Nat} (r : BankRoutes payloads)
    (updates : List (FeedbackUpdate payloads)) := bankPreheader (r.graphWithRow updates)

def BankRoutes.headerWithRow {payloads : Nat} (r : BankRoutes payloads)
    (updates : List (FeedbackUpdate payloads)) := bankHeader (r.graphWithRow updates)

def BankRoutes.lowerFuncWithRow {payloads : Nat} (r : BankRoutes payloads)
    (updates : List (FeedbackUpdate payloads)) := lowerBankFunc (r.graphWithRow updates)

def BankRoutes.lowerWithRow {payloads : Nat} (r : BankRoutes payloads)
    (updates : List (FeedbackUpdate payloads)) : Prog Reg :=
  lowerBank (r.graphWithRow updates)

-- Keep the previous optional-update interface as wrappers of the row emitter.
abbrev extraSigs {payloads : Nat} (u : Option (FeedbackUpdate payloads)) := rowSigs u.toList
abbrev headerSigsWith {payloads : Nat} (u : Option (FeedbackUpdate payloads)) := headerRowSigs u.toList
abbrev headerSuffix {payloads : Nat} (u : Option (FeedbackUpdate payloads)) := rowSuffix headerSigs u.toList
abbrev BankRoutes.feedbackWith {payloads : Nat} (r : BankRoutes payloads)
    (u : Option (FeedbackUpdate payloads)) := r.feedbackWithRow u.toList
abbrev BankRoutes.graphWith {payloads : Nat} (r : BankRoutes payloads)
    (u : Option (FeedbackUpdate payloads)) := r.graphWithRow u.toList
abbrev BankRoutes.incomingWith {payloads : Nat} (r : BankRoutes payloads)
    (u : Option (FeedbackUpdate payloads)) := r.incomingWithRow u.toList
abbrev BankRoutes.preheaderWith {payloads : Nat} (r : BankRoutes payloads)
    (u : Option (FeedbackUpdate payloads)) := r.preheaderWithRow u.toList
abbrev BankRoutes.headerWith {payloads : Nat} (r : BankRoutes payloads)
    (u : Option (FeedbackUpdate payloads)) := r.headerWithRow u.toList
abbrev BankRoutes.lowerFuncWith {payloads : Nat} (r : BankRoutes payloads)
    (u : Option (FeedbackUpdate payloads)) := r.lowerFuncWithRow u.toList
abbrev BankRoutes.lowerWith {payloads : Nat} (r : BankRoutes payloads)
    (u : Option (FeedbackUpdate payloads)) := r.lowerWithRow u.toList

abbrev BankRoutes.graph {payloads : Nat} (r : BankRoutes payloads) := r.graphWithRow []
abbrev BankRoutes.incomingRegisters {payloads : Nat} (r : BankRoutes payloads) := r.incomingWithRow []
abbrev BankRoutes.preheader {payloads : Nat} (r : BankRoutes payloads) := r.preheaderWithRow []
abbrev BankRoutes.header {payloads : Nat} (r : BankRoutes payloads) := r.headerWithRow []
abbrev BankRoutes.lowerFunc {payloads : Nat} (r : BankRoutes payloads) := r.lowerFuncWithRow []
abbrev BankRoutes.lower {payloads : Nat} (r : BankRoutes payloads) := r.lowerWithRow []

/-- A zero-payload bank is rejected because it has no payload return port. -/
def lowerBankChecked (payloads : Nat) (entry feedback : List Nat) (result : Nat) : Option (Prog Reg) :=
  (checkBankRoutes payloads entry feedback result).bind fun routes =>
    if routes.lowerFunc.WellFormed then some routes.lower else none

/-- Typed inputs shared by the two lowerings of this countdown profile. -/
structure FeedbackPlan (payloads : Nat) where
  routes : BankRoutes payloads
  updates : List (FeedbackUpdate payloads)

def FeedbackPlan.rtl {payloads : Nat} (plan : FeedbackPlan payloads) : Prog Reg :=
  plan.routes.lowerWithRow plan.updates

/-- Decode the copy column and the distinct computed destinations, then
check the machine function. Both code generators can use this same plan. -/
def checkFeedbackPlan (payloads : Nat) (entry feedback : List Nat) (result : Nat)
    (specs : List FeedbackSpec) : Option (FeedbackPlan payloads) :=
  (checkFeedbackRow payloads specs).bind fun updates =>
    (checkBankRoutes payloads entry feedback result).bind fun routes =>
      if (routes.lowerFuncWithRow updates).WellFormed then some ⟨routes, updates⟩ else none

def lowerFeedbackRowChecked (payloads : Nat) (entry feedback : List Nat) (result : Nat)
    (specs : List FeedbackSpec) : Option (Prog Reg) :=
  (checkFeedbackPlan payloads entry feedback result specs).map FeedbackPlan.rtl

def lowerComputedChecked (payloads : Nat) (entry feedback : List Nat) (result : Nat)
    (spec : FeedbackSpec) : Option (Prog Reg) :=
  lowerFeedbackRowChecked payloads entry feedback result [spec]

def counter {payloads : Nat} (values : WordTuple (payloads + 1)) : Word := values.get .head

def bindWords (base : Nat) (fr : Frame Reg) : {arity : Nat} → WordTuple arity → Frame Reg
  | 0, .nil => fr
  | _ + 1, .cons w rest => bindWords (base + 1) (fr.set (.arg base) w) rest

def bindBank {payloads : Nat} (fr : Frame Reg) (values : WordTuple (payloads + 1)) : Frame Reg :=
  bindWords (payloads + 1) fr values

def testWord {payloads : Nat} (old : WordTuple (payloads + 1)) : Word := ofBool (counter old != 0)

def headerFrame {payloads : Nat} (fr : Frame Reg) (old : WordTuple (payloads + 1)) : Frame Reg :=
  (((fr.set (.node 0) 1).set (.node 1) (counter old - 1)).set (.node 2) 0).set (.node 3) (testWord old)

/-- The suffix writes fresh temporaries. Each right-hand side sees the
same old bank, even when it reads another update's destination slot. -/
def rowFrameAt {fields arity : Nat} (slot : Fin fields → Port (wordPorts arity) wordPort)
    (old : WordTuple arity) : Nat → Frame Reg → List (FeedbackUpdate fields) → Frame Reg
  | _, fr, [] => fr
  | pc, fr, u :: rest => rowFrameAt slot old (pc + 1) (fr.set (.node pc) (u.evalAt slot old)) rest

abbrev rowFrame {payloads : Nat} (old : WordTuple (payloads + 1)) :=
  rowFrameAt (payloadPort payloads) old

def headerFrameWithRow {payloads : Nat} (updates : List (FeedbackUpdate payloads))
    (fr : Frame Reg) (old : WordTuple (payloads + 1)) : Frame Reg :=
  rowFrame old 4 (headerFrame fr old) updates

abbrev headerFrameWith {payloads : Nat} (u : Option (FeedbackUpdate payloads)) :=
  @headerFrameWithRow payloads u.toList

def ArgsMatch {args : List PortTy} (fr : Frame Reg) (input : Tuple (Val model.value) args) : Prop :=
  ∀ p : Port args wordPort, fr.get (.arg p.index) = some (input.get p)

def BankRoutes.nextBankWithRow {payloads : Nat} (r : BankRoutes payloads)
    (updates : List (FeedbackUpdate payloads)) (input old : WordTuple (payloads + 1)) :
    WordTuple (payloads + 1) :=
  let args := appendTuple old input
  let graph := r.graphWithRow updates
  graph.latch model .backedge args (graph.header.eval model args PUnit.unit)

abbrev BankRoutes.nextBankWith {payloads : Nat} (r : BankRoutes payloads)
    (u : Option (FeedbackUpdate payloads)) := r.nextBankWithRow u.toList

abbrev BankRoutes.nextBank {payloads : Nat} (r : BankRoutes payloads) := r.nextBankWithRow []

def BankRoutes.returnWord {payloads : Nat} (r : BankRoutes payloads) (old : WordTuple (payloads + 1)) : Word :=
  old.get r.resultPort

/-! The three-payload interface selects the first payload at exit. -/

abbrev inputSorts := wordSorts 4
abbrev carriedSorts := wordSorts 4

structure Routes where
  entry : ArgumentColumn 4 3
  feedback : ArgumentColumn 8 3

def Routes.toBankRoutes (r : Routes) : BankRoutes 3 := ⟨r.entry, r.feedback, 0⟩

def checkRoutes (entry feedback : List Nat) : Option Routes :=
  (checkColumn 4 3 entry).bind fun initial =>
    (checkColumn 8 3 feedback).map fun next => ⟨initial, next⟩

abbrev Routes.graph (r : Routes) := r.toBankRoutes.graph
abbrev Routes.incomingRegisters (r : Routes) := r.toBankRoutes.incomingRegisters
abbrev entryParams := paramRegs 0 4
abbrev bankParams := paramRegs 4 4
abbrev Routes.preheader (r : Routes) := r.toBankRoutes.preheader
abbrev Routes.header (r : Routes) := r.toBankRoutes.header
abbrev Routes.lowerFunc (r : Routes) := r.toBankRoutes.lowerFunc
abbrev Routes.lower (r : Routes) := r.toBankRoutes.lower
abbrev Routes.nextBank (r : Routes) := r.toBankRoutes.nextBank

def lowerChecked (entry feedback : List Nat) : Option (Prog Reg) :=
  (checkRoutes entry feedback).bind fun routes =>
    if routes.lowerFunc.WellFormed then some routes.lower else none

def pack (counter first second third : Word) : WordTuple 4 :=
  .cons counter (.cons first (.cons second (.cons third .nil)))

def first (values : WordTuple 4) : Word := values.get (.tail .head)

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing
