module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked.Phi.Defs

/-! # A guarded feedback row over an arbitrary i64 bank -/

@[expose] public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows

open Silmaril.Machine.Lir (Memory Word ofBool)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA (State)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg WordOp model)
open Silmaril.SSA.RVSDG (Address Origin Port Wires extend)
open Silmaril.SSA.SeaOfNodes.Diamond (Dataflow)
open Silmaril.SSA.SeaOfNodes.GVN (keepOrigin newest)
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA

/-- The right operand is a literal, an old bank field, or a row result. -/
inductive GuardOperand (arity producers : Nat) where
  | limit
  | bank (slot : Fin arity)
  | computed (producer : Fin producers)

structure Plan (arity : Nat) where
  entry : ArgumentColumn arity arity
  copies : ArgumentColumn arity arity
  updates : List (FeedbackUpdate arity)
  guardIndex : Fin updates.length
  comparison : Guard
  limit : Word
  exitSlot : Fin arity
  exitProducer : Option (Fin updates.length) := none
  guardOperand : GuardOperand arity updates.length := .limit

/-- Copies read old bank slots. The guard names a producer and its
destination. Exit reads the old slot by default or a producer checked
against that slot's destination. -/
structure Spec where
  entry : List Nat
  copies : List Nat
  updates : List FeedbackSpec
  guardOrigin : Address
  guardDestination : Nat
  comparison : Guard
  limit : Word
  exitSlot : Nat
  exitOrigin : Option Address := none
  /-- A bank-local argument or a distinct row producer's word output.
  Absence selects the fixed limit. -/
  guardRhs : Option Address := none

/-- Decode the single word result port of a typed update. -/
def checkResultPort {arity : Nat} (updates : List (FeedbackUpdate arity))
    (origin : Address) : Option (Fin updates.length) := do
  let .output index 0 := origin | none
  if inside : index < updates.length then some ⟨index, inside⟩ else none

/-- Decode the result port and check its declared bank destination. -/
def checkProducer {arity : Nat} (updates : List (FeedbackUpdate arity))
    (origin : Address) (destination : Nat) : Option (Fin updates.length) := do
  let index ← checkResultPort updates origin
  if updates[index].destination.val = destination then some index else none

/-- Decode an old bank operand in bank-local numbering. -/
def checkBankOperand (arity : Nat) (origin : Address) : Option (Fin arity) := do
  let .arg slot := origin | none
  if inside : slot < arity then some ⟨slot, inside⟩ else none

def checkGuardOperand {arity : Nat} (updates : List (FeedbackUpdate arity))
    (left : Fin updates.length) : Option Address → Option (GuardOperand arity updates.length)
  | none => some .limit
  | some (.arg slot) => (checkBankOperand arity (.arg slot)).map .bank
  | some (.output index port) => do
    let producer ← checkResultPort updates (.output index port)
    if producer = left then none else some (.computed producer)

def checkPlan (arity : Nat) (spec : Spec) : Option (Plan arity) := do
  let entry ← checkColumn arity arity spec.entry
  let copies ← checkColumn arity arity spec.copies
  let updates ← checkFeedbackRow arity spec.updates
  let guardIndex ← checkProducer updates spec.guardOrigin spec.guardDestination
  let guardOperand ← checkGuardOperand updates guardIndex spec.guardRhs
  if exit : spec.exitSlot < arity then
    let exitProducer ← spec.exitOrigin.mapM fun origin => checkProducer updates origin spec.exitSlot
    some ⟨entry, copies, updates, guardIndex, spec.comparison, spec.limit, ⟨spec.exitSlot, exit⟩, exitProducer, guardOperand⟩
  else none

theorem extend_append (past sigs tail : List (List PortTy)) :
    extend past (sigs ++ tail) = extend (extend past sigs) tail := by
  induction sigs generalizing past with
  | nil => rfl
  | cons _ _ ih => exact ih _

def appendFlow {args : List PortTy} {tail : List (List PortTy)} :
    {past sigs : List (List PortTy)} → Dataflow WordOp args past sigs →
    Dataflow WordOp args (extend past sigs) tail → Dataflow WordOp args past (sigs ++ tail)
  | _, _, .nil, rest => rest
  | _, _, .cons op wires next, rest => .cons op wires (appendFlow next rest)

def joinedOrigin {args : List PortTy} {past sigs tail : List (List PortTy)} {t : PortTy}
    (wire : Origin args (extend (extend past sigs) tail) t) :
    Origin args (extend past (sigs ++ tail)) t :=
  (extend_append past sigs tail).symm ▸ wire

theorem extend_rowSigs {fields : Nat} (updates : List (FeedbackUpdate fields)) (past : List (List PortTy)) :
    extend past (rowSigs updates) = past ++ List.replicate updates.length [wordPort] := by
  induction updates generalizing past with
  | nil => simp [rowSigs, extend]
  | cons _ rest ih =>
    rw [rowSigs, extend, ih, List.length_cons, List.replicate_succ, List.append_assoc]
    rfl

def guardSetupSigs {arity producers : Nat} : GuardOperand arity producers → List (List PortTy)
  | .limit => [[wordPort]]
  | .bank _ | .computed _ => []

def guardSetup {arity producers : Nat} {past : List (List PortTy)} (limit : Word) :
    (operand : GuardOperand arity producers) → Dataflow WordOp (bankArgs arity) past (guardSetupSigs operand)
  | .limit => .cons (.const limit) .nil .nil
  | .bank _ | .computed _ => .nil

def guardRhsWire {arity producers : Nat} {past : List (List PortTy)}
    (result : Fin producers → Origin (bankArgs arity) past wordPort) :
    (operand : GuardOperand arity producers) → Origin (bankArgs arity) (extend past (guardSetupSigs operand)) wordPort
  | .limit => newest .head
  | .bank slot => .arg (suffixPort (wordPorts arity) (argumentPort arity slot))
  | .computed producer => result producer

def GuardOperand.eval {arity : Nat} (updates : List (FeedbackUpdate arity))
    (limit : Word) (old : WordTuple arity) : GuardOperand arity updates.length → Word
  | .limit => limit
  | .bank slot => old.get (argumentPort arity slot)
  | .computed producer => updates[producer].evalAt (argumentPort arity) old

variable {arity : Nat} (p : Plan arity)

abbrev Plan.rowPast := extend [] (rowSigs p.updates)

abbrev Plan.comparePast := extend p.rowPast (guardSetupSigs p.guardOperand)
abbrev Plan.guardSigs := guardSetupSigs p.guardOperand ++ [[.value .predicate]]
abbrev Plan.sigs := rowSigs p.updates ++ p.guardSigs

def Plan.row : Dataflow WordOp (bankArgs arity) [] (rowSigs p.updates) :=
  rowSuffixAt (argumentPort arity) [] p.updates

def Plan.producerWire (producer : Fin p.updates.length) : Origin (bankArgs arity) p.rowPast wordPort :=
  let index : Fin p.rowPast.length := ⟨producer.val, by simp [extend_rowSigs]⟩
  .output index (by
    have mem : p.rowPast[index] ∈ p.rowPast := List.getElem_mem _
    have replicated : p.rowPast[index] ∈ List.replicate p.updates.length [wordPort] := by
      simpa only [extend_rowSigs, List.nil_append] using mem
    exact (List.eq_of_mem_replicate replicated).symm ▸ Port.head)

def Plan.guardWire : Origin (bankArgs arity) p.rowPast wordPort :=
  p.producerWire p.guardIndex

/-- The exit reads either an old bank slot or a result of this activation. -/
def Plan.exitWire : Origin (bankArgs arity) p.rowPast wordPort :=
  p.exitProducer.elim (.arg (suffixPort (wordPorts arity) (argumentPort arity p.exitSlot))) p.producerWire

def Plan.guardSetup : Dataflow WordOp (bankArgs arity) p.rowPast (guardSetupSigs p.guardOperand) :=
  Rows.guardSetup p.limit p.guardOperand

abbrev Plan.guardRhsWire : Origin (bankArgs arity) p.comparePast wordPort :=
  Rows.guardRhsWire p.producerWire p.guardOperand

def Plan.guardOperands : Wires (bankArgs arity) p.comparePast [wordPort, wordPort] :=
  .cons (keepOrigin p.guardSetup p.guardWire) (.cons p.guardRhsWire .nil)

def Plan.test : Dataflow WordOp (bankArgs arity) p.rowPast p.guardSigs :=
  appendFlow p.guardSetup (.cons p.comparison.source p.guardOperands .nil)

def Plan.testPredicate : Origin (bankArgs arity) (extend p.rowPast p.guardSigs) (.value .predicate) :=
  joinedOrigin (past := p.rowPast) (sigs := guardSetupSigs p.guardOperand)
    (tail := [[.value .predicate]]) (newest .head)

def Plan.feedbackColumn : Wires (bankArgs arity) p.rowPast (wordPorts arity) :=
  rowColumnAt (argumentPort arity) [] p.updates (p.copies.map fun _ wire =>
    match wire with
    | .arg slot => .arg (suffixPort (wordPorts arity) slot)
    | .output i _ => i.elim0)

def Plan.graph : BankGraph arity p.sigs where
  preheader := .nil
  header := appendFlow p.row p.test
  phiInputs
    | .entry => p.entry
    | .backedge => p.feedbackColumn.map fun _ wire =>
      joinedOrigin (past := []) (sigs := rowSigs p.updates) (tail := p.guardSigs) (keepOrigin p.test wire)
  predicate := joinedOrigin (past := []) (sigs := rowSigs p.updates) (tail := p.guardSigs) p.testPredicate
  result := joinedOrigin (past := []) (sigs := rowSigs p.updates) (tail := p.guardSigs) (keepOrigin p.test p.exitWire)

def Plan.guardValue (old : WordTuple arity) : Word :=
  p.updates[p.guardIndex].evalAt (argumentPort arity) old

def Plan.guardRhsValue (old : WordTuple arity) : Word :=
  GuardOperand.eval p.updates p.limit old p.guardOperand

def Plan.guardWord (old : WordTuple arity) : Word :=
  ofBool (p.comparison.target.eval (p.guardValue old) (p.guardRhsValue old))

def Plan.exitValue (old : WordTuple arity) : Word :=
  match p.exitProducer with
  | none => old.get (argumentPort arity p.exitSlot)
  | some index => p.updates[index].evalAt (argumentPort arity) old

def Plan.nextBank (input old : WordTuple arity) : WordTuple arity :=
  let args := appendTuple old input
  p.feedbackColumn.read args (p.row.eval model args PUnit.unit)

def Plan.rowFrame (fr : Frame Reg) (old : WordTuple arity) : Frame Reg :=
  rowFrameAt (argumentPort arity) old 0 fr p.updates

def Plan.guardSetupFrame (fr : Frame Reg) : Frame Reg :=
  match p.guardOperand with
  | .limit => fr.set (.node p.updates.length) p.limit
  | .bank _ | .computed _ => fr

def Plan.compareIndex : Nat := p.updates.length + (guardSetupSigs p.guardOperand).length

def Plan.testFrame (fr : Frame Reg) (old : WordTuple arity) : Frame Reg :=
  (p.guardSetupFrame (p.rowFrame fr old)).set (.node p.compareIndex) (p.guardWord old)

def Plan.successor (input old : WordTuple arity) (fr : Frame Reg) (mem : Memory) : State Reg :=
  let after := p.testFrame fr old
  if p.guardWord old = 0 then
    ⟨⟨0, 2, 0⟩, after.set .phi (p.exitValue old), [], mem⟩
  else
    ⟨⟨0, 1, 0⟩, bindWords arity after (p.nextBank input old), [], mem⟩

/-- One activation executes the row, the optional literal, the comparison,
and the conditional terminator. -/
def Plan.activationSteps : Nat := p.compareIndex + 2

/-- Machine fuel for at most this many backedges, including the entry jump,
the terminating header activation, and the return step. -/
def Plan.rtlFuel (backedges : Nat) : Nat :=
  p.activationSteps * (backedges + 1) + 2

def lowerChecked (arity : Nat) (spec : Spec) : Option Checked.Phi.Targets :=
  (checkPlan arity spec).bind fun p =>
    if (lowerBankFunc p.graph).WellFormed then some (lowerBank p.graph, Generic.lower p.graph) else none

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
