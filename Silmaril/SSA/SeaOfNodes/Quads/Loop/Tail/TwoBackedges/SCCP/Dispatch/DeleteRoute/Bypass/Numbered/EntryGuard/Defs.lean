module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Worklist.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Numbered.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Coverage.Defs

/-! Emit a typed numbered γ that guards the specialized θ fragment. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Tuple Port Origin Wires)
open RVSDG.NestedTheta (Graph Term)
open Join (Choice Opcode)
open Join.Finite (lastBank)
open Tail.Diamond (thenBase)

abbrev Tag : List (Diamond.Ty Width) := [.control 2]

def index (covered : Bool) : Fin 2 :=
  if covered then 1 else 0

variable {regs slots : List (ValueSort Width)} {past sigs : List (List (Diamond.Ty Width))}
variable {ins outs result : List (Diamond.Ty Width)}

abbrev Selector (regs : List (ValueSort Width)) :=
  Σ sigs, RVSDG.Term (Opcode Op) (dataPorts regs) [] sigs Tag

def bindOp (op : Opcode Op ins outs) (inputs : Wires (dataPorts regs) past ins)
    (rest : RVSDG.Term (Opcode Op) (dataPorts regs) (past ++ [outs]) sigs result) :
    RVSDG.Term (Opcode Op) (dataPorts regs) past (outs :: sigs) result :=
  .bind ⟨ins, .simple op, inputs, Fin.elim0⟩ (fun i => i.elim0) rest

def flag (covered : Bool) : RVSDG.Term (Opcode Op) (dataPorts regs) past [Tag] Tag :=
  bindOp (.route (regs := []) (.take (index covered))) .nil (.ret (lastBank past Tag))

/-- Pair the selector with the entry bank in its original slot order. -/
abbrev gammaNode (tag : Origin (dataPorts regs) past (.control 2))
    (childSigs : Fin 2 → List (List (Diamond.Ty Width))) : RVSDG.Node (Opcode Op) (dataPorts regs) past outs :=
  ⟨.control 2 :: dataPorts regs, .gamma 0, .cons tag (tabulate _ (fun port => .arg port)), childSigs⟩

def checkSigs (next : Selector regs) : Fin 2 → List (List (Diamond.Ty Width)) :=
  Fin.cases [Tag] (fun _ => next.1)

def checkArm (next : Selector regs) (i : Fin 2) :
    RVSDG.Term (Opcode Op) (dataPorts regs) [] (checkSigs next i) Tag :=
  Fin.cases (motive := fun i => RVSDG.Term (Opcode Op) (dataPorts regs) [] (checkSigs next i) Tag)
    (by exact flag false) (fun _ => by exact next.2) i

/-- A failed check returns the reject tag. Only a passing check evaluates
the remaining coverage graph, on the original bank in a fresh scope. -/
def andThen (tag : Origin (dataPorts regs) past (.control 2)) (next : Selector regs) :
    RVSDG.Term (Opcode Op) (dataPorts regs) past [Tag] Tag :=
  .bind (gammaNode tag (checkSigs next)) (fun i => checkArm next i) (.ret (lastBank past Tag))

abbrev PredicatePacket : List (Diamond.Ty Width) := [.control 2, .value .predicate]
abbrev WordPacket : List (Diamond.Ty Width) := [.control 2, .value .predicate, .value .predicate]

def predicateCheck (port : Port (dataPorts regs) (.value .predicate)) (expected : Bool)
    (next : Selector regs) : Selector regs :=
  ⟨[PredicatePacket, Tag],
    bindOp (.route (regs := [.predicate]) (.test .head (.take (index expected)) (.take (index !expected))))
      (.cons (.arg port) .nil) <|
    andThen ((lastBank [] PredicatePacket).get .head) next⟩

/-- Use the two existing unsigned comparisons. They both fail exactly when
the typed input word equals the expected word. -/
def wordCheck {width : Width} (port : Port (dataPorts regs) (.value (.data width)))
    (expected : Word width) (next : Selector regs) : Selector regs :=
  let word : List (Diamond.Ty Width) := [.value (.data width)]
  let pred : List (Diamond.Ty Width) := [.value .predicate]
  let compare : Choice [.predicate, .predicate] 2 :=
    .test .head (.take 0) (.test (.tail .head) (.take 0) (.take 1))
  ⟨[word, pred, pred, WordPacket, Tag],
    bindOp (.pure (.arithmetic (.constant expected))) .nil <|
    bindOp (.pure (.ult width)) (.cons (.arg port) (.cons ((lastBank [] word).get .head) .nil)) <|
    bindOp (.pure (.ult width)) (.cons (keep ((lastBank [] word).get .head)) (.cons (.arg port) .nil)) <|
    bindOp (.route compare) (.cons (keep ((lastBank [word] pred).get .head))
      (.cons ((lastBank [word, pred] pred).get .head) .nil)) <|
    andThen ((lastBank [word, pred, pred] WordPacket).get .head) next⟩

/-- Compile coverage over the pending slots while all checks read the
original bank. A constant slot inserts a short-circuit γ. -/
def checks :
    {slots : List (ValueSort Width)} → Tuple (Fact Word) (dataPorts slots) →
    (∀ {s}, Port (dataPorts slots) (.value s) → Port (dataPorts regs) (.value s)) →
    Selector regs
  | [], .nil, _ => ⟨[Tag], flag true⟩
  | slot :: _, .cons fact facts, source =>
    match fact with
    | .bottom => ⟨[Tag], flag false⟩
    | .overdefined => checks facts (fun port => source (.tail port))
    | .constant expected =>
      let next := checks facts (fun port => source (.tail port))
      match slot with
      | .predicate => predicateCheck (source .head) expected.down next
      | .data _ => wordCheck (source .head) expected next

def selector (facts : Tuple (Fact Word) (dataPorts regs)) : Selector regs :=
  checks facts (fun port => port)

/-- Link the existing numbered children using the emitted selector's wire.
Both children declare the same full original bank as input. -/
def choose (childSigs : Fin 2 → List (List (Diamond.Ty Width)))
    (children : ∀ i, Graph (Opcode Op) (dataPorts regs) [] (childSigs i) outs)
    (tag : Wires (dataPorts regs) past Tag) :
    Term (Opcode Op) (dataPorts regs) past [outs] outs :=
  .bind (.ofBase (gammaNode (tag.get .head) childSigs))
    (fun i => by exact (children (show Fin 2 from i)).toTerm) (.ret (lastBank past outs))

/-- Attach two numbered children without copying their producers into the
surrounding region. -/
def attach (test : Selector regs) (childSigs : Fin 2 → List (List (Diamond.Ty Width)))
    (children : ∀ i, Graph (Opcode Op) (dataPorts regs) [] (childSigs i) outs) :
    Graph (Opcode Op) (dataPorts regs) [] (test.1 ++ [outs]) outs :=
  (thenBase test.2 (choose childSigs children)).toGraph

variable {resultWidth : Width} {p : Program Op regs (.data resultWidth)}
variable [BankDecidableEq Word (dataPorts regs)]
variable {facts : Tuple (Fact Word) (dataPorts regs)}

abbrev Target (regs : List (ValueSort Width)) (result : Width) :=
  Σ sigs, Graph (Opcode Op) (dataPorts regs) [] sigs [.value (.data result)]

/-- Index 0 is the original graph, and index 1 is the specialized graph. -/
def arms (checked : Checked model p facts) : Fin 2 → Target regs resultWidth :=
  Fin.cases ⟨_, TwoBackedges.Numbered.lower p⟩ (fun _ => ⟨_, Bypass.Numbered.lower checked⟩)

def lower (checked : Checked model p facts) : Target regs resultWidth :=
  ⟨_, attach (selector facts) (fun i => (arms checked i).1) (fun i => (arms checked i).2)⟩

/-- The existing FIFO admits a singleton once. The emitted graph makes
the entry choice at execution time, for every input. -/
def compile (p : Program Op regs (.data resultWidth)) (facts : Tuple (Fact Word) (dataPorts regs)) :
    Except Refusal (Target regs resultWidth) :=
  (Backends.Worklist.admit model p facts).map lower

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard
