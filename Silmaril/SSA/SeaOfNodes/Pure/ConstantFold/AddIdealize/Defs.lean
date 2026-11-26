module

public import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddChain.Defs
public import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Doubling.Defs
public import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.LeftSpine.Defs

/-! Select one checked Simple word-add rewrite in source precedence order. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize

open Diamond (Dataflow Ty Val ValueSort dataPorts)
open GVN (Producer)
open GVN.Elimination (Rewrite dropNewest routeSuffix)
open LeftSpine (SourceIds)
open RightSpine (Addends WordWire)
open SubZero (model word wordPort)
open RVSDG (Locals Tuple Wires)

variable {args : List (Ty Unit)} {past sigs : List (List (Ty Unit))}
variable {ins inputs : List (ValueSort Unit)} {out : ValueSort Unit}

inductive Rule where
  | literal | rightZero | doubling | rightSpine | constantChain | leftSpine
  deriving DecidableEq, Repr

inductive Refusal where
  | notAddition
  | nonAddLeftSwap
  | offSpineSwap
  | missingSourceIds
  | outsideRuleProfile (rule : Rule)
  deriving DecidableEq, Repr

/-- An error is an explicit refusal. A successful `none` is a source branch with no edit. -/
abbrev Outcome (α : Type) := Except Refusal (Option α)

structure Facts (args : List (Ty Unit)) (past : List (List (Ty Unit))) where
  analyzed : RightSpine.Prefix args past
  explicit : AddChain.Prefix args past

def Facts.empty : Facts args [] := ⟨RightSpine.Prefix.empty, AddChain.Prefix.empty⟩

def Facts.record (facts : Facts args past) (op : SubZero.Opcode ins out)
    (operands : Wires args past (dataPorts ins)) : Facts args (past ++ [[.value out]]) :=
  ⟨facts.analyzed.record op operands, facts.explicit.record op operands⟩

inductive Edit (args : List (Ty Unit)) (past : List (List (Ty Unit))) where
  | replaceLiteral (literal : SubZero.Opcode [] word)
  | redirect (wire : WordWire args past)
  | splice (edit : AddRewrite.Splice args past)

def Edit.eval (edit : Edit args past) (entry : Tuple (Val model.value) args)
    (locals : Locals (Val model.value) past) : BitVec 64 :=
  match edit with
  | .replaceLiteral value => model.run value .nil
  | .redirect wire => Diamond.read model wire entry locals
  | .splice edit => edit.eval entry locals

def Edit.apply (edit : Edit args past) (rest : Dataflow SubZero.Opcode args (past ++ [[wordPort]]) sigs) :
    Rewrite SubZero.Opcode args past ([wordPort] :: sigs) :=
  match edit with
  | .replaceLiteral value => ⟨_, .cons value .nil rest, fun wire => wire⟩
  | .redirect wire =>
    let suffix := routeSuffix rest (dropNewest wire)
    ⟨_, suffix.1, suffix.2⟩
  | .splice edit => AddRewrite.insertSplice edit rest

def isZero (known : Literals args past) (rhs : WordWire args past) : Bool :=
  let value : Option (BitVec 64) := known rhs
  decide (value = some 0)

/-- Once the source branch has been selected, a narrower matcher can
refuse the edit. The decision stays at that branch. -/
def checkedSplice (rule : Rule) (candidate : Option (AddRewrite.Splice args past)) :
    Outcome (Rule × Edit args past) :=
  match candidate with
  | none => .error (.outsideRuleProfile rule)
  | some edit => .ok (some (rule, .splice edit))

def leftBranch (ids : SourceIds) (facts : Facts args past) (lhs rhs : WordWire args past)
    (left : Addends args past) : Outcome (Rule × Edit args past) :=
  if (facts.analyzed.literals left.right).isSome && (facts.analyzed.literals rhs).isSome then
    checkedSplice .constantChain (AddChain.rules.matchAdd? facts.explicit lhs rhs)
  else
    match LeftSpine.compare? ids facts.analyzed.literals left.right rhs with
    | none => .error .missingSourceIds
    | some false => .ok none
    | some true => checkedSplice .leftSpine (LeftSpine.matchAdd? ids facts.analyzed lhs rhs)

/-- Dispatch at the actual ordered add operands with the prefix facts.
This follows the source order in the acyclic, non-Φ profile. -/
def select (ids : SourceIds) (facts : Facts args past) (lhs rhs : WordWire args past) :
    Outcome (Rule × Edit args past) :=
  match binaryLiteral? facts.analyzed.literals .add (.cons lhs (.cons rhs .nil)) with
  | some literal => .ok (some (.literal, .replaceLiteral literal))
  | none =>
    if isZero facts.analyzed.literals rhs then
      if isZero facts.explicit.literals rhs then .ok (some (.rightZero, .redirect lhs))
      else .error (.outsideRuleProfile .rightZero)
    else if lhs.address = rhs.address then
      checkedSplice .doubling (Doubling.rules.matchAdd? facts.analyzed.literals lhs rhs)
    else
      match facts.analyzed.addends lhs, facts.analyzed.addends rhs with
      | none, some _ => .error .nonAddLeftSwap
      | some _, some _ => checkedSplice .rightSpine (RightSpine.matchAdd? facts.analyzed lhs rhs)
      | some left, none => leftBranch ids facts lhs rhs left
      | none, none =>
        match LeftSpine.compare? ids facts.analyzed.literals lhs rhs with
        | none => .error .missingSourceIds
        | some true => .error .offSpineSwap
        | some false => .ok none

structure Applied (args : List (Ty Unit)) (past sigs : List (List (Ty Unit))) where
  rule : Rule
  rewrite : Rewrite SubZero.Opcode args past sigs

def atProducer (ids : SourceIds) : {past sigs : List (List (Ty Unit))} →
    {flow : Dataflow SubZero.Opcode args past sigs} → {sort : ValueSort Unit} →
    Facts args past → Producer flow sort → Outcome (Applied args past sigs)
  | _, _, _, _, facts, .here (op := .add) (inputs := .cons lhs (.cons rhs .nil)) (rest := rest) =>
    (select ids facts lhs rhs).map (Option.map fun (rule, edit) => ⟨rule, edit.apply rest⟩)
  | _, _, _, _, _, .here => .error .notAddition
  | _, _, _, _, facts, .later (op := op) (inputs := operands) candidate =>
    (atProducer ids (facts.record op operands) candidate).map (Option.map fun applied =>
      ⟨applied.rule, ⟨_, .cons op operands applied.rewrite.flow, applied.rewrite.route⟩⟩)

/-- Apply the source-ordered decision to one nominated producer. Earlier
bindings are analyzed to supply facts for that decision. -/
def step (ids : SourceIds) (program : Program SubZero.Opcode inputs out)
    (candidate : Producer program.dataflow word) : Outcome (Applied (dataPorts inputs) [] program.sigs) :=
  atProducer ids Facts.empty candidate

end Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize
