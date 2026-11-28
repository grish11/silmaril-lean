module

public import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Defs
public import Silmaril.SSA.SeaOfNodes.Pure.RightIdentityPass.Defs

/-! Bounded replay of checked word-add replacements at the routed nomination. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Replay

open Diamond (Ty ValueSort dataPorts)
open GVN (Producer)
open GVN.Elimination (Rewrite)
open LeftSpine (SourceIds)
open RightSpine (WordWire)
open SubZero (word)
open RVSDG (extend)

variable {inputs : List (ValueSort Unit)} {out : ValueSort Unit}

inductive Stop where
  | noEdit
  | argument
  | refused (reason : Refusal)
  | unresolvedProducer
  | fuelExhausted
  deriving DecidableEq, Repr

structure Result (args : List (Ty Unit)) (sigs : List (List (Ty Unit))) where
  rewrite : Rewrite SubZero.Opcode args [] sigs
  rules : List Rule
  stop : Stop

/-- Find the actual word producer that owns the routed wire in the current table. -/
def findProducer? (program : Program SubZero.Opcode inputs out)
    (wire : WordWire (dataPorts inputs) (extend [] program.sigs)) : Option (Producer program.dataflow word) :=
  (RightIdentityPass.wordProducers program.dataflow).find? fun candidate =>
    decide (candidate.origin.address = wire.address)

def nominate (program : Program SubZero.Opcode inputs out)
    (wire : WordWire (dataPorts inputs) (extend [] program.sigs)) : Except Stop (Producer program.dataflow word) :=
  match wire with
  | .arg _ => .error .argument
  | .output _ _ =>
    match findProducer? program wire with
    | none => .error .unresolvedProducer
    | some candidate => .ok candidate

/-- A swap keeps producer identities and addresses. Other edits keep only
the argument part of the supplied source order. -/
def idsAfter (ids : SourceIds) : Rule → SourceIds
  | .nonAddLeftSwap | .offSpineSwap => ids
  | _ => ⟨fun address =>
    match address with
    | .arg _ => ids.lookup address
    | .output _ _ => none⟩

def unchanged (program : Program SubZero.Opcode inputs out) (stop : Stop) :
    Result (dataPorts inputs) program.sigs :=
  ⟨(GVN.Pass.unchanged program.dataflow).rewrite, [], stop⟩

/-- Spend one unit of fuel per accepted edit. Follow the nominated result
through its routing and compose the routing of each successful step. -/
def run : Nat → SourceIds → (program : Program SubZero.Opcode inputs out) →
    Producer program.dataflow word → Result (dataPorts inputs) program.sigs
  | 0, _, program, _ => unchanged program .fuelExhausted
  | fuel + 1, ids, program, candidate =>
    match AddIdealize.step ids program candidate with
    | .error reason => unchanged program (.refused reason)
    | .ok none => unchanged program .noEdit
    | .ok (some applied) =>
      let next := AddRewrite.rewrittenProgram program applied.rewrite
      match nominate next (applied.rewrite.route candidate.origin) with
      | .error stop => ⟨applied.rewrite, [applied.rule], stop⟩
      | .ok nomination =>
        let tail := run fuel (idsAfter ids applied.rule) next nomination
        ⟨GVN.Pass.compose applied.rewrite tail.rewrite, applied.rule :: tail.rules, tail.stop⟩

end Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Replay
