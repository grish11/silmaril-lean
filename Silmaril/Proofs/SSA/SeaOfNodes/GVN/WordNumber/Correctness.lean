module

public import Silmaril.SSA.SeaOfNodes.GVN.WordNumber.Defs
import Silmaril.SSA.SeaOfNodes.GVN.Elimination.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Equality.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.WordNumber

open Silmaril.SSA.SeaOfNodes.Diamond
open Silmaril.SSA.SeaOfNodes.GVN.WordNumber
open Silmaril.SSA.SeaOfNodes.GVN.Elimination (read_splitOrigin splitOrigin)
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (Opcode model word wordPort)
open Silmaril.SSA.RVSDG (Address Locals Origin Port Tuple Wires)

variable {args : List (Ty Unit)} {past sigs : List (List (Ty Unit))}

private theorem same_port (lhs rhs : Port args wordPort) (same : lhs.index = rhs.index) : lhs = rhs := by
  have h := Silmaril.SSA.RVSDG.NestedTheta.Equality.addresses_injective
    (.cons (Origin.arg (past := []) lhs) .nil) (.cons (.arg rhs) .nil)
    (congrArg (fun index => [Address.arg index]) same)
  exact Origin.arg.inj (congrArg (fun (wires : Wires args [] [wordPort]) => wires.get .head) h)

theorem matches_eq {lhs other : Key args} (matched : lhs.matches other = true) : lhs = other := by
  induction lhs generalizing other with
  | argument lhs =>
    cases other with
    | argument rhs => exact congrArg Key.argument (same_port lhs rhs (of_decide_eq_true matched))
    | literal _ | binary _ _ _ => cases matched
  | literal lhs =>
    cases other with
    | literal rhs => exact congrArg Key.literal (of_decide_eq_true matched)
    | argument _ | binary _ _ _ => cases matched
  | binary op lhs rhs ihL ihR =>
    cases other with
    | binary otherOp otherLhs otherRhs =>
      simp only [Key.matches, Bool.and_eq_true] at matched
      rw [of_decide_eq_true matched.1.1, ihL matched.1.2, ihR matched.2]
    | argument _ | literal _ => cases matched

private theorem run_agrees {entry : Tuple (Val model.value) args}
    {keys : Tuple (Val (numbering args).value) args}
    {locals : Locals (Val model.value) past} {numbered : Locals (Val (numbering args).value) past}
    (agrees : ∀ wire : Origin args past wordPort,
      (read (numbering args) wire keys numbered).eval entry = read model wire entry locals)
    {ins : List (ValueSort Unit)} (op : Opcode ins word) (wires : Wires args past (dataPorts ins)) :
    ((numbering args).run op (wires.read keys numbered)).eval entry = model.run op (wires.read entry locals) := by
  cases op with
  | literal value => cases wires; rfl
  | add | sub | mul =>
    cases wires with
    | cons lhs tail =>
      cases tail with
      | cons rhs tail =>
        cases tail
        first
        | exact congrArg₂ BitVec.add (agrees lhs) (agrees rhs)
        | exact congrArg₂ BitVec.sub (agrees lhs) (agrees rhs)
        | exact congrArg₂ BitVec.mul (agrees lhs) (agrees rhs)

private theorem snoc_agrees {entry : Tuple (Val model.value) args}
    {keys : Tuple (Val (numbering args).value) args}
    {locals : Locals (Val model.value) past} {numbered : Locals (Val (numbering args).value) past}
    (agrees : ∀ wire : Origin args past wordPort,
      (read (numbering args) wire keys numbered).eval entry = read model wire entry locals)
    {key : Key args} {value : BitVec 64} (next : key.eval entry = value)
    (wire : Origin args (past ++ [[wordPort]]) wordPort) :
    (read (numbering args) wire keys (numbered.snoc (.cons key .nil))).eval entry =
      read model wire entry (locals.snoc (.cons value .nil)) := by
  rw [← read_splitOrigin wire (numbering args), ← read_splitOrigin wire model]
  cases splitOrigin [wordPort] wire with
  | inl prior => exact agrees prior
  | inr port =>
    cases port with
    | head => exact next
    | tail impossible => cases impossible

theorem eval_agrees (flow : Dataflow Opcode args past sigs)
    {entry : Tuple (Val model.value) args} {keys : Tuple (Val (numbering args).value) args}
    {locals : Locals (Val model.value) past} {numbered : Locals (Val (numbering args).value) past}
    (agrees : ∀ wire : Origin args past wordPort,
      (read (numbering args) wire keys numbered).eval entry = read model wire entry locals) :
    ∀ wire : Origin args (Silmaril.SSA.RVSDG.extend past sigs) wordPort,
      (read (numbering args) wire keys (flow.eval (numbering args) keys numbered)).eval entry =
        read model wire entry (flow.eval model entry locals) := by
  induction flow with
  | nil => exact agrees
  | cons op wires rest ih =>
    cases op <;> exact ih (snoc_agrees agrees (run_agrees agrees _ wires))

private theorem keyArguments_get (inputs : List (ValueSort Unit)) :
    ∀ (lift : ∀ {sort}, Port (dataPorts inputs) (.value sort) → Port args (.value sort))
      (port : Port (dataPorts inputs) wordPort),
      (keyArguments args inputs lift).get port = Key.argument (lift port) := by
  induction inputs with
  | nil => intro _ port; cases port
  | cons sort tail ih =>
    intro lift port
    cases sort with
    | predicate =>
      cases port with
      | tail inner => exact ih (fun q => lift (.tail q)) inner
    | data singleton =>
      cases singleton
      cases port with
      | head => rfl
      | tail inner => exact ih (fun q => lift (.tail q)) inner

theorem entry_read_agrees {inputs : List (ValueSort Unit)} (entry : Tuple (Val model.value) (dataPorts inputs))
    (wire : Origin (dataPorts inputs) [] wordPort) :
    (read (numbering (dataPorts inputs)) wire (entryKeys inputs) PUnit.unit).eval entry =
      read model wire entry PUnit.unit := by
  cases wire with
  | output index _ => exact index.elim0
  | arg port =>
    change ((entryKeys inputs).get port).eval entry = entry.get port
    rw [entryKeys, keyArguments_get]
    rfl

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.WordNumber
