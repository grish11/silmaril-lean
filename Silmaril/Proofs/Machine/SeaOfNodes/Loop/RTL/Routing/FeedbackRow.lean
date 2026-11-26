module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Defs
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Frame
import Silmaril.SSA.SeaOfNodes.GVN.Elimination.Thms

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Proofs

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA (Block Op Prog State Steps Transition)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg WordOp emitOpsWith model)
open Silmaril.SSA.SeaOfNodes.Diamond (Dataflow Val read)
open Silmaril.SSA.SeaOfNodes.GVN (keepOrigin olderIndex weaken)
open Silmaril.SSA.SeaOfNodes.GVN.Elimination (splitOrigin splitOutput read_splitOrigin)
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)
open Silmaril.SSA.RVSDG (Locals Origin Port Tuple extend)

variable {payloads : Nat}

theorem rowFrameAt_get {fields arity : Nat} (slot : Fin fields → Port (wordPorts arity) wordPort)
    (old : WordTuple arity) (updates : List (FeedbackUpdate fields))
    (pc : Nat) (fr : Frame Reg) (reg : Reg) (untouched : ∀ j, pc ≤ j → reg ≠ .node j) :
    (rowFrameAt slot old pc fr updates).get reg = fr.get reg := by
  induction updates generalizing pc fr with
  | nil => rfl
  | cons u rest ih =>
    rw [rowFrameAt, ih (pc + 1) _ (fun j ge => untouched j (by omega))]
    simp only [Frame.get_set, ite_eq_right (untouched pc (Nat.le_refl pc))]

theorem rowFrameAt_read {fields arity : Nat} (slot : Fin fields → Port (wordPorts arity) wordPort)
    (old : WordTuple arity) (updates : List (FeedbackUpdate fields)) (pc : Nat) (fr : Frame Reg)
    (index : Fin updates.length) :
    (rowFrameAt slot old pc fr updates).get (.node (pc + index.val)) =
      some (updates[index].evalAt slot old) := by
  induction updates generalizing pc fr with
  | nil => exact index.elim0
  | cons u rest ih =>
    refine Fin.cases ?_ (fun j => ?_) index
    · change (rowFrameAt slot old (pc + 1) (fr.set (.node pc) (u.evalAt slot old)) rest).get (.node pc) =
        some (u.evalAt slot old)
      rw [rowFrameAt_get _ _ _ _ _ _ (by intro k ge same; have := Reg.node.inj same; omega)]
      simp
    · change (rowFrameAt slot old (pc + 1) (fr.set (.node pc) (u.evalAt slot old)) rest).get
        (.node (pc + (j.val + 1))) = some (rest[j].evalAt slot old)
      rw [show pc + (j.val + 1) = pc + 1 + j.val by omega]
      exact ih _ _ j

theorem rowFrame_get (old : WordTuple (payloads + 1)) (updates : List (FeedbackUpdate payloads))
    (pc : Nat) (fr : Frame Reg) (reg : Reg) (untouched : ∀ j, pc ≤ j → reg ≠ .node j) :
    (rowFrame old pc fr updates).get reg = fr.get reg :=
  rowFrameAt_get (payloadPort payloads) old updates pc fr reg untouched

private theorem olderIndex_val (head : List PortTy) (past : List (List PortTy))
    (i : Fin past.length) : (olderIndex head past i).val = i.val := by
  induction past with
  | nil => exact i.elim0
  | cons _ rest ih => exact Fin.cases rfl (fun j => congrArg Nat.succ (ih j)) i

theorem keep_register {args : List PortTy} {past sigs : List (List PortTy)} {t : PortTy}
    (flow : Dataflow WordOp args past sigs) (wire : Origin args past t) :
    register (keepOrigin flow wire).address = register wire.address := by
  induction flow with
  | nil => rfl
  | cons op operands rest ih =>
    change register (keepOrigin rest (weaken _ wire)).address = _
    rw [ih]
    cases wire with
    | arg => rfl
    | output i port => exact congrArg Reg.node (olderIndex_val _ _ i)

theorem keep_row_register {past : List (List PortTy)} {t : PortTy}
    (updates : List (FeedbackUpdate payloads)) (wire : Origin (headerArgs payloads) past t) :
    register (keepOrigin (rowSuffix past updates) wire).address = register wire.address :=
  keep_register (rowSuffix past updates) wire

private theorem split_index {head : List PortTy} {t : PortTy} (past : List (List PortTy))
    (i : Fin (past ++ [head]).length) (p : Port (past ++ [head])[i] t) :
    i.val = match splitOutput head past i p with
      | .inl ⟨j, _⟩ => j.val
      | .inr _ => past.length := by
  induction past with
  | nil =>
    revert p
    exact Fin.cases (fun _ => rfl) (fun j => j.elim0) i
  | cons h tail ih =>
    revert p
    refine Fin.cases (fun _ => rfl) (fun j p => ?_) i
    have same := ih j p
    simp only [splitOutput, Fin.cases_succ]
    cases split : splitOutput head tail j p with
    | inl prior =>
      rcases prior with ⟨k, q⟩
      rw [split] at same
      exact congrArg Nat.succ same
    | inr q =>
      rw [split] at same
      exact congrArg Nat.succ same

private theorem split_register {args : List PortTy} {past : List (List PortTy)} {t : PortTy}
    (wire : Origin args (past ++ [[wordPort]]) t) :
    register wire.address = match splitOrigin [wordPort] wire with
      | .inl prior => register prior.address
      | .inr _ => .node past.length := by
  cases wire with
  | arg => rfl
  | output i p =>
    have same := split_index past i p
    simp only [splitOrigin]
    cases split : splitOutput [wordPort] past i p with
    | inl prior =>
      rcases prior with ⟨j, q⟩
      rw [split] at same
      exact congrArg Reg.node same
    | inr q =>
      rw [split] at same
      exact congrArg Reg.node same

private theorem prior_register_ne {args : List PortTy} {past : List (List PortTy)} {t : PortTy}
    (wire : Origin args past t) : register wire.address ≠ .node past.length := by
  cases wire with
  | arg => simp [Origin.address, register]
  | output i p => exact fun same => (Nat.ne_of_lt i.isLt) (Reg.node.inj same)

private theorem old_read {arity : Nat} (input old : WordTuple arity)
    (port : Port (wordPorts arity) wordPort) :
    (appendTuple old input).get (suffixPort (wordPorts arity) port) = old.get port :=
  suffix_get input old _

private theorem operation_reads {fields arity : Nat} (slot : Fin fields → Port (wordPorts arity) wordPort)
    (u : FeedbackUpdate fields) (input old : WordTuple arity)
    (past : List (List PortTy)) (locals : Locals (Val model.value) past) :
    model.run u.operation.source ((u.operandsAt slot past).read (appendTuple old input) locals) =
      u.evalAt slot old := by
  change model.run u.operation.source
    (.cons ((appendTuple old input).get (suffixPort (wordPorts arity) (slot u.left)))
      (.cons ((appendTuple old input).get (suffixPort (wordPorts arity) (slot u.right))) .nil)) = _
  rw [old_read, old_read]
  rcases u with ⟨op, _, _, _⟩
  cases op <;> rfl

private theorem binding_reads {args : List PortTy} {past : List (List PortTy)}
    (input : Tuple (Val model.value) args) (locals : Locals (Val model.value) past)
    (fr : Frame Reg) (value : Word)
    (agree : ∀ wire : Origin args past wordPort,
      fr.get (register wire.address) = some (read model wire input locals))
    (wire : Origin args (past ++ [[wordPort]]) wordPort) :
    (fr.set (.node past.length) value).get (register wire.address) =
      some (read model wire input (locals.snoc (.cons value .nil))) := by
  have machine := split_register wire
  have native := read_splitOrigin wire model input locals (.cons value .nil)
  cases split : splitOrigin [wordPort] wire with
  | inl prior =>
    rw [split] at machine native
    rw [machine, ← native, Frame.get_set, ite_eq_right (prior_register_ne prior)]
    exact agree prior
  | inr port =>
    rw [split] at machine native
    rw [machine, ← native]
    cases port with
    | head =>
      change (fr.set (.node past.length) value).get (.node past.length) = some value
      simp
    | tail port => exact nomatch port

theorem row_reads_at {fields arity : Nat} (slot : Fin fields → Port (wordPorts arity) wordPort)
    (updates : List (FeedbackUpdate fields)) (past : List (List PortTy))
    (input old : WordTuple arity) (fr : Frame Reg) (locals : Locals (Val model.value) past)
    (agree : ∀ wire : Origin (bankArgs arity) past wordPort,
      fr.get (register wire.address) = some (read model wire (appendTuple old input) locals))
    (wire : Origin (bankArgs arity) (extend past (rowSigs updates)) wordPort) :
    (rowFrameAt slot old past.length fr updates).get (register wire.address) =
      some (read model wire (appendTuple old input) ((rowSuffixAt slot past updates).eval model
        (appendTuple old input) locals)) := by
  induction updates generalizing past fr with
  | nil => exact agree wire
  | cons u rest ih =>
    let local' := locals.snoc (head := [wordPort]) (.cons (u.evalAt slot old) .nil)
    let fr' := fr.set (.node past.length) (u.evalAt slot old)
    have matched := ih (past ++ [[wordPort]]) fr' local'
      (binding_reads (appendTuple old input) locals fr (u.evalAt slot old) agree) wire
    rw [List.length_append, List.length_singleton] at matched
    rw [rowFrameAt]
    change _ = some (read model wire (appendTuple old input)
      ((rowSuffixAt slot _ rest).eval model (appendTuple old input)
        (locals.snoc (.cons (model.run u.operation.source ((u.operandsAt slot past).read
          (appendTuple old input) locals)) .nil))))
    rw [operation_reads]
    exact matched

theorem row_reads (updates : List (FeedbackUpdate payloads)) (past : List (List PortTy))
    (input old : WordTuple (payloads + 1)) (fr : Frame Reg) (locals : Locals (Val model.value) past)
    (agree : ∀ wire : Origin (headerArgs payloads) past wordPort,
      fr.get (register wire.address) = some (read model wire (appendTuple old input) locals))
    (wire : Origin (headerArgs payloads) (extend past (rowSigs updates)) wordPort) :
    (rowFrame old past.length fr updates).get (register wire.address) =
      some (read model wire (appendTuple old input) ((rowSuffix past updates).eval model
        (appendTuple old input) locals)) :=
  row_reads_at (payloadPort payloads) updates past input old fr locals agree wire

private theorem emit_update {fields arity : Nat} (slot : Fin fields → Port (wordPorts arity) wordPort)
    (u : FeedbackUpdate fields) (past : List (List PortTy)) :
    emitOpsWith (fun p => .arg p.index) (rowSuffixAt slot past [u]) =
      [.binary u.operation.target (.node past.length)
        (.arg (suffixPort (wordPorts arity) (slot u.left)).index)
        (.arg (suffixPort (wordPorts arity) (slot u.right)).index)] := by
  rcases u with ⟨op, _, _, _⟩
  cases op <;> rfl

private theorem update_exec {fields arity : Nat} (slot : Fin fields → Port (wordPorts arity) wordPort)
    (u : FeedbackUpdate fields) (input old : WordTuple arity)
    (pc : Nat) (fr : Frame Reg) (mem : Memory) (agree : ArgsMatch fr (appendTuple old input)) :
    (Op.binary u.operation.target (.node pc)
      (.arg (suffixPort (wordPorts arity) (slot u.left)).index)
      (.arg (suffixPort (wordPorts arity) (slot u.right)).index)).exec fr mem =
      some (fr.set (.node pc) (u.evalAt slot old), mem) := by
  have leftRead := agree (suffixPort (wordPorts arity) (slot u.left))
  have rightRead := agree (suffixPort (wordPorts arity) (slot u.right))
  rw [old_read] at leftRead
  rw [old_read] at rightRead
  simp only [Op.exec, leftRead, rightRead]
  rcases u with ⟨op, _, _, _⟩
  cases op <;> rfl

/-- Run the emitted suffix at its actual offsets in the header. -/
theorem row_steps_at {fields arity : Nat} (slot : Fin fields → Port (wordPorts arity) wordPort)
    (p : Prog Reg) (block : Block Reg) (found : p.block? 0 1 = some block)
    (input old : WordTuple arity) (mem : Memory)
    (updates : List (FeedbackUpdate fields)) (past : List (List PortTy))
    (prefixOps : List (Op Reg)) (prefixLength : prefixOps.length = past.length)
    (tailOps : List (Op Reg))
    (ops : block.ops = prefixOps ++ (emitOpsWith (fun p => .arg p.index) (rowSuffixAt slot past updates) ++ tailOps))
    (fr : Frame Reg) (agree : ArgsMatch fr (appendTuple old input)) :
    Steps p ⟨⟨0, 1, past.length⟩, fr, [], mem⟩
      ⟨⟨0, 1, past.length + updates.length⟩, rowFrameAt slot old past.length fr updates, [], mem⟩ := by
  induction updates generalizing past prefixOps fr with
  | nil =>
    exact .refl
  | cons u rest ih =>
    let op : Op Reg := .binary u.operation.target (.node past.length)
      (.arg (suffixPort (wordPorts arity) (slot u.left)).index) (.arg (suffixPort (wordPorts arity) (slot u.right)).index)
    have emitted : block.ops = prefixOps ++ op ::
        (emitOpsWith (fun p => .arg p.index) (rowSuffixAt slot (past ++ [[wordPort]]) rest) ++ tailOps) := by
      rw [ops]
      have single := emit_update slot u past
      change _ = [op] at single
      have first := (List.cons.inj single).1
      change prefixOps ++ (_ :: _) = _
      rw [first]
      rfl
    have fetch : p.fetch ⟨0, 1, past.length⟩ = some (.op op) := by
      simp [Prog.fetch, found, emitted, prefixLength]
    have step := Transition.op (s := (⟨⟨0, 1, past.length⟩, fr, [], mem⟩ : State Reg))
      fetch (update_exec slot u input old past.length fr mem agree)
    have remainingOps : block.ops = (prefixOps ++ [op]) ++
        (emitOpsWith (fun p => .arg p.index) (rowSuffixAt slot (past ++ [[wordPort]]) rest) ++ tailOps) := by
      rw [emitted, List.append_assoc]
      rfl
    have tail := ih (past ++ [[wordPort]]) (prefixOps ++ [op])
      (by simp [prefixLength]) remainingOps (fr.set (.node past.length) (u.evalAt slot old))
      (fun i => by simpa using agree i)
    rw [List.length_append, List.length_singleton] at tail
    have length : past.length + (u :: rest).length = past.length + 1 + rest.length := by simp; omega
    rw [length]
    exact .head step.step_eq tail

theorem emit_row_length {fields arity : Nat} (slot : Fin fields → Port (wordPorts arity) wordPort)
    (past : List (List PortTy)) (updates : List (FeedbackUpdate fields)) :
    (emitOpsWith (fun p => .arg p.index) (rowSuffixAt slot past updates)).length = updates.length := by
  induction updates generalizing past with
  | nil => rfl
  | cons u rest ih => simp [rowSuffixAt, emitOpsWith, ih]

theorem row_steps (p : Prog Reg) (block : Block Reg) (found : p.block? 0 1 = some block)
    (input old : WordTuple (payloads + 1)) (mem : Memory)
    (updates : List (FeedbackUpdate payloads)) (past : List (List PortTy))
    (prefixOps : List (Op Reg)) (prefixLength : prefixOps.length = past.length)
    (ops : block.ops = prefixOps ++ emitOpsWith (fun p => .arg p.index) (rowSuffix past updates))
    (fr : Frame Reg) (agree : ArgsMatch fr (appendTuple old input)) :
    Steps p ⟨⟨0, 1, past.length⟩, fr, [], mem⟩
      ⟨⟨0, 1, block.ops.length⟩, rowFrame old past.length fr updates, [], mem⟩ := by
  have length : block.ops.length = past.length + updates.length := by
    rw [ops, List.length_append, prefixLength, emit_row_length]
  rw [length]
  exact row_steps_at (payloadPort payloads) p block found input old mem updates past prefixOps prefixLength
    [] (by simpa using ops) fr agree

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Proofs
