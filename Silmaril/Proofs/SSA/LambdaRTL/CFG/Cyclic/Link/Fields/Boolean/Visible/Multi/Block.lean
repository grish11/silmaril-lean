module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Multi.Defs
import Silmaril.Semantics.ITree.Thms

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Multi

open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean (Packet)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Multi
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Program (bit primitive)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.Bridge.NamedFlat (treeModel)
open Silmaril.Elgot.ITree (Tree vis vis_bind)
open Silmaril.Elgot.ITree.Finite (Event)

variable {F : Type} {K : Type 1} {n a b : Nat}

abbrev model (F : Type) := treeModel.{0, 0} (primitive (F := F))

private def unpacked (fields : List (Fin n)) (packet : Packet n) (input : Register n → Value Atom) :
    Register n → Value Atom
  | ⟨none⟩ => .unit
  | ⟨some i⟩ => if i ∈ fields then bit (packet i) else input (fieldReg i)

private theorem unpack_eval (packet : Packet n) (fields : List (Fin n)) (body : Body (Register n) K F)
    (input : Register n → Value Atom) (source : input cursor = encodeFields packet fields) :
    (unpack fields body).evalJump (model F) input = body.evalJump (model F) (unpacked fields packet input) := by
  induction fields generalizing input with
  | nil =>
    apply congrArg (body.evalJump (model F))
    funext reg
    rcases reg with ⟨_ | i⟩
    · exact source
    · simp [unpacked, fieldReg]
  | cons field fields ih =>
    let next := upd (upd input (fieldReg field) (bit (packet field))) cursor (encodeFields packet fields)
    have cursorRead : next cursor = encodeFields packet fields := by simp [next, upd]
    have rest : unpacked fields packet next = unpacked (field :: fields) packet input := by
      funext reg
      rcases reg with ⟨_ | i⟩
      · rfl
      · by_cases same : i = field <;> simp [unpacked, next, upd, fieldReg, cursor, same]
    have splitPair : (model F).unpair (.pair (bit (packet field)) (encodeFields packet fields)) =
        pure (bit (packet field), encodeFields packet fields) := rfl
    simp only [unpack, Body.evalJump, Body.exec, Op.eval, Val.eval, pure_bind, source, encodeFields, splitPair]
    change (unpack fields body).evalJump (model F) next = _
    rw [ih next cursorRead, rest]
    rfl

private theorem pack_eval (packet : Packet n) (fields : List (Fin n)) (regs : Register n → Value Atom)
    (reads : ∀ i, regs (fieldReg i) = bit (packet i)) :
    (packRegs fields).eval (model F) regs = encodeFields packet fields := by
  induction fields with
  | nil => rfl
  | cons i rest ih =>
    simp only [packRegs, Val.eval, encodeFields, reads, ih]
    rfl

private theorem read_field (i : Fin n) (packet : Packet n) (input : Register n → Value Atom) :
    unpacked (List.finRange n) packet input (fieldReg i) = bit (packet i) := by
  simp [unpacked, fieldReg]

private theorem packed_after_cursor (packet : Packet n) (input : Register n → Value Atom) :
    (packRegs (List.finRange n)).eval (model F)
        (upd (unpacked (List.finRange n) packet input) cursor Value.unit) = encode packet :=
  pack_eval packet _ _ fun i => by
    simpa [upd, fieldReg, cursor] using read_field i packet input

private theorem packed_after_reply (packet : Packet n) (destination : Fin n) (reply : Bool)
    (input : Register n → Value Atom) :
    (packRegs (List.finRange n)).eval (model F)
        (upd (unpacked (List.finRange n) packet input) (fieldReg destination) (bit reply)) =
      encode (replace packet destination reply) :=
  pack_eval (replace packet destination reply) _ _ fun i => by
    by_cases same : i = destination
    · subst i
      simp [upd, replace]
    · simpa [upd, replace, fieldReg, same] using read_field i packet input

private theorem primitive_bit (symbol : F) (arg : Bool) :
    (model F).app symbol (bit arg) =
      vis (.ask (symbol, arg)) (fun reply => pure (bit reply)) := by
  cases arg <;> rfl

theorem eval_block (program : Program F a b n) (row : Instruction F _ n) (packet : Packet n)
    (input : Register n → Value Atom) :
    (program.compiledBlock row).body.evalJump (model F) (upd input cursor (encode packet)) =
      match row with
      | .jump target => pure (⟨target⟩, encode packet)
      | .branch field yes no => pure (⟨if packet field then yes else no⟩, encode packet)
      | .apply symbol arg dst target =>
        vis (.ask (symbol, packet arg)) (fun reply => pure (⟨target⟩, encode (replace packet dst reply))) := by
  let initial := upd input cursor (encode packet)
  have source : initial cursor = encodeFields packet (List.finRange n) := by simp [initial, upd, encode]
  cases row with
  | jump target =>
    simp [Program.compiledBlock, Body.evalJump, Body.exec, Term.exec, Val.eval, upd]
  | branch field yes no =>
    simp only [Program.compiledBlock]
    rw [unpack_eval packet _ _ initial source]
    have splitBit : (model F).split (bit (packet field)) =
        pure (if packet field then .inl Value.unit else .inr Value.unit) := by
      cases packet field <;> rfl
    simp only [Body.evalJump, Body.exec, Term.exec, Op.eval, Val.eval, pure_bind, read_field, splitBit]
    cases packet field <;> simp [packed_after_cursor]
  | apply symbol arg dst target =>
    simp only [Program.compiledBlock]
    rw [unpack_eval packet _ _ initial source]
    simp only [Body.evalJump, Body.exec, Term.exec, Op.eval, Val.eval, read_field, primitive_bit, vis_bind,
      pure_bind, packed_after_reply]

private theorem bit_injective : Function.Injective bit := by
  intro left right same
  cases left <;> cases right <;> simp_all [bit]

private theorem encodeFields_agrees (left right : Packet n) (fields : List (Fin n)) (i : Fin n)
    (inside : i ∈ fields) (equal : encodeFields left fields = encodeFields right fields) :
    left i = right i := by
  induction fields with
  | nil => simp at inside
  | cons field rest ih =>
    obtain ⟨head, tail⟩ := Value.pair.inj equal
    rcases List.mem_cons.mp inside with rfl | later
    · exact bit_injective head
    · exact ih later tail

theorem encode_injective : Function.Injective (encode (n := n)) :=
  fun left right equal => funext fun i => encodeFields_agrees left right _ i (List.mem_finRange i) equal

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Multi
