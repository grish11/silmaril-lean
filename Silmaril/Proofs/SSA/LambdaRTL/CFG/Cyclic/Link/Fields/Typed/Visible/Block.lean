module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Defs
import Silmaril.Semantics.ITree.Thms

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.PacketType (encode decode)
open Silmaril.Elgot.ITree (Tree vis vis_bind)
open Silmaril.Elgot.ITree.Finite (Event)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.Bridge.NamedFlat (treeModel)

variable {F L : Type} {signature : PrimitiveSignature F} {types : L → PacketType} {Γ : List PacketType}

abbrev model (signature : PrimitiveSignature F) := treeModel.{0, 0} signature.primitive

theorem decode_encode (ty : PacketType) (value : Denote ty) : decode ty (encode ty value) = some value := by
  induction ty with
  | base x => exact x.elim
  | empty => exact value.elim
  | unit => cases value; rfl
  | product x y ihX ihY =>
    rcases value with ⟨left, right⟩
    change (do return (← decode x (encode x left), ← decode y (encode y right))) = some (left, right)
    rw [ihX left, ihY right]
    rfl
  | coprod x y ihX ihY =>
    cases value with
    | inl left =>
      change (decode x (encode x left)).map Sum.inl = some (.inl left)
      rw [ihX left]
      rfl
    | inr right =>
      change (decode y (encode y right)).map Sum.inr = some (.inr right)
      rw [ihY right]
      rfl

theorem encode_injective (ty : PacketType) : Function.Injective (encode ty) := by
  intro x y eq
  exact Option.some.inj ((decode_encode ty x).symm.trans ((congrArg (decode ty) eq).trans (decode_encode ty y)))

def encodeTransfer (packet : PacketAt types) : ULift.{1} L × Value Atom :=
  (⟨packet.1⟩, encode (types packet.1) packet.2)

def Agrees (env : Env Γ) (store : Register → Value Atom) : Prop :=
  ∀ ty (slot : Slot Γ ty), store slot.reg = encode ty (env slot)

private theorem reg_lt {ty : PacketType} (slot : Slot Γ ty) : slot.reg.down < Γ.length := by
  induction slot with
  | here => exact Nat.lt_succ_self _
  | there _ ih => exact Nat.lt_succ_of_lt ih

private theorem agrees_extend {env : Env Γ} {store : Register → Value Atom}
    (agrees : Agrees env store) {ty : PacketType} (value : Denote ty) :
    Agrees (extend env value) (upd store ⟨Γ.length⟩ (encode ty value)) := by
  intro slotType slot
  cases slot with
  | here => simp [Slot.reg, extend, upd]
  | there old =>
    have fresh : old.reg ≠ (⟨Γ.length⟩ : Register) :=
      fun h => (Nat.ne_of_lt (reg_lt old)) (congrArg ULift.down h)
    simpa [Slot.reg, extend, upd, fresh] using agrees _ old

theorem agrees_single {ty : PacketType} (value : Denote ty) (store : Register → Value Atom) :
    Agrees (single value) (upd store ⟨0⟩ (encode ty value)) := by
  intro slotType slot
  cases slot with
  | here => simp [Slot.reg, single, upd]
  | there old => nomatch old

private theorem expr_sound (signature : PrimitiveSignature F) {ty : PacketType} (expr : Expr Γ ty)
    (env : Env Γ) (store : Register → Value Atom) (agrees : Agrees env store) :
    expr.compile.eval (model signature) store = encode ty (expr.eval env) := by
  induction expr with
  | var slot => exact agrees _ slot
  | unit => rfl
  | pair _ _ ihX ihY =>
    simp only [Expr.compile, Expr.eval, Val.eval, encode, ihX, ihY]
    rfl

private theorem split_inl (signature : PrimitiveSignature F) {x y : PacketType} (arg : Denote x) :
    (model signature).split (encode (.coprod x y) (.inl arg)) = pure (.inl (encode x arg)) := rfl

private theorem split_inr (signature : PrimitiveSignature F) {x y : PacketType} (arg : Denote y) :
    (model signature).split (encode (.coprod x y) (.inr arg)) = pure (.inr (encode y arg)) := rfl

private theorem unpair (signature : PrimitiveSignature F) {x y : PacketType} (a : Denote x) (b : Denote y) :
    (model signature).unpair (encode (.product x y) (a, b)) = pure (encode x a, encode y b) := rfl

private theorem branch_sound (signature : PrimitiveSignature F) (branch : Branch types Γ) (env : Env Γ)
    (store : Register → Value Atom) (agrees : Agrees env store) :
    (Body.term branch.compile).evalJump (model signature) store = pure (encodeTransfer (branch.transfer env)) := by
  induction branch generalizing store with
  | jump label value =>
    simp [Branch.compile, Branch.transfer, encodeTransfer, Body.evalJump, Body.exec, Term.exec,
      expr_sound signature value env store agrees]
  | case value left right ihL ihR =>
    simp only [Branch.compile, Body.evalJump, Body.exec, Term.exec, Op.eval, pure_bind,
      expr_sound signature value env store agrees, Branch.transfer]
    cases selected : value.eval env with
    | inl arg =>
      rw [split_inl, pure_bind]
      exact ihL (extend env arg) _ (agrees_extend agrees arg)
    | inr arg =>
      rw [split_inr, pure_bind]
      exact ihR (extend env arg) _ (agrees_extend agrees arg)

theorem code_sound (code : Code signature types Γ) (env : Env Γ) (store : Register → Value Atom)
    (agrees : Agrees env store) :
    code.compile.evalJump (model signature) store =
      match code.action env with
      | .inr next => pure (encodeTransfer next)
      | .inl ⟨key, next⟩ => vis (.ask key) fun reply => pure (encodeTransfer (next reply)) := by
  induction code generalizing store with
  | term branch => exact branch_sound signature branch env store agrees
  | unpack value tail ih =>
    simp only [Code.compile, Body.evalJump, Body.exec, Op.eval, pure_bind,
      expr_sound signature value env store agrees, Code.action]
    obtain ⟨left, right⟩ := value.eval env
    rw [unpair, pure_bind]
    exact ih (extend (extend env left) right) _ (agrees_extend (agrees_extend agrees left) right)
  | apply op arg label next =>
    simp only [Code.compile, Code.action, Body.evalJump, Body.exec, Term.exec, Op.eval,
      expr_sound signature arg env store agrees]
    have event : (model signature).app op (encode (signature.argument op) (arg.eval env)) =
        vis (Event.ask (Reply := signature.Reply) ⟨op, arg.eval env⟩) (fun reply => pure (encode (signature.reply op) reply)) := by
      change signature.primitive op _ = _
      simp [PrimitiveSignature.primitive, decode_encode]
    rw [event, vis_bind]
    congr 1
    funext reply
    simp only [pure_bind, encodeTransfer,
      expr_sound signature next (extend env reply) _ (agrees_extend agrees reply)]

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
