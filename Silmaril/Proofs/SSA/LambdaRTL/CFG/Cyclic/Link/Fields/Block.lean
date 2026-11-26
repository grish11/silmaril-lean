module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Defs

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields

open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Comparison
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields

variable {V K F α : Type} {n w : Nat} {M : Type → Type}

private theorem eval_packed (model : Model F M α) (store : V → α) (values : Fin w → Val V) :
    (packed values).eval model store = encode model (fun i => (values i).eval model store) := by
  induction w with
  | zero => rfl
  | succ w ih => simp only [packed, Val.eval, encode, ih]

private theorem fields_eval (model : Model F M α) (packet : Fin n → α) {value : Val (Fin n)}
    {fields : Fin w → Fin n} (decoded : fieldMap? w value = some fields) :
    value.eval model packet = encode model (packet ∘ fields) := by
  induction w generalizing value with
  | zero =>
    cases value <;> simp_all [fieldMap?, Val.eval, encode]
  | succ w ih =>
    cases value with
    | var i => simp [fieldMap?] at decoded
    | unit => simp [fieldMap?] at decoded
    | pair head tail =>
      cases head with
      | unit => simp [fieldMap?] at decoded
      | pair a b => simp [fieldMap?] at decoded
      | var i =>
        cases rest : fieldMap? w tail with
        | none => simp [fieldMap?, rest] at decoded
        | some tailFields =>
          have same : Fin.cons i tailFields = fields := by simpa [fieldMap?, rest] using decoded
          subst fields
          simp [Val.eval, encode, Function.comp_def, ih rest]

private def Agrees (model : Model F M α) (packet : Fin n → α)
    (env : V → Option (Val (Fin n))) (store : V → α) : Prop :=
  ∀ reg shape, env reg = some shape → store reg = shape.eval model packet

private theorem read_eval {model : Model F M α} {packet : Fin n → α}
    {env : V → Option (Val (Fin n))} {store : V → α}
    (agrees : Agrees model packet env store) {value : Val V} {shape : Val (Fin n)}
    (found : read? env value = some shape) : value.eval model store = shape.eval model packet := by
  induction value generalizing shape with
  | var reg => exact agrees reg shape found
  | unit =>
    have same : Val.unit = shape := Option.some.inj found
    subst shape
    rfl
  | pair left right ihL ihR =>
    cases leftRead : read? env left with
    | none => simp [read?, leftRead] at found
    | some l =>
      cases rightRead : read? env right with
      | none => simp [read?, leftRead, rightRead] at found
      | some r =>
        have same : Val.pair l r = shape := by simpa [read?, leftRead, rightRead] using found
        subst shape
        simp [Val.eval, ihL leftRead, ihR rightRead]

variable [DecidableEq V]

private theorem agrees_upd {model : Model F M α} {packet : Fin n → α}
    {env : V → Option (Val (Fin n))} {store : V → α} (agrees : Agrees model packet env store)
    (dst : V) (shape : Val (Fin n)) :
    Agrees model packet (upd env dst (some shape)) (upd store dst (shape.eval model packet)) := by
  intro reg other found
  by_cases same : reg = dst
  · subst reg
    have eq : shape = other := by simpa [upd] using found
    simp [upd, eq]
  · exact by simpa [upd, same] using agrees reg other (by simpa [upd, same] using found)

variable [Monad M] [LawfulMonad M]

private theorem body_sound (model : PairModel F M α) (packet : Fin n → α) (width : K → Nat) (body : Body V K F)
    {env : V → Option (Val (Fin n))} {store : V → α}
    (agrees : Agrees model.val packet env store) {target : K} {fields : Route n (width target)}
    (accepted : bodyTo? width env body = some ⟨target, fields⟩) :
    body.evalJump model.val store = pure (target, encode model.val (packet ∘ fields)) := by
  induction body generalizing env store with
  | let1 dst op tail ih =>
    cases op with
    | val value =>
      cases found : read? env value with
      | none => simp [bodyTo?, found] at accepted
      | some shape =>
        have evaluated := read_eval agrees found
        simp only [Body.evalJump, Body.exec, Op.eval, pure_bind, evaluated]
        exact ih (agrees_upd agrees dst shape) (by simpa [bodyTo?, found] using accepted)
    | _ => simp [bodyTo?] at accepted
  | let2 left right op tail ih =>
    cases op with
    | val value =>
      cases found : read? env value with
      | none => simp [bodyTo?, found] at accepted
      | some shape =>
        cases shape with
        | var i => simp [bodyTo?, found] at accepted
        | unit => simp [bodyTo?, found] at accepted
        | pair fst snd =>
          have evaluated := read_eval agrees found
          simp only [Body.evalJump, Body.exec, Op.eval, pure_bind, evaluated, Val.eval,
            model.property.unpair_pair]
          exact ih (agrees_upd (agrees_upd agrees left fst) right snd)
            (by simpa [bodyTo?, found] using accepted)
    | _ => simp [bodyTo?] at accepted
  | term term =>
    cases term with
    | case => simp [bodyTo?] at accepted
    | br label value =>
      cases found : read? env value with
      | none => simp [bodyTo?, found] at accepted
      | some shape =>
        cases decoded : fieldMap? (width label) shape with
        | none => simp [bodyTo?, found, decoded] at accepted
        | some route =>
          have same : (⟨label, route⟩ : (k : K) × Route n (width k)) = ⟨target, fields⟩ :=
            Option.some.inj (by simpa [bodyTo?, found, decoded] using accepted)
          cases same
          simp [Body.evalJump, Body.exec, Term.exec, read_eval agrees found, fields_eval model.val packet decoded]

theorem block_to_sound (model : PairModel F M α) (packet : Fin n → α) (width : K → Nat) (block : Block V K F)
    (store : V → α) {target : K} {fields : Route n (width target)} (accepted : blockTo? n width block = some ⟨target, fields⟩) :
    block.body.evalJump model.val (upd store block.param (encode model.val packet)) =
      pure (target, encode model.val (packet ∘ fields)) := by
  apply body_sound model packet width block.body _ accepted
  intro reg shape found
  by_cases same : reg = block.param
  · subst reg
    have eq : packed (fun i : Fin n => .var i) = shape := by simpa [upd] using found
    subst shape
    simp [upd, eval_packed, Val.eval]
  · simp [upd, same] at found

theorem block_sound (model : PairModel F M α) (packet : Fin n → α) (block : Block V K F)
    (store : V → α) {target : K} {fields : FieldMap n} (accepted : block? n block = some (target, fields)) :
    block.body.evalJump model.val (upd store block.param (encode model.val packet)) =
      pure (target, encode model.val (packet ∘ fields)) := by
  cases checked : blockTo? n (fun _ => n) block with
  | none => simp [block?, checked] at accepted
  | some result =>
    obtain ⟨label, route⟩ := result
    have same : label = target ∧ route = fields := by simpa [block?, checked] using accepted
    obtain ⟨rfl, rfl⟩ := same
    exact block_to_sound model packet (fun _ => n) block store checked

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields
