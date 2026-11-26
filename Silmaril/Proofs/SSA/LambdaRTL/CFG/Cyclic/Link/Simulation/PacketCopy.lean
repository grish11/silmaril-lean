module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Simulation.Defs

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.PacketCopy

open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.PacketCopy

variable {V K K' F α : Type} [DecidableEq V]

private theorem of_target {available : Finset V} {body : Body V K F} {target : K}
    (accepted : target? available body = some target) : Forwards available body target := by
  induction body generalizing available with
  | let1 dst op rest ih =>
    cases op with
    | val value =>
      cases value with
      | var src =>
        by_cases read : src ∈ available
        · exact .copy read (ih (by simpa [target?, read] using accepted))
        · simp [target?, read] at accepted
      | _ => simp [target?] at accepted
    | _ => simp [target?] at accepted
  | let2 => simp [target?] at accepted
  | term term =>
    cases term with
    | br label value =>
      cases value with
      | var src =>
        by_cases read : src ∈ available
        · have same : label = target := by simpa [target?, read] using accepted
          subst target
          exact .jump read
        · simp [target?, read] at accepted
      | _ => simp [target?] at accepted
    | case => simp [target?] at accepted

theorem target_iff {available : Finset V} {body : Body V K F} {target : K} :
    target? available body = some target ↔ Forwards available body target := by
  refine ⟨of_target, fun typed => ?_⟩
  induction typed with
  | jump read => simp [target?, read]
  | copy read next ih => simp [target?, read, ih]

theorem relabel {available : Finset V} {body : Body V K F} {target : K}
    (typed : Forwards available body target) (rename : K → K') :
    Forwards available (body.relabel rename) (rename target) := by
  induction typed with
  | jump read => exact .jump read
  | copy read next ih => exact .copy read ih

theorem target_relabel (rename : K → K') (available : Finset V) (body : Body V K F) :
    target? available (body.relabel rename) = (target? available body).map rename := by
  induction body generalizing available with
  | let1 dst op rest ih =>
    cases op with
    | val value =>
      cases value with
      | var src => by_cases read : src ∈ available <;> simp [Body.relabel, target?, read, ih]
      | _ => rfl
    | _ => rfl
  | let2 => rfl
  | term term =>
    cases term with
    | br label value =>
      cases value with
      | var src => by_cases read : src ∈ available <;> simp [Body.relabel, Term.relabel, target?, read]
      | _ => rfl
    | case => rfl

theorem evalJump {M : Type → Type} [Monad M] [LawfulMonad M]
    (model : Model F M α) {available : Finset V} {body : Body V K F} {target : K}
    (typed : Forwards available body target) (store : V → α) (packet : α)
    (agrees : ∀ reg ∈ available, store reg = packet) :
    body.evalJump model store = pure (target, packet) := by
  induction typed generalizing store with
  | jump read =>
    simp [Body.evalJump, Body.exec, Term.exec, Val.eval, agrees _ read]
  | @copy available src dst rest target read next ih =>
    simp only [Body.evalJump, Body.exec, Op.eval, Val.eval, pure_bind, agrees src read]
    apply ih
    intro reg known
    by_cases same : reg = dst
    · subst reg
      simp [upd]
    · rw [upd, ite_eq_right same]
      exact agrees reg ((Finset.mem_insert.mp known).resolve_left same)

theorem evalJump_packet {M : Type → Type} [Monad M] [LawfulMonad M]
    (model : Model F M α) (source : Block V K F) {target : K}
    (typed : Forwards {source.param} source.body target) (store : V → α) (packet : α) :
    source.body.evalJump model (upd store source.param packet) = pure (target, packet) := by
  apply evalJump model typed
  intro reg known
  obtain rfl := Finset.mem_singleton.mp known
  simp [upd]

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.PacketCopy
