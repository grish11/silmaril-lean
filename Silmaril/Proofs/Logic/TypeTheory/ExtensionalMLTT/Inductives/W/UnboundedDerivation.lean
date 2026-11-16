module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Finite.Derivation.Defs

public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

/-- No uniform bound is introduced when replaying the original cofinite rule families. -/
theorem toUnbounded {H : Set Jdg} {Γ : Ctx} {A a b : Tm 0}
    (h : Ctx.JEqH H Γ A a b) : Ctx.JEqB .unbounded H Γ A a b := by
  induction h with
  | hyp hj => exact .hyp hj
  | nil_ok => exact .nil_ok
  | cons_ok => apply Ctx.JEqB.cons_ok <;> first | assumption | trivial
  | var => apply Ctx.JEqB.var <;> assumption
  | univ => apply Ctx.JEqB.univ <;> first | assumption | trivial
  | empty => apply Ctx.JEqB.empty <;> first | assumption | trivial
  | unit => apply Ctx.JEqB.unit <;> first | assumption | trivial
  | nats => apply Ctx.JEqB.nats <;> first | assumption | trivial
  | zero => apply Ctx.JEqB.zero; assumption
  | succ => apply Ctx.JEqB.succ; assumption
  | pi => apply Ctx.JEqB.pi <;> first | assumption | trivial
  | sigma => apply Ctx.JEqB.sigma <;> first | assumption | trivial
  | id => apply Ctx.JEqB.id <;> first | assumption | trivial
  | abs => apply Ctx.JEqB.abs <;> first | assumption | trivial
  | app => apply Ctx.JEqB.app <;> first | assumption | trivial
  | pair => apply Ctx.JEqB.pair <;> first | assumption | trivial
  | fst => apply Ctx.JEqB.fst <;> first | assumption | trivial
  | snd => apply Ctx.JEqB.snd <;> first | assumption | trivial
  | natrec => apply Ctx.JEqB.natrec <;> first | assumption | trivial
  | refl => apply Ctx.JEqB.refl; assumption
  | absurd => apply Ctx.JEqB.absurd <;> first | assumption | trivial
  | beta_app => apply Ctx.JEqB.beta_app <;> first | assumption | trivial
  | beta_fst => apply Ctx.JEqB.beta_fst <;> first | assumption | trivial
  | beta_snd => apply Ctx.JEqB.beta_snd <;> first | assumption | trivial
  | beta_natrec_zero => apply Ctx.JEqB.beta_natrec_zero <;> first | assumption | trivial
  | beta_natrec_succ => apply Ctx.JEqB.beta_natrec_succ <;> first | assumption | trivial
  | reflect => apply Ctx.JEqB.reflect <;> assumption
  | id_uip => apply Ctx.JEqB.id_uip <;> assumption
  | unit_ext => apply Ctx.JEqB.unit_ext; assumption
  | pi_ext => apply Ctx.JEqB.pi_ext <;> first | assumption | trivial
  | sigma_ext => apply Ctx.JEqB.sigma_ext <;> first | assumption | trivial
  | symm => apply Ctx.JEqB.symm; assumption
  | trans => apply Ctx.JEqB.trans <;> assumption
  | conv => apply Ctx.JEqB.conv <;> first | assumption | trivial
  | cumul => apply Ctx.JEqB.cumul <;> first | assumption | trivial
  | wtype => apply Ctx.JEqB.wtype <;> first | assumption | trivial
  | sup => apply Ctx.JEqB.sup <;> first | assumption | trivial
  | wrec => apply Ctx.JEqB.wrec <;> first | assumption | trivial
  | beta_wrec => apply Ctx.JEqB.beta_wrec <;> first | assumption | trivial

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
