module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Rules.Defs

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

/-- Substitute derivations for hypothesis leaves. -/
theorem Ctx.JEqH.bind {H H' : Set Jdg}
    (hh : ∀ j ∈ H, Ctx.JEqH H' j.Γ j.A j.a j.b)
    {Γ : Ctx} {A a b : Tm 0} (h : Ctx.JEqH H Γ A a b) :
    Ctx.JEqH H' Γ A a b := by
  induction h with
  | hyp hj => exact hh _ hj
  | nil_ok => exact Ctx.JEqH.nil_ok
  | cons_ok => apply Ctx.JEqH.cons_ok <;> assumption
  | var => apply Ctx.JEqH.var <;> assumption
  | univ => apply Ctx.JEqH.univ; assumption
  | empty => apply Ctx.JEqH.empty; assumption
  | unit => apply Ctx.JEqH.unit; assumption
  | nats => apply Ctx.JEqH.nats; assumption
  | zero => apply Ctx.JEqH.zero; assumption
  | succ => apply Ctx.JEqH.succ; assumption
  | pi => apply Ctx.JEqH.pi <;> assumption
  | sigma => apply Ctx.JEqH.sigma <;> assumption
  | id => apply Ctx.JEqH.id <;> assumption
  | abs => apply Ctx.JEqH.abs <;> assumption
  | app => apply Ctx.JEqH.app <;> assumption
  | pair => apply Ctx.JEqH.pair <;> assumption
  | fst => apply Ctx.JEqH.fst <;> assumption
  | snd => apply Ctx.JEqH.snd <;> assumption
  | natrec => apply Ctx.JEqH.natrec <;> assumption
  | refl => apply Ctx.JEqH.refl; assumption
  | absurd => apply Ctx.JEqH.absurd <;> assumption
  | beta_app => apply Ctx.JEqH.beta_app <;> assumption
  | beta_fst => apply Ctx.JEqH.beta_fst <;> assumption
  | beta_snd => apply Ctx.JEqH.beta_snd <;> assumption
  | beta_natrec_zero => apply Ctx.JEqH.beta_natrec_zero <;> assumption
  | beta_natrec_succ => apply Ctx.JEqH.beta_natrec_succ <;> assumption
  | reflect => apply Ctx.JEqH.reflect <;> assumption
  | id_uip => apply Ctx.JEqH.id_uip <;> assumption
  | unit_ext => apply Ctx.JEqH.unit_ext; assumption
  | pi_ext => apply Ctx.JEqH.pi_ext <;> assumption
  | sigma_ext => apply Ctx.JEqH.sigma_ext <;> assumption
  | symm => apply Ctx.JEqH.symm; assumption
  | trans => apply Ctx.JEqH.trans <;> assumption
  | conv => apply Ctx.JEqH.conv <;> assumption
  | cumul => apply Ctx.JEqH.cumul <;> assumption
  | wtype => apply Ctx.JEqH.wtype <;> assumption
  | sup => apply Ctx.JEqH.sup <;> assumption
  | wrec => apply Ctx.JEqH.wrec <;> assumption
  | beta_wrec => apply Ctx.JEqH.beta_wrec <;> assumption

/-- Increasing the theory preserves derivability. -/
theorem Ctx.JEqH.mono {H H' : Set Jdg} (hh : H ⊆ H')
    {Γ : Ctx} {A a b : Tm 0} (h : Ctx.JEqH H Γ A a b) :
    Ctx.JEqH H' Γ A a b :=
  h.bind fun _ hj => .hyp (hh hj)


end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
