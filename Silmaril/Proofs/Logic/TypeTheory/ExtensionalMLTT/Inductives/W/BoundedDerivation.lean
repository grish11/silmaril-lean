module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Finite.Derivation.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

/-- Discard the uniform universe bound without altering an inference rule. -/
theorem forget {levels : RuleBudget} {H : Set Jdg} {Γ : Ctx} {A a b : Tm 0}
    (h : Ctx.JEqB levels H Γ A a b) : Ctx.JEqH H Γ A a b := by
  induction h with
  | hyp hj => exact Ctx.JEqH.hyp hj
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

/-- Change theory and enlarge the uniform universe bound in one induction. -/
theorem transport {levels more : RuleBudget} (hlevels : levels ≤ more) {H H' : Set Jdg}
    (hh : ∀ j ∈ H, Ctx.JEqB more H' j.Γ j.A j.a j.b)
    {Γ : Ctx} {A a b : Tm 0} (h : Ctx.JEqB levels H Γ A a b) :
    Ctx.JEqB more H' Γ A a b := by
  induction h with
  | hyp hj => exact hh _ hj
  | nil_ok => exact Ctx.JEqB.nil_ok
  | cons_ok =>
    apply Ctx.JEqB.cons_ok <;> try assumption
    exact RuleBudget.Allows.mono hlevels (by assumption)
  | var => apply Ctx.JEqB.var <;> assumption
  | univ =>
    apply Ctx.JEqB.univ <;> try assumption
    exact RuleBudget.Allows.mono hlevels (by assumption)
  | empty =>
    apply Ctx.JEqB.empty <;> try assumption
    exact RuleBudget.Allows.mono hlevels (by assumption)
  | unit =>
    apply Ctx.JEqB.unit <;> try assumption
    exact RuleBudget.Allows.mono hlevels (by assumption)
  | nats =>
    apply Ctx.JEqB.nats <;> try assumption
    exact RuleBudget.Allows.mono hlevels (by assumption)
  | zero => apply Ctx.JEqB.zero; assumption
  | succ => apply Ctx.JEqB.succ; assumption
  | pi =>
    apply Ctx.JEqB.pi <;> try assumption
    exact RuleBudget.Allows.mono hlevels (by assumption)
  | sigma =>
    apply Ctx.JEqB.sigma <;> try assumption
    exact RuleBudget.Allows.mono hlevels (by assumption)
  | id =>
    apply Ctx.JEqB.id <;> try assumption
    exact RuleBudget.Allows.mono hlevels (by assumption)
  | abs =>
    apply Ctx.JEqB.abs <;> try assumption
    exact RuleBudget.Allows.mono hlevels (by assumption)
  | app =>
    apply Ctx.JEqB.app <;> try assumption
    exact RuleBudget.Allows.mono hlevels (by assumption)
  | pair =>
    apply Ctx.JEqB.pair <;> try assumption
    exact RuleBudget.Allows.mono hlevels (by assumption)
  | fst =>
    apply Ctx.JEqB.fst <;> try assumption
    exact RuleBudget.Allows.mono hlevels (by assumption)
  | snd =>
    apply Ctx.JEqB.snd <;> try assumption
    exact RuleBudget.Allows.mono hlevels (by assumption)
  | natrec =>
    apply Ctx.JEqB.natrec <;> try assumption
    exact RuleBudget.Allows.mono hlevels (by assumption)
  | refl => apply Ctx.JEqB.refl; assumption
  | absurd =>
    apply Ctx.JEqB.absurd <;> try assumption
    exact RuleBudget.Allows.mono hlevels (by assumption)
  | beta_app =>
    apply Ctx.JEqB.beta_app <;> try assumption
    exact RuleBudget.Allows.mono hlevels (by assumption)
  | beta_fst =>
    apply Ctx.JEqB.beta_fst <;> try assumption
    exact RuleBudget.Allows.mono hlevels (by assumption)
  | beta_snd =>
    apply Ctx.JEqB.beta_snd <;> try assumption
    exact RuleBudget.Allows.mono hlevels (by assumption)
  | beta_natrec_zero =>
    apply Ctx.JEqB.beta_natrec_zero <;> try assumption
    exact RuleBudget.Allows.mono hlevels (by assumption)
  | beta_natrec_succ =>
    apply Ctx.JEqB.beta_natrec_succ <;> try assumption
    exact RuleBudget.Allows.mono hlevels (by assumption)
  | reflect => apply Ctx.JEqB.reflect <;> assumption
  | id_uip => apply Ctx.JEqB.id_uip <;> assumption
  | unit_ext => apply Ctx.JEqB.unit_ext; assumption
  | pi_ext =>
    apply Ctx.JEqB.pi_ext <;> try assumption
    exact RuleBudget.Allows.mono hlevels (by assumption)
  | sigma_ext =>
    apply Ctx.JEqB.sigma_ext <;> try assumption
    exact RuleBudget.Allows.mono hlevels (by assumption)
  | symm => apply Ctx.JEqB.symm; assumption
  | trans => apply Ctx.JEqB.trans <;> assumption
  | conv =>
    apply Ctx.JEqB.conv <;> try assumption
    exact RuleBudget.Allows.mono hlevels (by assumption)
  | cumul =>
    apply Ctx.JEqB.cumul <;> try assumption
    exact RuleBudget.Allows.mono hlevels (by assumption)
  | wtype =>
    apply Ctx.JEqB.wtype <;> try assumption
    exact RuleBudget.Allows.mono hlevels (by assumption)
  | sup =>
    apply Ctx.JEqB.sup <;> try assumption
    exact RuleBudget.Allows.mono hlevels (by assumption)
  | wrec =>
    apply Ctx.JEqB.wrec <;> try assumption
    all_goals exact RuleBudget.Allows.mono hlevels (by assumption)
  | beta_wrec =>
    apply Ctx.JEqB.beta_wrec <;> try assumption
    all_goals exact RuleBudget.Allows.mono hlevels (by assumption)

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
