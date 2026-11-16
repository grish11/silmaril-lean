module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Derivation.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedDerivation

open Silmaril.Logic.TypeTheory.ExtensionalMLTT

/-- Discard the uniform universe bound without altering an inference rule. -/
theorem forget {levels : ℕ} {H : Set EJdg} {Γ : ECtx} {A a b : ETm 0}
    (h : ECtx.JEqB levels H Γ A a b) : ECtx.JEqH H Γ A a b := by
  induction h with
  | hyp hj => exact ECtx.JEqH.hyp hj
  | nil_ok => exact ECtx.JEqH.nil_ok
  | cons_ok => apply ECtx.JEqH.cons_ok <;> assumption
  | var => apply ECtx.JEqH.var <;> assumption
  | univ => apply ECtx.JEqH.univ; assumption
  | empty => apply ECtx.JEqH.empty; assumption
  | unit => apply ECtx.JEqH.unit; assumption
  | nats => apply ECtx.JEqH.nats; assumption
  | zero => apply ECtx.JEqH.zero; assumption
  | succ => apply ECtx.JEqH.succ; assumption
  | pi => apply ECtx.JEqH.pi <;> assumption
  | sigma => apply ECtx.JEqH.sigma <;> assumption
  | id => apply ECtx.JEqH.id <;> assumption
  | abs => apply ECtx.JEqH.abs <;> assumption
  | app => apply ECtx.JEqH.app <;> assumption
  | pair => apply ECtx.JEqH.pair <;> assumption
  | fst => apply ECtx.JEqH.fst <;> assumption
  | snd => apply ECtx.JEqH.snd <;> assumption
  | natrec => apply ECtx.JEqH.natrec <;> assumption
  | refl => apply ECtx.JEqH.refl; assumption
  | absurd => apply ECtx.JEqH.absurd <;> assumption
  | beta_app => apply ECtx.JEqH.beta_app <;> assumption
  | beta_fst => apply ECtx.JEqH.beta_fst <;> assumption
  | beta_snd => apply ECtx.JEqH.beta_snd <;> assumption
  | beta_natrec_zero => apply ECtx.JEqH.beta_natrec_zero <;> assumption
  | beta_natrec_succ => apply ECtx.JEqH.beta_natrec_succ <;> assumption
  | reflect => apply ECtx.JEqH.reflect <;> assumption
  | id_uip => apply ECtx.JEqH.id_uip <;> assumption
  | unit_ext => apply ECtx.JEqH.unit_ext; assumption
  | pi_ext => apply ECtx.JEqH.pi_ext <;> assumption
  | sigma_ext => apply ECtx.JEqH.sigma_ext <;> assumption
  | symm => apply ECtx.JEqH.symm; assumption
  | trans => apply ECtx.JEqH.trans <;> assumption
  | conv => apply ECtx.JEqH.conv <;> assumption
  | cumul => apply ECtx.JEqH.cumul <;> assumption

/-- Change theory and enlarge the uniform universe bound in one induction. -/
theorem transport {levels more : ℕ} (hlevels : levels ≤ more) {H H' : Set EJdg}
    (hh : ∀ j ∈ H, ECtx.JEqB more H' j.Γ j.A j.a j.b)
    {Γ : ECtx} {A a b : ETm 0} (h : ECtx.JEqB levels H Γ A a b) :
    ECtx.JEqB more H' Γ A a b := by
  induction h with
  | hyp hj => exact hh _ hj
  | nil_ok => exact ECtx.JEqB.nil_ok
  | cons_ok =>
    apply ECtx.JEqB.cons_ok <;> try assumption
    omega
  | var => apply ECtx.JEqB.var <;> assumption
  | univ =>
    apply ECtx.JEqB.univ <;> try assumption
    omega
  | empty =>
    apply ECtx.JEqB.empty <;> try assumption
    omega
  | unit =>
    apply ECtx.JEqB.unit <;> try assumption
    omega
  | nats =>
    apply ECtx.JEqB.nats <;> try assumption
    omega
  | zero => apply ECtx.JEqB.zero; assumption
  | succ => apply ECtx.JEqB.succ; assumption
  | pi =>
    apply ECtx.JEqB.pi <;> try assumption
    omega
  | sigma =>
    apply ECtx.JEqB.sigma <;> try assumption
    omega
  | id =>
    apply ECtx.JEqB.id <;> try assumption
    omega
  | abs =>
    apply ECtx.JEqB.abs <;> try assumption
    omega
  | app =>
    apply ECtx.JEqB.app <;> try assumption
    omega
  | pair =>
    apply ECtx.JEqB.pair <;> try assumption
    omega
  | fst =>
    apply ECtx.JEqB.fst <;> try assumption
    omega
  | snd =>
    apply ECtx.JEqB.snd <;> try assumption
    omega
  | natrec =>
    apply ECtx.JEqB.natrec <;> try assumption
    omega
  | refl => apply ECtx.JEqB.refl; assumption
  | absurd =>
    apply ECtx.JEqB.absurd <;> try assumption
    omega
  | beta_app =>
    apply ECtx.JEqB.beta_app <;> try assumption
    omega
  | beta_fst =>
    apply ECtx.JEqB.beta_fst <;> try assumption
    omega
  | beta_snd =>
    apply ECtx.JEqB.beta_snd <;> try assumption
    omega
  | beta_natrec_zero =>
    apply ECtx.JEqB.beta_natrec_zero <;> try assumption
    omega
  | beta_natrec_succ =>
    apply ECtx.JEqB.beta_natrec_succ <;> try assumption
    omega
  | reflect => apply ECtx.JEqB.reflect <;> assumption
  | id_uip => apply ECtx.JEqB.id_uip <;> assumption
  | unit_ext => apply ECtx.JEqB.unit_ext; assumption
  | pi_ext =>
    apply ECtx.JEqB.pi_ext <;> try assumption
    omega
  | sigma_ext =>
    apply ECtx.JEqB.sigma_ext <;> try assumption
    omega
  | symm => apply ECtx.JEqB.symm; assumption
  | trans => apply ECtx.JEqB.trans <;> assumption
  | conv =>
    apply ECtx.JEqB.conv <;> try assumption
    omega
  | cumul =>
    apply ECtx.JEqB.cumul <;> try assumption
    omega


end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedDerivation

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT

open Silmaril.Logic.TypeTheory.ExtensionalMLTT

/-- Compatibility name for bounded-rule erasure. -/
theorem forget {levels : ℕ} {H : Set EJdg} {Γ : ECtx} {A a b : ETm 0}
    (h : ECtx.JEqB levels H Γ A a b) : ECtx.JEqH H Γ A a b :=
  BoundedDerivation.forget h

/-- Compatibility name for budget enlargement and theory substitution. -/
theorem transport {levels more : ℕ} (hlevels : levels ≤ more) {H H' : Set EJdg}
    (hh : ∀ j ∈ H, ECtx.JEqB more H' j.Γ j.A j.a j.b)
    {Γ : ECtx} {A a b : ETm 0} (h : ECtx.JEqB levels H Γ A a b) :
    ECtx.JEqB more H' Γ A a b :=
  BoundedDerivation.transport hlevels hh h

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT
