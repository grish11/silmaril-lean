module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Derivation.Defs

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

/-- Substitute derivations for hypothesis leaves. -/
theorem ECtx.JEqH.bind {H H' : Set EJdg}
    (hh : ∀ j ∈ H, ECtx.JEqH H' j.Γ j.A j.a j.b)
    {Γ : ECtx} {A a b : ETm 0} (h : ECtx.JEqH H Γ A a b) :
    ECtx.JEqH H' Γ A a b := by
  induction h with
  | hyp hj => exact hh _ hj
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

/-- Increasing the theory preserves derivability. -/
theorem ECtx.JEqH.mono {H H' : Set EJdg} (hh : H ⊆ H')
    {Γ : ECtx} {A a b : ETm 0} (h : ECtx.JEqH H Γ A a b) :
    ECtx.JEqH H' Γ A a b :=
  h.bind fun _ hj => .hyp (hh hj)

/-- Every original closed-theory derivation is available under any theory. -/
theorem ECtx.JEq.toJEqH {H : Set EJdg}
    {Γ : ECtx} {A a b : ETm 0} (h : ECtx.JEq Γ A a b) :
    ECtx.JEqH H Γ A a b := by
  induction h with
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

/-- No additional judgments are derived from the empty theory. -/
theorem ECtx.JEqH.of_empty {Γ : ECtx} {A a b : ETm 0}
    (h : ECtx.JEqH ∅ Γ A a b) : ECtx.JEq Γ A a b := by
  induction h with
  | hyp hj => exact (Set.notMem_empty _ hj).elim
  | nil_ok => exact ECtx.JEq.nil_ok
  | cons_ok => apply ECtx.JEq.cons_ok <;> assumption
  | var => apply ECtx.JEq.var <;> assumption
  | univ => apply ECtx.JEq.univ; assumption
  | empty => apply ECtx.JEq.empty; assumption
  | unit => apply ECtx.JEq.unit; assumption
  | nats => apply ECtx.JEq.nats; assumption
  | zero => apply ECtx.JEq.zero; assumption
  | succ => apply ECtx.JEq.succ; assumption
  | pi => apply ECtx.JEq.pi <;> assumption
  | sigma => apply ECtx.JEq.sigma <;> assumption
  | id => apply ECtx.JEq.id <;> assumption
  | abs => apply ECtx.JEq.abs <;> assumption
  | app => apply ECtx.JEq.app <;> assumption
  | pair => apply ECtx.JEq.pair <;> assumption
  | fst => apply ECtx.JEq.fst <;> assumption
  | snd => apply ECtx.JEq.snd <;> assumption
  | natrec => apply ECtx.JEq.natrec <;> assumption
  | refl => apply ECtx.JEq.refl; assumption
  | absurd => apply ECtx.JEq.absurd <;> assumption
  | beta_app => apply ECtx.JEq.beta_app <;> assumption
  | beta_fst => apply ECtx.JEq.beta_fst <;> assumption
  | beta_snd => apply ECtx.JEq.beta_snd <;> assumption
  | beta_natrec_zero => apply ECtx.JEq.beta_natrec_zero <;> assumption
  | beta_natrec_succ => apply ECtx.JEq.beta_natrec_succ <;> assumption
  | reflect => apply ECtx.JEq.reflect <;> assumption
  | id_uip => apply ECtx.JEq.id_uip <;> assumption
  | unit_ext => apply ECtx.JEq.unit_ext; assumption
  | pi_ext => apply ECtx.JEq.pi_ext <;> assumption
  | sigma_ext => apply ECtx.JEq.sigma_ext <;> assumption
  | symm => apply ECtx.JEq.symm; assumption
  | trans => apply ECtx.JEq.trans <;> assumption
  | conv => apply ECtx.JEq.conv <;> assumption
  | cumul => apply ECtx.JEq.cumul <;> assumption

theorem ECtx.JEqH.empty_iff {Γ : ECtx} {A a b : ETm 0} :
    ECtx.JEqH ∅ Γ A a b ↔ ECtx.JEq Γ A a b :=
  ⟨ECtx.JEqH.of_empty, ECtx.JEq.toJEqH⟩

end Silmaril.Logic.TypeTheory.ExtensionalMLTT
