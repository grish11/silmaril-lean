module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGLink.Link
public import Silmaril.Wasm.Game.Determinism.Thms
public import Silmaril.Games.Abstract.SessionCat.Defs

/-!
# Returns of the importer's triple are deterministic, at `profile o` (proofs)

At the deterministic profiles, the hidden state of the importer's core instance is a function of
the play (`ScalarInstance.Trans.functional`) and Proponent's move from a state is unique
(`ScalarInstance.Trans.player_unique`). A core import call whose arguments do not lift is
answered by a trap without a wired call, the same in both runs; otherwise both runs make the same
wired call, and equal wired answers give equal core answers (`impRel_agree`). So two returning
rounds at the same store and question agree as long as their wired answers agree
(`agree_core`, `retDet_impTripleS`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGLink

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game (ScalarInstance Answer)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)
open Silmaril.Wasm.Execution.Core (Store)

variable {I : ScalarInstance} {o : GrowOracle} {b : SimpleI} {wire : List Nat}

theorem pmove_eq {q q₁ q₂ : I.HState} {m m' : Move I.E I.F}
    (h₁ : I.Trans (profile o) q m q₁) (h₂ : I.Trans (profile o) q m' q₂) (hm : m.IsP) :
    m = m' ∧ q₁ = q₂ := by
  have := ScalarInstance.Trans.player_unique h₁ h₂ hm
  subst this
  exact ⟨rfl, ScalarInstance.Trans.functional h₁ h₂⟩

theorem agree_cons {E : Sig.{0}} {S B : Type} {m m' : E.Op} {n : E.Ar m} {n' : E.Ar m'}
    {c c' : List (Call E)} {e e' : End S B} (h₁ : m = m') (h₂ : HEq n n' → AFun.Agree c e c' e') :
    AFun.Agree (⟨m, n⟩ :: c) e (⟨m', n'⟩ :: c') e' := by
  simp only [AFun.Agree]
  exact ⟨h₁, h₂⟩

/-- **One core import call, twice**: no wired call and a trap in both, or the same wired call
in both, equal wired answers giving equal core answers. -/
theorem impRel_agree {m : I.E.Op} {n n' : I.E.Ar m} {ds ds' : List b.ICall}
    (h : ImpRel b I ⟨m, n⟩ ds) (h' : ImpRel b I ⟨m, n'⟩ ds') :
    (ds = [] ∧ ds' = [] ∧ n = Answer.trap ∧ n' = Answer.trap) ∨
      ∃ z z', ds = [z] ∧ ds' = [z'] ∧ z.1 = z'.1 ∧ (z.2 = z'.2 → n = n') := by
  obtain ⟨nm, ft, A, h₁, h₂, h₃⟩ := h
  obtain ⟨nm', ft', A', h₁', h₂', h₃'⟩ := h'
  rw [h₁] at h₁'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h₁')
  split at h₃
  · rename_i hl
    split at h₃'
    · obtain ⟨rfl, rfl⟩ := h₃
      obtain ⟨rfl, rfl⟩ := h₃'
      exact .inl ⟨rfl, rfl, h₂.symm, h₂'.symm⟩
    · rename_i hl'
      rw [hl] at hl'
      cases hl'
  · rename_i ws hl
    split at h₃'
    · rename_i hl'
      rw [hl] at hl'
      cases hl'
    · rename_i ws' hl'
      rw [hl] at hl'
      cases hl'
      obtain ⟨hk, R, rfl, rfl⟩ := h₃
      obtain ⟨hk', R', rfl, rfl⟩ := h₃'
      refine .inr ⟨_, _, rfl, rfl, rfl, fun hR => ?_⟩
      simp only at hR
      subst hR
      exact h₂.symm.trans h₂'

/-- **Two returning rounds from the same state agree** while their wired answers agree. -/
theorem agree_core {j : Fin b.exports.length} {f : I.F.Op}
    {cs : List (Σ e : I.E.Op, I.E.Ar e)} {dss : List (List b.ICall)}
    (hr : List.Forall₂ (ImpRel b I) cs dss) :
    ∀ {x : I.HState} {cs' : List (Σ e : I.E.Op, I.E.Ar e)} {dss' : List (List b.ICall)}
      {w w' : I.F.Ar f} {u₁ u₁' : Store Nat}, List.Forall₂ (ImpRel b I) cs' dss' →
      I.Path (profile o) x (callMoves cs ++ [.inr (.ans f w)]) (.idle u₁) →
      I.Path (profile o) x (callMoves cs' ++ [.inr (.ans f w')]) (.idle u₁') →
      AFun.Agree (b.wireLog wire dss.flatten) (End.ret (ExpSpec.sumAns (b.liftAns j w)) u₁)
        (b.wireLog wire dss'.flatten) (End.ret (ExpSpec.sumAns (b.liftAns j w')) u₁') := by
  induction hr with
  | nil =>
    intro x cs' dss' w w' u₁ u₁' hr' h h'
    cases hr' with
    | nil =>
      cases h with
      | cons t₁ h =>
        cases h' with
        | cons t₁' h' =>
          obtain ⟨hm, rfl⟩ := pmove_eq t₁ t₁' trivial
          simp only [Sum.inr.injEq, Ev.ans.injEq, heq_eq_eq, true_and] at hm
          subst hm
          cases h
          cases h'
          rfl
    | @cons c' ds' cs' dss' hx' hr' =>
      exfalso
      obtain ⟨m', n'⟩ := c'
      simp only [callMoves, List.cons_append] at h'
      cases h with
      | cons t₁ _ =>
        cases h' with
        | cons t₁' _ =>
          have := (pmove_eq t₁ t₁' trivial).1
          simp at this
  | @cons c ds cs dss hx hr ih =>
    intro x cs' dss' w w' u₁ u₁' hr' h h'
    obtain ⟨m, n⟩ := c
    simp only [callMoves, List.cons_append] at h
    cases hr' with
    | nil =>
      exfalso
      cases h with
      | cons t₁ _ =>
        cases h' with
        | cons t₁' _ =>
          have := (pmove_eq t₁ t₁' trivial).1
          simp at this
    | @cons c' ds' cs' dss' hx' hr' =>
      obtain ⟨m', n'⟩ := c'
      simp only [callMoves, List.cons_append] at h'
      cases h with
      | cons t₁ h =>
        cases h with
        | cons t₂ h =>
          cases h' with
          | cons t₁' h' =>
            cases h' with
            | cons t₂' h' =>
              obtain ⟨hm, rfl⟩ := pmove_eq t₁ t₁' trivial
              simp only [Sum.inl.injEq, Ev.ask.injEq] at hm
              subst hm
              rcases impRel_agree hx hx' with ⟨rfl, rfl, rfl, rfl⟩ | ⟨z, z', rfl, rfl, hzq, hzn⟩
              · have := ScalarInstance.Trans.functional t₂ t₂'
                subst this
                show AFun.Agree (b.wireLog wire dss.flatten) _ (b.wireLog wire dss'.flatten) _
                exact ih hr' h h'
              · show AFun.Agree (b.wireCall wire z :: b.wireLog wire dss.flatten) _
                  (b.wireCall wire z' :: b.wireLog wire dss'.flatten) _
                refine agree_cons (by simp [hzq]) (fun hn => ?_)
                have hR : z.2 = z'.2 := sumAns_inj (eq_of_heq hn)
                have := hzn hR
                subst this
                have := ScalarInstance.Trans.functional t₂ t₂'
                subst this
                exact ih hr' h h'

theorem op_ext {f f' : I.F.Op} (h₁ : f.1.val = f'.1.val) (h₂ : f.2.1 = f'.2.1) : f = f' := by
  obtain ⟨⟨i, hi⟩, ⟨a, ha⟩⟩ := f
  obtain ⟨⟨i', hi'⟩, ⟨a', ha'⟩⟩ := f'
  simp only at h₁ h₂
  subst h₁ h₂
  rfl

/-- **Returns of the importer's triple are deterministic** (`profile o`). -/
theorem retDet_impTripleS : SessionCat.RetDet (b.impTripleS (profile o) wire I) := by
  intro u q c c' bb bb' s₁ s₁' h h'
  rcases h with ⟨hnt, h⟩ | ⟨j, vs, f, cs, dss, rfl, hlow, hlog, hd⟩
  · rcases h' with ⟨-, h'⟩ | ⟨j', vs', f', cs', dss', hq', hlow', -, -⟩
    · simp only [Prod.mk.injEq] at h h'
      obtain ⟨rfl, he⟩ := h
      obtain ⟨rfl, he'⟩ := h'
      show End.ret bb s₁ = End.ret bb' s₁'
      rw [he, he']
    · exact (hnt (hq' ▸ typedQ_of_lowered hlow')).elim
  · rcases h' with ⟨hnt', -⟩ | ⟨j', vs', f', cs', dss', hq', hlow', hlog', hd'⟩
    · exact (hnt' (typedQ_of_lowered hlow)).elim
    simp only [Prod.mk.injEq, Payload.vals.injEq] at hq'
    obtain ⟨hj, rfl⟩ := hq'
    obtain rfl : j = j' := Fin.ext hj
    have hf : f = f' := by
      obtain ⟨xs, hc, hf1, hf2, -⟩ := hlow
      obtain ⟨xs', hc', hf1', hf2', -⟩ := hlow'
      rw [hc] at hc'
      cases hc'
      exact op_ext (hf1.trans hf1'.symm) (hf2.trans hf2'.symm)
    subst hf
    simp only at hlog hlog'
    subst hlog hlog'
    rcases hd with ⟨w, u₁, hp, he⟩ | ⟨-, -, -, -, he⟩
    · rcases hd' with ⟨w', u₁', hp', he'⟩ | ⟨-, -, -, -, he'⟩
      · simp only [End.ret.injEq] at he he'
        obtain ⟨rfl, rfl⟩ := he
        obtain ⟨rfl, rfl⟩ := he'
        rw [List.cons_append] at hp hp'
        cases hp with
        | cons t h =>
          cases t
          cases hp' with
          | cons t' h' =>
            cases t'
            exact agree_core (lowered_forall₂ hlow) (lowered_forall₂ hlow') h h'
      · simp at he'
    · simp at he

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGLink
