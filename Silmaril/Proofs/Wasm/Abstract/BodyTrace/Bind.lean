module

public import Silmaril.Wasm.Abstract.BodyTrace.Defs
public import Silmaril.Semantics.ITree.Thms
import Silmaril.Proofs.Wasm.Abstract.BodyTrace.Basic

/-!
# Paths through a bind of interaction trees

A finite path of `t >>= k` is a returning path of `t` followed by a path of
the continuation, or a diverging path of `t`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.BodyTrace

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract.Body
  Silmaril.Wasm.Abstract.BodyTrace Silmaril.Elgot.ITree

universe u

variable {E : Sig.{u}} {A B : Type (u + 1)}

theorem path_bind_inv {t : Tree (SigEv E) A} {k : A → Tree (SigEv E) B} {cs : List (Call E)}
    {r : PathEnd B} (h : Path (t >>= k) cs r) :
    (∃ cs₁ cs₂ a, cs = cs₁ ++ cs₂ ∧ Path t cs₁ (.val a) ∧ Path (k a) cs₂ r) ∨
      (r = .div ∧ Path t cs .div) := by
  generalize hT : t >>= k = T at h
  induction h generalizing t with
  | @ret T b hb =>
    rcases cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R, e, k', rfl⟩
    · rw [diverge_bind] at hT; rw [← hT] at hb; exact absurd hb.symm (ret_ne_diverge _)
    · rw [show (ret a >>= k) = k a from pure_bind a k] at hT
      exact .inl ⟨[], [], a, rfl, .ret rfl, .ret (hT.trans hb)⟩
    · rw [vis_bind] at hT; rw [← hT] at hb; exact absurd hb.symm (ret_ne_vis _ _ _)
  | @div T hd =>
    rcases cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R, e, k', rfl⟩
    · exact .inr ⟨rfl, .div rfl⟩
    · rw [show (ret a >>= k) = k a from pure_bind a k] at hT
      exact .inl ⟨[], [], a, rfl, .ret rfl, .div (hT.trans hd)⟩
    · rw [vis_bind] at hT; rw [← hT] at hd; exact absurd hd (vis_ne_diverge _ _)
  | @vis T R e k'' n cs' r' hv hp ih =>
    rcases cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R', e', k', rfl⟩
    · rw [diverge_bind] at hT; rw [← hT] at hv; exact absurd hv.symm (vis_ne_diverge _ _)
    · rw [show (ret a >>= k) = k a from pure_bind a k] at hT
      exact .inl ⟨[], _, a, rfl, .ret rfl, .vis (hT.trans hv) hp⟩
    · rw [vis_bind] at hT
      rw [← hT] at hv
      obtain ⟨rfl, he, hk⟩ := vis_heq hv
      obtain rfl := eq_of_heq he
      obtain rfl := eq_of_heq hk
      rcases ih (t := k' n) rfl with ⟨cs₁, cs₂, a, rfl, h₁, h₂⟩ | ⟨rfl, h₁⟩
      · exact .inl ⟨_ :: cs₁, cs₂, a, rfl, .vis rfl h₁, h₂⟩
      · exact .inr ⟨rfl, .vis rfl h₁⟩

theorem path_bind_ret {t : Tree (SigEv E) A} {k : A → Tree (SigEv E) B} {cs₁ cs₂ : List (Call E)}
    {a : A} {r : PathEnd B} (h₁ : Path t cs₁ (.val a)) (h₂ : Path (k a) cs₂ r) :
    Path (t >>= k) (cs₁ ++ cs₂) r := by
  generalize ha : (PathEnd.val a : PathEnd A) = ra at h₁
  induction h₁ with
  | ret ht =>
    cases ha
    rw [ht, show (ret _ >>= k) = k _ from pure_bind _ k]
    exact h₂
  | div _ => cases ha
  | vis ht _ ih =>
    rw [ht, vis_bind]
    exact .vis rfl (ih ha)

theorem path_bind_div {t : Tree (SigEv E) A} {k : A → Tree (SigEv E) B} {cs : List (Call E)}
    (h : Path t cs .div) : Path (t >>= k) cs .div := by
  generalize hd : (PathEnd.div : PathEnd A) = rd at h
  induction h with
  | ret _ => cases hd
  | div ht => rw [ht, diverge_bind]; exact .div rfl
  | vis ht _ ih => rw [ht, vis_bind]; exact .vis rfl (ih hd)

variable {S T C : Type (u + 1)}

theorem endOf_eq_trap {r : PathEnd (Except T (B × S))} (h : endOf r = .trap) :
    ∃ e, r = .val (.error e) := by
  rcases r with (e | ⟨b, s⟩) | _ <;> simp_all [endOf]

theorem endOf_eq_div {r : PathEnd (Except T (B × S))} (h : endOf r = .div) : r = .div := by
  rcases r with (e | ⟨b, s⟩) | _ <;> simp_all [endOf]

theorem endOf_eq_ret {r : PathEnd (Except T (B × S))} {b : B} {s : S} (h : endOf r = .ret b s) :
    r = .val (.ok (b, s)) := by
  rcases r with (e | ⟨b', s'⟩) | _ <;> simp_all [endOf]

/-- The continuation of a body bind, at the interaction-tree level. -/
def kont (g : Hom E S T B C) : Except T (B × S) → Tree (SigEv E) (Except T (C × S))
  | .ok (b, s') => ((g b).run s').run
  | .error e => pure (.error e)

theorem run_bind (f : Hom E S T A B) (g : Hom E S T B C) (a : A) (s : S) :
    ((f a >>= g).run s).run = ((f a).run s).run >>= kont g := by
  rw [StateT.run_bind, ExceptT.run_bind]
  congr 1
  funext r
  rcases r with e | ⟨b, s'⟩ <;> rfl

theorem toAFun_comp (f : Hom E S T A B) (g : Hom E S T B C) :
    toAFun (fun a => f a >>= g) = AFun.seq (toAFun f) (toAFun g) := by
  funext s a
  ext x
  constructor
  · rintro ⟨cs, r, hp, rfl⟩
    rw [run_bind] at hp
    rcases path_bind_inv hp with ⟨cs₁, cs₂, a', rfl, h₁, h₂⟩ | ⟨rfl, h₁⟩
    · rcases a' with e | ⟨b, s₁⟩
      · have : cs₂ = [] ∧ r = .val (.error e) := by
          cases h₂ with
          | ret h =>
            have h' : (ret (Except.error e) : Tree (SigEv E) (Except T (C × S))) = ret _ := h
            exact ⟨rfl, by rw [ret_inj.1 h']⟩
          | div h => exact absurd h (ret_ne_diverge _)
          | vis h _ => exact absurd h (ret_ne_vis _ _ _)
        obtain ⟨rfl, rfl⟩ := this
        exact .inl ⟨_, ⟨cs₁, _, h₁, rfl⟩, by simp [endOf]⟩
      · refine .inr (.inr ⟨cs₁.map liftCall, b, s₁, cs₂.map liftCall, endOf r,
          ⟨cs₁, _, h₁, rfl⟩, ⟨cs₂, r, h₂, rfl⟩, by simp⟩)
    · exact .inr (.inl ⟨_, ⟨cs, _, h₁, rfl⟩, rfl⟩)
  · rintro (⟨c, ⟨cs, r, hp, he⟩, rfl⟩ | ⟨c, ⟨cs, r, hp, he⟩, rfl⟩ |
        ⟨c₁, b, s₁, c₂, e, ⟨cs₁, r₁, h₁, he₁⟩, ⟨cs₂, r₂, h₂, he₂⟩, rfl⟩)
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, he⟩ := he
      obtain ⟨t, rfl⟩ := endOf_eq_trap he.symm
      refine ⟨cs ++ [], .val (.error t), ?_, by simp [endOf]⟩
      rw [run_bind]
      exact path_bind_ret hp (.ret rfl)
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, he⟩ := he
      obtain rfl := endOf_eq_div he.symm
      refine ⟨cs, .div, ?_, by simp [endOf]⟩
      rw [run_bind]
      exact path_bind_div hp
    · simp only [Prod.mk.injEq] at he₁ he₂
      obtain ⟨rfl, he₁⟩ := he₁
      obtain ⟨rfl, rfl⟩ := he₂
      obtain rfl := endOf_eq_ret he₁.symm
      refine ⟨cs₁ ++ cs₂, r₂, ?_, by simp⟩
      rw [run_bind]
      exact path_bind_ret h₁ h₂

end Silmaril.Proofs.Wasm.Abstract.BodyTrace
