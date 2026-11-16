module

public import Silmaril.Wasm.Abstract.BodyTrace.Defs
public import Silmaril.Semantics.ITree.Thms
public import Silmaril.Proofs.Wasm.Abstract.BodyTrace.Basic
public import Silmaril.Proofs.Wasm.Abstract.BodyTrace.Bind
public import Silmaril.Proofs.Wasm.Abstract.BodyTrace.Iter
public import Silmaril.Proofs.Wasm.Abstract.BodyTrace.Collapse

/-!
# Finished paths and pending calls determine an interaction tree

Two weak interaction trees with the same finished paths (`Path`) and the same
pending calls (`Pend`) are equal: by induction on the observation depth, the
root is fixed by the empty path or the first pending call, and each child by
the observations that start with its answer. No assumption on answer types is
needed, because a pending call is seen before it is answered.

For bodies this makes `toAFun` together with `toPending` a faithful
observation of bodies up to trap payloads (`erasedRun`), and their
trap ≈ divergence version a faithful observation of `collapse`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.BodyTrace

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract.Body
  Silmaril.Wasm.Abstract.BodyTrace Silmaril.Elgot.ITree

universe u

variable {E : Sig.{u}} {Y : Type (u + 1)}

/-! ## Calls and events -/

theorem call_answer_inj {m : E.Op} {R : Type u} (h : E.Ar m = R) {n n' : R}
    (hc : (⟨m, cast h.symm n⟩ : Call E) = ⟨m, cast h.symm n'⟩) : n = n' := by
  have := congrArg (cast h) (eq_of_heq (Sigma.mk.inj_iff.1 hc).2)
  simpa using this

theorem path_vis_cons {R : Type u} {e : SigEv E R} {k : R → Tree (SigEv E) Y} {r : R}
    {cs : List (Call E)} {x : PathEnd Y} :
    Path (vis e k) (⟨e.1, cast e.2.symm r⟩ :: cs) x ↔ Path (k r) cs x := by
  refine ⟨fun h => ?_, fun h => .vis rfl h⟩
  obtain ⟨n, cs', hc, hp⟩ := path_vis_inv h
  simp only [List.cons.injEq] at hc
  obtain ⟨hc, rfl⟩ := hc
  obtain rfl := call_answer_inj e.2 hc
  exact hp

theorem pend_vis_inv {R : Type u} {e : SigEv E R} {k : R → Tree (SigEv E) Y}
    {cs : List (Call E)} {m : E.Op} (h : Pend (vis e k) cs m) :
    (cs = [] ∧ m = e.1) ∨ ∃ n cs', cs = ⟨e.1, cast e.2.symm n⟩ :: cs' ∧ Pend (k n) cs' m := by
  cases h with
  | here h =>
    obtain ⟨rfl, he, -⟩ := vis_heq h
    obtain rfl := eq_of_heq he
    exact .inl ⟨rfl, rfl⟩
  | vis h hp =>
    obtain ⟨rfl, he, hk⟩ := vis_heq h
    obtain rfl := eq_of_heq he
    obtain rfl := eq_of_heq hk
    exact .inr ⟨_, _, rfl, hp⟩

theorem pend_vis_cons {R : Type u} {e : SigEv E R} {k : R → Tree (SigEv E) Y} {r : R}
    {cs : List (Call E)} {m : E.Op} :
    Pend (vis e k) (⟨e.1, cast e.2.symm r⟩ :: cs) m ↔ Pend (k r) cs m := by
  refine ⟨fun h => ?_, fun h => .vis rfl h⟩
  rcases pend_vis_inv h with ⟨h, -⟩ | ⟨n, cs', hc, hp⟩
  · cases h
  · simp only [List.cons.injEq] at hc
    obtain ⟨hc, rfl⟩ := hc
    obtain rfl := call_answer_inj e.2 hc
    exact hp

theorem not_pend_ret {v : Y} {cs : List (Call E)} {m : E.Op} : ¬ Pend (ret v) cs m := by
  intro h
  cases h with
  | here h => exact ret_ne_vis _ _ _ h
  | vis h _ => exact ret_ne_vis _ _ _ h

theorem not_pend_diverge {cs : List (Call E)} {m : E.Op} :
    ¬ Pend (diverge : Tree (SigEv E) Y) cs m := by
  intro h
  cases h with
  | here h => exact vis_ne_diverge _ _ h.symm
  | vis h _ => exact vis_ne_diverge _ _ h.symm

theorem path_nil_div {t : Tree (SigEv E) Y} (h : Path t [] .div) : t = diverge := by
  cases h with
  | div h => exact h

/-! ## Determination -/

/-- The same finished paths and the same pending calls. -/
def SameObs (t t' : Tree (SigEv E) Y) : Prop :=
  (∀ cs r, Path t cs r ↔ Path t' cs r) ∧ ∀ cs m, Pend t cs m ↔ Pend t' cs m

theorem observe_eq_of_sameObs :
    ∀ (n : Nat) (t t' : Tree (SigEv E) Y), SameObs t t' → t.observe n = t'.observe n
  | 0, _, _, _ => rfl
  | n + 1, t, t', h => by
    rw [observe_succ_eq_out, observe_succ_eq_out]
    rcases cases_visible t with rfl | ⟨v, rfl⟩ | ⟨R, ⟨m, hm⟩, k, rfl⟩
    · rw [path_nil_div ((h.1 [] .div).1 (.div rfl))]
    · rw [path_nil_val ((h.1 [] (.val v)).1 (.ret rfl))]
    · subst hm
      have hp := (h.2 [] m).1 (.here rfl)
      rcases cases_visible t' with rfl | ⟨v, rfl⟩ | ⟨R', ⟨m', hm'⟩, k', rfl⟩
      · exact absurd hp not_pend_diverge
      · exact absurd hp not_pend_ret
      · subst hm'
        rcases pend_vis_inv hp with ⟨-, hmm⟩ | ⟨_, _, hc, -⟩
        · change m = m' at hmm
          subst hmm
          have hk : ∀ r, (k r).observe n = (k' r).observe n := fun r =>
            observe_eq_of_sameObs n (k r) (k' r)
              ⟨fun cs x => by
                rw [← path_vis_cons (e := ⟨m, rfl⟩) (k := k) (r := r),
                  ← path_vis_cons (e := ⟨m, rfl⟩) (k := k') (r := r)]
                exact h.1 _ _,
               fun cs x => by
                rw [← pend_vis_cons (e := ⟨m, rfl⟩) (k := k) (r := r),
                  ← pend_vis_cons (e := ⟨m, rfl⟩) (k := k') (r := r)]
                exact h.2 _ _⟩
          rw [out_vis (E := SigEv E) (R := E.Ar m) ⟨m, rfl⟩ k,
            out_vis (E := SigEv E) (R := E.Ar m) ⟨m, rfl⟩ k']
          change Part.map _ (Part.some _) = Part.map _ (Part.some _)
          rw [Part.map_some, Part.map_some]
          change Part.some (Visible.vis _ fun r => (k r).observe n) =
            Part.some (Visible.vis _ fun r => (k' r).observe n)
          rw [funext hk]
        · cases hc

theorem eq_of_sameObs {t t' : Tree (SigEv E) Y} (h : SameObs t t') : t = t' :=
  Tree.ext fun n => observe_eq_of_sameObs n t t' h

/-! ## Pending calls through a bind -/

theorem pend_bind_iff {Z : Type (u + 1)} {t : Tree (SigEv E) Z} {k : Z → Tree (SigEv E) Y}
    (hk : ∀ v cs m, ¬ Pend (k v) cs m) {cs : List (Call E)} {m : E.Op} :
    Pend (t >>= k) cs m ↔ Pend t cs m := by
  constructor
  · intro h
    generalize hT : t >>= k = T at h
    induction h generalizing t with
    | @here T R e k'' hv =>
      rcases cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R', e', k', rfl⟩
      · rw [diverge_bind] at hT; rw [← hT] at hv; exact absurd hv.symm (vis_ne_diverge _ _)
      · rw [show (ret a >>= k) = k a from pure_bind a k] at hT
        exact absurd (Pend.here (hT.trans hv)) (hk a _ _)
      · rw [vis_bind] at hT
        rw [← hT] at hv
        obtain ⟨rfl, he, -⟩ := vis_heq hv
        obtain rfl := eq_of_heq he
        exact .here rfl
    | @vis T R e k'' n cs' m' hv hp ih =>
      rcases cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R', e', k', rfl⟩
      · rw [diverge_bind] at hT; rw [← hT] at hv; exact absurd hv.symm (vis_ne_diverge _ _)
      · rw [show (ret a >>= k) = k a from pure_bind a k] at hT
        exact absurd (Pend.vis (hT.trans hv) hp) (hk a _ _)
      · rw [vis_bind] at hT
        rw [← hT] at hv
        obtain ⟨rfl, he, hk'⟩ := vis_heq hv
        obtain rfl := eq_of_heq he
        obtain rfl := eq_of_heq hk'
        exact .vis rfl (ih rfl)
  · intro h
    induction h with
    | here ht => rw [ht, vis_bind]; exact .here rfl
    | vis ht _ ih => rw [ht, vis_bind]; exact .vis rfl ih

/-! ## Bodies -/

variable {S T A B : Type (u + 1)}

theorem liftCall_injective : Function.Injective (liftCall (E := E)) := by
  rintro ⟨m, n⟩ ⟨m', n'⟩ h
  obtain ⟨h₁, h₂⟩ := Sigma.mk.inj_iff.1 h
  obtain rfl : m = m' := congrArg ULift.down h₁
  have := congrArg ULift.down (eq_of_heq h₂)
  simp only at this
  subst this
  rfl

theorem endOf_erase_injective {r r' : PathEnd (Except PUnit.{u + 2} (B × S))}
    (h : endOf r = endOf r') : r = r' := by
  rcases r with (⟨⟩ | ⟨b, s⟩) | _ <;> rcases r' with (⟨⟩ | ⟨b', s'⟩) | _ <;>
    simp_all [endOf]

theorem cendOf_injective {r r' : PathEnd (B × S)} (h : cendOf r = cendOf r') : r = r' := by
  rcases r with ⟨b, s⟩ | _ <;> rcases r' with ⟨b', s'⟩ | _ <;> simp_all [cendOf]

theorem endOf_mapEnd_erase (r : PathEnd (Except T (B × S))) :
    endOf (mapEnd eraseTrap r) = endOf r := by
  rcases r with (e | ⟨b, s⟩) | _ <;> rfl

theorem toAFun_eq_erased (f : Hom E S T A B) (s : S) (a : A) :
    toAFun f s a = {x | ∃ cs r, Path (erasedRun f s a) cs r ∧ x = (cs.map liftCall, endOf r)} := by
  ext x
  constructor
  · rintro ⟨cs, r, hp, rfl⟩
    exact ⟨cs, _, path_map hp, by rw [endOf_mapEnd_erase]⟩
  · rintro ⟨cs, r, hp, rfl⟩
    obtain ⟨r', hp', rfl⟩ := path_map_inv hp
    exact ⟨cs, r', hp', by rw [endOf_mapEnd_erase]⟩

theorem not_pend_pure {Z : Type (u + 1)} (z : Z) {cs : List (Call E)} {m : E.Op} :
    ¬ Pend (pure z : Tree (SigEv E) Z) cs m := not_pend_ret

theorem toPending_eq_erased (f : Hom E S T A B) (s : S) (a : A) :
    toPending f s a =
      {x | ∃ cs m, Pend (erasedRun f s a) cs m ∧ x = (cs.map liftCall, ULift.up m)} := by
  ext x
  simp only [toPending, erasedRun, Set.mem_ofPred_eq,
    pend_bind_iff (fun v _ _ => not_pend_pure (eraseTrap v))]
  exact Iff.rfl

theorem toPending_eq_collapse (f : Hom E S T A B) (s : S) (a : A) :
    toPending f s a =
      {x | ∃ cs m, Pend (collapse (f a) s) cs m ∧ x = (cs.map liftCall, ULift.up m)} := by
  have hk : ∀ (v : Except T (B × S)) cs m, ¬ Pend (trapDiverge (E := E) v) cs m := by
    rintro (e | p) cs m
    · exact not_pend_diverge
    · exact not_pend_pure p
  ext x
  simp only [toPending, collapse_eq_bind, Set.mem_ofPred_eq, pend_bind_iff hk]
  exact Iff.rfl

/-- Equal images of an injective reading determine the predicate. -/
theorem pred_iff_of_image_eq.{v, w, x} {α : Type v} {β : Type w} {γ : Type x} {P Q : α → β → Prop} {F : α → β → γ}
    (hF : ∀ a b a' b', F a b = F a' b' → a = a' ∧ b = b')
    (h : {x | ∃ a b, P a b ∧ x = F a b} = {x | ∃ a b, Q a b ∧ x = F a b}) (a : α) (b : β) :
    P a b ↔ Q a b := by
  constructor
  · intro hp
    obtain ⟨a', b', hq, he⟩ := (h ▸ (⟨a, b, hp, rfl⟩ : F a b ∈ {x | ∃ a b, P a b ∧ x = F a b}) :
      F a b ∈ {x | ∃ a b, Q a b ∧ x = F a b})
    obtain ⟨rfl, rfl⟩ := hF _ _ _ _ he
    exact hq
  · intro hq
    obtain ⟨a', b', hp, he⟩ := (h.symm ▸ (⟨a, b, hq, rfl⟩ : F a b ∈ {x | ∃ a b, Q a b ∧ x = F a b}) :
      F a b ∈ {x | ∃ a b, P a b ∧ x = F a b})
    obtain ⟨rfl, rfl⟩ := hF _ _ _ _ he
    exact hp

theorem faithful_iff (f g : Hom E S T A B) :
    (toAFun f = toAFun g ∧ toPending f = toPending g) ↔ erasedRun f = erasedRun g := by
  constructor
  · rintro ⟨h₁, h₂⟩
    funext s a
    have e₁ := congrFun (congrFun h₁ s) a
    have e₂ := congrFun (congrFun h₂ s) a
    rw [toAFun_eq_erased, toAFun_eq_erased] at e₁
    rw [toPending_eq_erased, toPending_eq_erased] at e₂
    refine eq_of_sameObs ⟨fun cs r => pred_iff_of_image_eq ?_ e₁ cs r,
      fun cs m => pred_iff_of_image_eq ?_ e₂ cs m⟩
    · intro c r c' r' he
      simp only [Prod.mk.injEq] at he
      exact ⟨(List.map_injective_iff.2 liftCall_injective) he.1, endOf_erase_injective he.2⟩
    · intro c m c' m' he
      simp only [Prod.mk.injEq, ULift.up.injEq] at he
      exact ⟨(List.map_injective_iff.2 liftCall_injective) he.1, he.2⟩
  · intro h
    refine ⟨funext fun s => funext fun a => ?_, funext fun s => funext fun a => ?_⟩
    · rw [toAFun_eq_erased, toAFun_eq_erased, h]
    · rw [toPending_eq_erased, toPending_eq_erased, h]

theorem collapse_faithful_iff (f g : Hom E S T A B) :
    (AFun.ObsEquiv AFun.obsCollapse (toAFun f) (toAFun g) ∧ toPending f = toPending g) ↔
      ∀ a, collapse (f a) = collapse (g a) := by
  constructor
  · rintro ⟨h₁, h₂⟩ a
    funext s
    have e₁ := h₁ s a
    have e₂ := congrFun (congrFun h₂ s) a
    rw [obsCollapse_toAFun, obsCollapse_toAFun] at e₁
    rw [toPending_eq_collapse, toPending_eq_collapse] at e₂
    refine eq_of_sameObs ⟨fun cs r => pred_iff_of_image_eq ?_ e₁ cs r,
      fun cs m => pred_iff_of_image_eq ?_ e₂ cs m⟩
    · intro c r c' r' he
      simp only [Prod.mk.injEq] at he
      exact ⟨(List.map_injective_iff.2 liftCall_injective) he.1, cendOf_injective he.2⟩
    · intro c m c' m' he
      simp only [Prod.mk.injEq, ULift.up.injEq] at he
      exact ⟨(List.map_injective_iff.2 liftCall_injective) he.1, he.2⟩
  · intro h
    refine ⟨fun s a => ?_, funext fun s => funext fun a => ?_⟩
    · rw [obsCollapse_toAFun, obsCollapse_toAFun, h a]
    · rw [toPending_eq_collapse, toPending_eq_collapse, h a]

end Silmaril.Proofs.Wasm.Abstract.BodyTrace
