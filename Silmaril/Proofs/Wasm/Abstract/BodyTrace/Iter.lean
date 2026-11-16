module

public import Silmaril.Wasm.Abstract.BodyTrace.Defs
public import Silmaril.Games.Abstract.FunctionIter.Defs
public import Silmaril.Semantics.ITree.Thms
import Silmaril.Proofs.Wasm.Abstract.BodyTrace.Basic
import Silmaril.Proofs.Wasm.Abstract.BodyTrace.Bind

/-!
# Paths through an iterated interaction tree

A finite path of `iter G x` is, up to a finite number of continuing
iterations, an exit or a divergence of one iteration, or an infinite chain of
iterations that each continue silently (`IterPath`). The last case is real:
such a chain makes `iter G x` diverge although no iteration diverges
(`iter_eq_diverge`, from uniformity). Conversely, a returning or visible
iterate has a finite chain of silent continuations before its first visible
layer; that is a classical case split, not a productivity assumption.

With the bind lemmas this gives `toAFun (iter F) = AFun.iter (toAFun F)`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.BodyTrace

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract.Body
  Silmaril.Wasm.Abstract.BodyTrace Silmaril.Elgot.ITree

universe u

variable {E : Sig.{u}}

/-! ## Paths of returns -/

theorem path_ret_inv {Y : Type (u + 1)} {t : Tree (SigEv E) Y} {v : Y} {cs : List (Call E)}
    {r : PathEnd Y} (ht : t = ret v) (h : Path t cs r) : cs = [] ∧ r = .val v := by
  cases h with
  | ret h => rw [ht] at h; rw [ret_inj.1 h]; exact ⟨rfl, rfl⟩
  | div h => rw [ht] at h; exact absurd h (ret_ne_diverge _)
  | vis h _ => rw [ht] at h; exact absurd h (ret_ne_vis _ _ _)

theorem path_nil_val {Y : Type (u + 1)} {t : Tree (SigEv E) Y} {v : Y}
    (h : Path t [] (.val v)) : t = ret v := by
  cases h with
  | ret h => exact h

theorem path_diverge_inv {Y : Type (u + 1)} {cs : List (Call E)} {r : PathEnd Y}
    (h : Path (diverge : Tree (SigEv E) Y) cs r) : cs = [] ∧ r = .div := by
  cases h with
  | ret h => exact absurd h.symm (ret_ne_diverge _)
  | div _ => exact ⟨rfl, rfl⟩
  | vis h _ => exact absurd h.symm (vis_ne_diverge _ _)

theorem path_vis_inv {Y : Type (u + 1)} {R : Type u} {e : SigEv E R}
    {k : R → Tree (SigEv E) Y} {cs : List (Call E)} {r : PathEnd Y} (h : Path (vis e k) cs r) :
    ∃ n cs', cs = ⟨e.1, cast e.2.symm n⟩ :: cs' ∧ Path (k n) cs' r := by
  cases h with
  | ret h => exact absurd h.symm (ret_ne_vis _ _ _)
  | div h => exact absurd h (vis_ne_diverge _ _)
  | vis h hp =>
    obtain ⟨rfl, he, hk⟩ := vis_heq h
    obtain rfl := eq_of_heq he
    obtain rfl := eq_of_heq hk
    exact ⟨_, _, rfl, hp⟩

/-! ## Iterated trees -/

variable {X Y : Type (u + 1)}

/-- The finite paths of an iterated tree, constructor by constructor. -/
inductive IterPath (G : X → Tree (SigEv E) (Y ⊕ X)) : X → List (Call E) → PathEnd Y → Prop
  | exit {x cs y} : Path (G x) cs (.val (.inl y)) → IterPath G x cs (.val y)
  | div {x cs} : Path (G x) cs .div → IterPath G x cs .div
  | step {x cs₁ x' cs₂ r} : Path (G x) cs₁ (.val (.inr x')) → IterPath G x' cs₂ r →
      IterPath G x (cs₁ ++ cs₂) r
  | spin {x} (σ : Nat → X) : σ 0 = x → (∀ n, G (σ n) = ret (.inr (σ (n + 1)))) →
      IterPath G x [] .div

/-- Iteration of interaction trees, at a fixed universe. -/
noncomputable abbrev iterT (G : X → Tree (SigEv E) (Y ⊕ X)) : X → Tree (SigEv E) Y :=
  Silmaril.Elgot.iter G

theorem iter_unfold (G : X → Tree (SigEv E) (Y ⊕ X)) (x : X) :
    iterT G x = G x >>= Sum.elim pure (iterT G) :=
  congrFun (Silmaril.Elgot.LawfulElgotMonad.fixpoint G) x

/-- An infinite chain of silent continuations diverges. -/
theorem iter_eq_diverge (G : X → Tree (SigEv E) (Y ⊕ X)) (σ : Nat → X)
    (hσ : ∀ n, G (σ n) = ret (.inr (σ (n + 1)))) : iterT G (σ 0) = diverge := by
  let f : ULift.{u + 1} Nat → Tree (SigEv E) (Y ⊕ ULift.{u + 1} Nat) :=
    fun n => pure (.inr ⟨n.down + 1⟩)
  have comm : (f >=> Silmaril.Elgot.liftPure (Sum.map id fun n => σ n.down)) =
      (Silmaril.Elgot.liftPure (fun n : ULift.{u + 1} Nat => σ n.down) >=> G) := by
    funext n
    simp only [Bind.kleisliRight, Silmaril.Elgot.liftPure, Function.comp, f, pure_bind,
      Sum.map_inr]
    exact (hσ n.down).symm
  have hu := congrFun (Silmaril.Elgot.LawfulElgotMonad.uniformity f G _ comm) ⟨0⟩
  simp only [Bind.kleisliRight, Silmaril.Elgot.liftPure, Function.comp, pure_bind] at hu
  change Silmaril.Elgot.iter G (σ 0) = _
  rw [← hu]
  exact iterate_pure_loop (fun n : ULift.{u + 1} Nat => (⟨n.down + 1⟩ : ULift Nat)) _

theorem iterPath_path {G : X → Tree (SigEv E) (Y ⊕ X)} {x : X} {cs : List (Call E)}
    {r : PathEnd Y} (h : IterPath G x cs r) : Path (iterT G x) cs r := by
  induction h with
  | exit hp =>
    rw [iter_unfold]
    simpa using (path_bind_ret (k := Sum.elim pure (iterT G)) (cs₂ := []) hp
      (Path.ret rfl))
  | div hp => rw [iter_unfold]; exact path_bind_div hp
  | step hp _ ih => rw [iter_unfold]; exact path_bind_ret hp ih
  | spin σ h0 hσ => rw [← h0, iter_eq_diverge G σ hσ]; exact .div rfl

/-- One iteration returns `inr` at once. -/
def IterSilent (G : X → Tree (SigEv E) (Y ⊕ X)) (x : X) : Prop := ∃ x', G x = ret (.inr x')

open Classical in
/-- The next state of a silent iteration (any state otherwise). -/
noncomputable def iterNext (G : X → Tree (SigEv E) (Y ⊕ X)) (x : X) : X :=
  if h : IterSilent G x then Classical.choose h else x

theorem iterNext_spec {G : X → Tree (SigEv E) (Y ⊕ X)} {x : X} (h : IterSilent G x) :
    G x = ret (.inr (iterNext G x)) := by
  rw [iterNext, dite_eq_left_of_eq_true (eq_true h)]; exact Classical.choose_spec h

theorem path_iterPath_base {G : X → Tree (SigEv E) (Y ⊕ X)} (L : Nat)
    (ih : ∀ (x : X) (cs : List (Call E)) (r : PathEnd Y), cs.length < L →
      Path (iterT G x) cs r → IterPath G x cs r)
    {x : X} {cs : List (Call E)} {r : PathEnd Y} (hL : cs.length = L) (hs : ¬ IterSilent G x)
    (hp : Path (iterT G x) cs r) : IterPath G x cs r := by
  rw [iter_unfold] at hp
  rcases path_bind_inv hp with ⟨cs₁, cs₂, v, rfl, h₁, h₂⟩ | ⟨rfl, h₁⟩
  · rcases v with y | x'
    · obtain ⟨rfl, rfl⟩ := path_ret_inv rfl h₂
      rw [List.append_nil]
      exact .exit h₁
    · cases cs₁ with
      | nil => exact absurd ⟨x', path_nil_val h₁⟩ hs
      | cons c cs₁ =>
        refine .step h₁ (ih x' cs₂ r ?_ h₂)
        simp at hL; omega
  · exact .div h₁

theorem path_iterPath_aux {G : X → Tree (SigEv E) (Y ⊕ X)} (L : Nat)
    (ih : ∀ (x : X) (cs : List (Call E)) (r : PathEnd Y), cs.length < L →
      Path (iterT G x) cs r → IterPath G x cs r)
    (n : Nat) : ∀ (x : X) (cs : List (Call E)) (r : PathEnd Y), cs.length = L →
      ¬ IterSilent G ((iterNext G)^[n] x) → Path (iterT G x) cs r → IterPath G x cs r := by
  induction n with
  | zero => exact fun x cs r hL hs hp => path_iterPath_base L ih hL hs hp
  | succ n ihn =>
    intro x cs r hL hs hp
    by_cases hx : IterSilent G x
    · have hG := iterNext_spec hx
      have hp' : Path (iterT G (iterNext G x)) cs r := by
        have e : (G x >>= Sum.elim pure (iterT G)) = iterT G (iterNext G x) := by
          rw [hG]; exact pure_bind _ _
        rw [iter_unfold, e] at hp
        exact hp
      have := ihn (iterNext G x) cs r hL (by rwa [Function.iterate_succ_apply] at hs) hp'
      have h1 : Path (G x) [] (.val (.inr (iterNext G x))) := .ret hG
      simpa using IterPath.step h1 this
    · exact path_iterPath_base L ih hL hx hp

theorem path_iterPath_len {G : X → Tree (SigEv E) (Y ⊕ X)} (L : Nat) :
    ∀ (x : X) (cs : List (Call E)) (r : PathEnd Y), cs.length = L → Path (iterT G x) cs r →
      IterPath G x cs r := by
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro x cs r h hp
    by_cases hall : ∀ n, IterSilent G ((iterNext G)^[n] x)
    · have hσ : ∀ n, G ((iterNext G)^[n] x) = ret (.inr ((iterNext G)^[n + 1] x)) := fun n => by
        rw [Function.iterate_succ_apply']; exact iterNext_spec (hall n)
      have hd := iter_eq_diverge G (fun n => (iterNext G)^[n] x) hσ
      simp only [Function.iterate_zero, id] at hd
      rw [hd] at hp
      obtain ⟨rfl, rfl⟩ := path_diverge_inv hp
      exact .spin _ rfl hσ
    · push Not at hall
      obtain ⟨n, hn⟩ := hall
      exact path_iterPath_aux L (fun x cs r hl hp => ih _ hl x cs r rfl hp) n x cs r h hn hp

theorem path_iterPath {G : X → Tree (SigEv E) (Y ⊕ X)} {x : X} {cs : List (Call E)}
    {r : PathEnd Y} (hp : Path (iterT G x) cs r) : IterPath G x cs r :=
  path_iterPath_len _ x cs r rfl hp

/-- The paths of an iterated tree. -/
theorem path_iter_iff {G : X → Tree (SigEv E) (Y ⊕ X)} {x : X} {cs : List (Call E)}
    {r : PathEnd Y} : Path (iterT G x) cs r ↔ IterPath G x cs r :=
  ⟨path_iterPath, iterPath_path⟩

/-! ## Iterating trees without events -/

theorem iter_ret_of_pureReach {G : X → Tree (SigEv E) (Y ⊕ X)} {x : X} {y : Y}
    (h : PureReach G x y) : iterT G x = ret y := by
  induction h with
  | done hx => rw [iter_unfold, hx]; exact pure_bind _ _
  | step hx _ ih => rw [iter_unfold, hx]; exact (pure_bind _ _).trans ih

theorem iter_pure_aux {G : X → Tree (SigEv E) (Y ⊕ X)}
    (hG : ∀ x, G x = diverge ∨ ∃ v, G x = ret v) (n : Nat) :
    ∀ x : X, ¬ IterSilent G ((iterNext G)^[n] x) → (∀ y : Y, ¬ PureReach G x y) →
      iterT G x = (diverge : Tree (SigEv E) Y) := by
  induction n with
  | zero =>
    intro x hs hn
    rcases hG x with hx | ⟨(y | x'), hx⟩
    · rw [iter_unfold, hx, diverge_bind]
    · exact absurd (PureReach.done hx) (hn y)
    · exact absurd ⟨x', hx⟩ hs
  | succ n ih =>
    intro x hs hn
    by_cases hx : IterSilent G x
    · have hG' := iterNext_spec hx
      have e : (G x >>= Sum.elim pure (iterT G)) = iterT G (iterNext G x) := by
        rw [hG']; exact pure_bind _ _
      rw [iter_unfold, e]
      exact ih _ (by rwa [Function.iterate_succ_apply] at hs) fun y hy => hn y (.step hG' hy)
    · rcases hG x with hx' | ⟨(y | x'), hx'⟩
      · rw [iter_unfold, hx', diverge_bind]
      · exact absurd (PureReach.done hx') (hn y)
      · exact absurd ⟨x', hx'⟩ hx

/-- Iterating a body without events: a finite chain of silent continuations
to an exit returns, and otherwise the iteration diverges. -/
theorem iter_pure {G : X → Tree (SigEv E) (Y ⊕ X)}
    (hG : ∀ x, G x = diverge ∨ ∃ v, G x = ret v) (x : X) :
    (∃ y, PureReach G x y ∧ iterT G x = ret y) ∨ (iterT G x = diverge ∧ ∀ y : Y, ¬ PureReach G x y) := by
  by_cases h : ∃ y, PureReach G x y
  · obtain ⟨y, hy⟩ := h
    exact .inl ⟨y, hy, iter_ret_of_pureReach hy⟩
  · push Not at h
    refine .inr ⟨?_, h⟩
    by_cases hall : ∀ n, IterSilent G ((iterNext G)^[n] x)
    · have hσ : ∀ n, G ((iterNext G)^[n] x) = ret (.inr ((iterNext G)^[n + 1] x)) := fun n => by
        rw [Function.iterate_succ_apply']; exact iterNext_spec (hall n)
      have hd := iter_eq_diverge G (fun n => (iterNext G)^[n] x) hσ
      simpa using hd
    · push Not at hall
      obtain ⟨n, hn⟩ := hall
      exact iter_pure_aux hG n x hn h

/-! ## Bodies -/

/-- Map the end of a path. -/
def mapEnd {Y Z : Type (u + 1)} (d : Y → Z) : PathEnd Y → PathEnd Z
  | .val y => .val (d y)
  | .div => .div

theorem path_map_inv {Y Z : Type (u + 1)} {t : Tree (SigEv E) Y} {d : Y → Z} {cs : List (Call E)}
    {r : PathEnd Z} (h : Path (t >>= fun y => pure (d y)) cs r) :
    ∃ r', Path t cs r' ∧ r = mapEnd d r' := by
  rcases path_bind_inv h with ⟨cs₁, cs₂, y, rfl, h₁, h₂⟩ | ⟨rfl, h₁⟩
  · obtain ⟨rfl, rfl⟩ := path_ret_inv rfl h₂
    exact ⟨_, by simpa using h₁, rfl⟩
  · exact ⟨_, h₁, rfl⟩

theorem path_map {Y Z : Type (u + 1)} {t : Tree (SigEv E) Y} {d : Y → Z} {cs : List (Call E)}
    {r : PathEnd Y} (h : Path t cs r) : Path (t >>= fun y => pure (d y)) cs (mapEnd d r) := by
  cases r with
  | val y =>
    have := path_bind_ret (k := fun y => pure (d y)) (cs₂ := []) h (Path.ret rfl)
    rw [List.append_nil] at this
    exact this
  | div => exact path_bind_div h

variable {S T A B : Type (u + 1)}

theorem run_iter (F : Hom E S T A (B ⊕ A)) (a : A) (s : S) :
    ((Silmaril.Elgot.iter F a).run s).run = iterT (loopTree F) (a, s) := by
  change Silmaril.Elgot.iter (Silmaril.Elgot.ExceptT.body (Silmaril.Elgot.StateT.body F)) (a, s) = _
  congr 1
  funext p
  simp only [Silmaril.Elgot.ExceptT.body, Silmaril.Elgot.StateT.body, loopTree, ExceptT.run_bind,
    bind_assoc, Function.comp]
  congr 1
  funext r
  rcases r with e | ⟨b | a', s'⟩ <;> simp [loopEnd, Silmaril.Elgot.ExceptT.distribute,
    Silmaril.Elgot.StateT.distribute]

theorem loopEnd_inl {r : PathEnd (Except T ((B ⊕ A) × S))} {y : Except T (B × S)}
    (h : mapEnd loopEnd r = .val (.inl y)) :
    (∃ e, r = .val (.error e) ∧ y = .error e) ∨
      ∃ b s, r = .val (.ok (.inl b, s)) ∧ y = .ok (b, s) := by
  rcases r with (e | ⟨b | a, s⟩) | _ <;> simp_all [mapEnd, loopEnd]

theorem loopEnd_inr {r : PathEnd (Except T ((B ⊕ A) × S))} {p : A × S}
    (h : mapEnd loopEnd r = .val (.inr p)) : r = .val (.ok (.inr p.1, p.2)) := by
  obtain ⟨a₀, s₀⟩ := p
  rcases r with (e | ⟨b | a, s⟩) | _ <;> simp_all [mapEnd, loopEnd]

theorem loopEnd_div {r : PathEnd (Except T ((B ⊕ A) × S))}
    (h : mapEnd loopEnd r = (.div : PathEnd (Except T (B × S) ⊕ (A × S)))) : r = .div := by
  rcases r with (e | ⟨b | a, s⟩) | _ <;> simp_all [mapEnd, loopEnd]

theorem iterPath_toAFun {F : Hom E S T A (B ⊕ A)} {p : A × S} {cs : List (Call E)}
    {r : PathEnd (Except T (B × S))} (h : IterPath (loopTree F) p cs r) :
    AFun.IterBeh (toAFun F) p.2 p.1 (cs.map liftCall, endOf r) := by
  induction h with
  | exit hp =>
    obtain ⟨r', hp', he⟩ := path_map_inv hp
    rcases loopEnd_inl he.symm with ⟨e, rfl, rfl⟩ | ⟨b, s, rfl, rfl⟩
    · exact AFun.IterBeh.trap ⟨_, _, hp', rfl⟩
    · exact AFun.IterBeh.exit ⟨_, _, hp', rfl⟩
  | div hp =>
    obtain ⟨r', hp', he⟩ := path_map_inv hp
    obtain rfl := loopEnd_div he.symm
    exact AFun.IterBeh.div ⟨_, _, hp', rfl⟩
  | step hp _ ih =>
    obtain ⟨r', hp', he⟩ := path_map_inv hp
    obtain rfl := loopEnd_inr he.symm
    rw [List.map_append]
    exact AFun.IterBeh.step ⟨_, _, hp', rfl⟩ ih
  | @spin p σ h0 hσ =>
    refine AFun.IterBeh.spin (fun n => ((σ n).2, (σ n).1)) (by simp [h0]) fun n => ?_
    obtain ⟨r', hp', he⟩ := path_map_inv (Path.ret (hσ n) : Path (loopTree F (σ n)) [] _)
    obtain rfl := loopEnd_inr he.symm
    exact ⟨[], _, hp', rfl⟩

theorem iterBeh_path {F : Hom E S T A (B ⊕ A)} {s : S} {a : A} {x}
    (h : AFun.IterBeh (toAFun F) s a x) :
    ∃ cs r, IterPath (loopTree F) (a, s) cs r ∧ x = (cs.map liftCall, endOf r) := by
  induction h with
  | exit hm =>
    obtain ⟨cs, r, hp, he⟩ := hm
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, he⟩ := he
    obtain rfl := endOf_eq_ret he.symm
    exact ⟨cs, _, IterPath.exit (path_map (d := loopEnd) hp), by simp [endOf]⟩
  | trap hm =>
    obtain ⟨cs, r, hp, he⟩ := hm
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, he⟩ := he
    obtain ⟨e, rfl⟩ := endOf_eq_trap he.symm
    exact ⟨cs, _, IterPath.exit (path_map (d := loopEnd) hp), by simp [endOf]⟩
  | div hm =>
    obtain ⟨cs, r, hp, he⟩ := hm
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, he⟩ := he
    obtain rfl := endOf_eq_div he.symm
    exact ⟨cs, _, IterPath.div (path_map (d := loopEnd) hp), rfl⟩
  | step hm _ ih =>
    obtain ⟨cs₁, r₁, hp, he⟩ := hm
    obtain ⟨cs₂, r₂, hp₂, he₂⟩ := ih
    simp only [Prod.mk.injEq] at he he₂
    obtain ⟨rfl, rfl⟩ := he₂
    obtain ⟨rfl, he⟩ := he
    obtain rfl := endOf_eq_ret he.symm
    exact ⟨cs₁ ++ cs₂, r₂, IterPath.step (path_map (d := loopEnd) hp) hp₂, by simp⟩
  | @spin s a σ h0 hσ =>
    refine ⟨[], .div, IterPath.spin (fun n => ((σ n).2, (σ n).1)) (by simp [h0]) fun n => ?_, rfl⟩
    obtain ⟨cs, r, hp, he⟩ := hσ n
    simp only [Prod.mk.injEq] at he
    obtain ⟨hc, he⟩ := he
    obtain rfl : cs = [] := List.map_eq_nil_iff.1 hc.symm
    obtain rfl := endOf_eq_ret he.symm
    exact path_nil_val (path_map (d := loopEnd) hp)

theorem toAFun_of_run_ret {B : Type (u + 1)} {f : Hom E S T A B} {s : S} {a : A}
    {v : Except T (B × S)} (h : ((f a).run s).run = ret v) :
    toAFun f s a = {([], endOf (.val v))} := by
  ext x
  constructor
  · rintro ⟨cs, r, hp, rfl⟩
    obtain ⟨rfl, rfl⟩ := path_ret_inv h hp
    rfl
  · rintro rfl
    exact ⟨[], _, .ret h, rfl⟩

theorem toAFun_of_run_diverge {B : Type (u + 1)} {f : Hom E S T A B} {s : S} {a : A}
    (h : ((f a).run s).run = diverge) : toAFun f s a = {([], .div)} := by
  ext x
  constructor
  · rintro ⟨cs, r, hp, rfl⟩
    rw [h] at hp
    obtain ⟨rfl, rfl⟩ := path_diverge_inv hp
    rfl
  · rintro rfl
    exact ⟨[], _, .div h, rfl⟩

theorem toAFun_iter (F : Hom E S T A (B ⊕ A)) :
    toAFun (Silmaril.Elgot.iter F) = AFun.iter (toAFun F) := by
  funext s a
  ext x
  constructor
  · rintro ⟨cs, r, hp, rfl⟩
    rw [run_iter, path_iter_iff] at hp
    exact iterPath_toAFun hp
  · intro hx
    obtain ⟨cs, r, hp, rfl⟩ := iterBeh_path hx
    exact ⟨cs, r, by rw [run_iter, path_iter_iff]; exact hp, rfl⟩

end Silmaril.Proofs.Wasm.Abstract.BodyTrace
