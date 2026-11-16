module

public import Silmaril.Wasm.Abstract.BodyDet.Defs
public import Silmaril.Wasm.Abstract.BodyStrat.Thms
public import Silmaril.Games.Abstract.StratObs.Thms
public import Silmaril.Semantics.ITree.Thms

/-!
# Deterministic observation triples: proofs

A tree has one next event at each node, so along one call log there is one
node: at most one pending call there, and never both an end and a call.
P-move determinism of `toDStrat t` reads the next automaton step off the
triple.
-/

public section

namespace Silmaril.Proofs.Wasm.Abstract.BodyDet

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract.Body
  Silmaril.Wasm.Abstract.BodyTrace Silmaril.Wasm.Abstract.BodyStrat
  Silmaril.Wasm.Abstract.BodyDet Silmaril.Elgot.ITree

universe u

section Tree

variable {E : Sig.{u}} {Y : Type (u + 1)}

theorem vis_heq {R R' : Type u} {e : SigEv E R} {e' : SigEv E R'}
    {k : R → Tree (SigEv E) Y} {k' : R' → Tree (SigEv E) Y} (h : vis e k = vis e' k') :
    R = R' ∧ HEq e e' ∧ HEq k k' := by
  have := congrArg out h
  simp only [out_vis, Part.some_inj, Visible.vis.injEq] at this
  exact this

theorem answer_eq {R : Type u} {e : SigEv E R} {n n' : R}
    (h : (⟨e.1, cast e.2.symm n⟩ : Call E) = ⟨e.1, cast e.2.symm n'⟩) : n = n' := by
  have := congrArg (cast e.2) (eq_of_heq (Sigma.mk.inj h).2)
  simpa using this

/-- At most one pending call after a call log. -/
theorem pend_unique {t : Tree (SigEv E) Y} {c c' : List (Call E)} {m m' : E.Op}
    (h : Pend t c m) (h' : Pend t c' m') (hc : c = c') : m = m' := by
  induction h generalizing c' m' with
  | here ht =>
    cases h' with
    | here ht' =>
      rw [ht] at ht'
      obtain ⟨rfl, he, -⟩ := vis_heq ht'
      rw [eq_of_heq he]
    | vis _ _ => simp at hc
  | @vis t R e k n cs m ht hp ih =>
    cases h' with
    | here _ => simp at hc
    | @vis _ R' e' k' n' cs' m'' ht' hp' =>
      rw [ht] at ht'
      obtain ⟨rfl, he, hk⟩ := vis_heq ht'
      obtain rfl := eq_of_heq he
      obtain rfl := eq_of_heq hk
      obtain ⟨h₁, h₂⟩ := List.cons.inj hc
      obtain rfl := answer_eq h₁
      exact ih hp' h₂

/-- No call log both ends a finished path and has a pending call. -/
theorem path_not_pend {t : Tree (SigEv E) Y} {c c' : List (Call E)} {r : PathEnd Y}
    {m : E.Op} (h : Path t c r) (h' : Pend t c' m) (hc : c = c') : False := by
  induction h generalizing c' with
  | ret ht =>
    cases h' with
    | here ht' => rw [ht] at ht'; exact ret_ne_vis _ _ _ ht'
    | vis ht' _ => rw [ht] at ht'; exact ret_ne_vis _ _ _ ht'
  | div ht =>
    cases h' with
    | here ht' => rw [ht] at ht'; exact vis_ne_diverge _ _ ht'.symm
    | vis ht' _ => rw [ht] at ht'; exact vis_ne_diverge _ _ ht'.symm
  | @vis t R e k n cs r ht hp ih =>
    cases h' with
    | here _ => simp at hc
    | @vis _ R' e' k' n' cs' m'' ht' hp' =>
      rw [ht] at ht'
      obtain ⟨rfl, he, hk⟩ := vis_heq ht'
      obtain rfl := eq_of_heq he
      obtain rfl := eq_of_heq hk
      obtain ⟨h₁, h₂⟩ := List.cons.inj hc
      obtain rfl := answer_eq h₁
      exact ih hp' h₂

/-- Forget the lift of a call. -/
def unlift (x : Call (liftSig E)) : Call E := ⟨x.1.down, x.2.down⟩

theorem map_liftCall_inj {cs cs' : List (Call E)} (h : cs.map liftCall = cs'.map liftCall) :
    cs = cs' :=
  List.map_injective_iff.2
    (Function.LeftInverse.injective (g := unlift) fun _ => rfl) h

end Tree

theorem toTriple_det {E : Sig.{u}} {S T A B : Type (u + 1)} (f : Hom E S T A B) :
    TripleDet (toTriple f) where
  fin := toAFun_det f
  pend := by
    rintro s a c m m' ⟨cs, m₁, h₁, he₁⟩ ⟨cs', m₂, h₂, he₂⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he₁
    obtain ⟨hc, rfl⟩ := Prod.mk.inj he₂
    rw [pend_unique h₁ h₂ (map_liftCall_inj hc)]
  excl := by
    rintro s a c e m ⟨cs, r, h₁, he₁⟩ ⟨cs', m₁, h₂, he₂⟩
    exact path_not_pend h₁ h₂
      (map_liftCall_inj ((Prod.mk.inj he₁).1.symm.trans (Prod.mk.inj he₂).1))
  inf := by
    intro s a ω hω k
    rw [← StratObs.saturated_iff.1 (toTriple_saturated f)]
    exact .inr (.inr (.inr ⟨ω, hω, k, rfl, rfl⟩))

section Triple

variable {E : Sig.{u}} {S A B : Type u}

/-- Behaviours with the same log agree on their end. -/
theorem agree_self {c : List (Call E)} {e e' : End S B} (h : AFun.Agree c e c e') : e = e' := by
  induction c with
  | nil => exact h
  | cons x c ih => obtain ⟨m, n⟩ := x; exact ih (h.2 HEq.rfl)

theorem ansEnd_inj {r r' : (B × S) ⊕ PUnit.{u + 1}}
    (h : StratObs.ansEnd r = StratObs.ansEnd r') : r = r' := by
  rcases r with ⟨b, s⟩ | ⟨⟩ <;> rcases r' with ⟨b', s'⟩ | ⟨⟩ <;>
    simp_all [StratObs.ansEnd]

theorem toDStrat_pdet {t : ObsTriple E S A B} (hs : StratObs.Saturated t) (hd : TripleDet t) :
    PDet (StratObs.toDStrat t).toStrategy := by
  intro p o o' h h' ho _
  obtain ⟨z, hz⟩ := StratObs.mem_toDStrat.1 h
  obtain ⟨z', hz'⟩ := StratObs.mem_toDStrat.1 h'
  obtain ⟨y, hy, hyz⟩ := hz.of_append
  obtain ⟨y', hy', hyz'⟩ := hz'.of_append
  obtain rfl := hy.det hy'
  have hP := StratObs.saturated_iff.1 hs
  rcases hyz with _ | ⟨h₁, -⟩
  rcases hyz' with _ | ⟨h₂, -⟩
  cases h₁ with
  | ask => simp [Move.IsP] at ho
  | reply => simp [Move.IsP] at ho
  | call q c m hm =>
    rw [hP] at hm
    cases h₂ with
    | call _ _ m' hm' =>
      rw [hP] at hm'
      rw [hd.pend _ _ _ _ _ hm hm']
    | ret _ _ r hr => exact (hd.excl _ _ _ _ _ hr hm).elim
  | ret q c r hr =>
    cases h₂ with
    | call _ _ m hm =>
      rw [hP] at hm
      exact (hd.excl _ _ _ _ _ hr hm).elim
    | ret _ _ r' hr' =>
      rw [ansEnd_inj (agree_self
        (hd.fin q.1 q.2 (c, StratObs.ansEnd r) (c, StratObs.ansEnd r') hr hr'))]

end Triple

end Silmaril.Proofs.Wasm.Abstract.BodyDet
