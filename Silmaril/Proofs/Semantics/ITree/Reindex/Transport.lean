module

public import Silmaril.Semantics.ITree.Reindex.Defs

public section

namespace Silmaril.Proofs.ITree.Reindex

open Silmaril.Elgot.ITree

universe u v w w'

variable {E F : Type u → Type u} {A B : Type v}

theorem tree_refl (t : Tree E A) : (SignatureEquiv.refl E).tree (Equiv.refl A) t = t := by
  have approx_refl (n : Nat) (x : Approx E A n) :
      (SignatureEquiv.refl E).approx (Equiv.refl A) n x = x := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change Part.map _ x = x
      apply Part.map_id'
      intro node
      cases node with
      | ret => rfl
      | vis ev k =>
        change Visible.vis ev (fun r => (SignatureEquiv.refl E).approx (Equiv.refl A) n (k r)) = _
        simp only [ih]
  exact Tree.ext fun n => approx_refl n (t.observe n)

theorem tree_trans {G : Type u → Type u} {C : Type v} (e : SignatureEquiv E F)
    (f : SignatureEquiv F G) (a : A ≃ B) (b : B ≃ C) (t : Tree E A) :
    (e.trans f).tree (a.trans b) t = f.tree b (e.tree a t) := by
  have approx_trans (n : Nat) (x : Approx E A n) :
      (e.trans f).approx (a.trans b) n x = f.approx b n (e.approx a n x) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [SignatureEquiv.approx, Equiv.coe_fn_mk, Part.map_map]
      apply congrArg (fun g => Part.map g x)
      funext node
      cases node with
      | ret => rfl
      | @vis R ev k =>
        let inv := ((e.trans f).reply ⟨R, ev⟩).symm
        change Visible.vis _ (fun r => (e.trans f).approx (a.trans b) n (k (inv r))) =
          Visible.vis _ (fun r => f.approx b n (e.approx a n (k (inv r))))
        simp only [ih]
        rfl
  exact Tree.ext fun n => approx_trans n (t.observe n)

theorem out_tree (e : SignatureEquiv E F) (a : A ≃ B) (t : Tree E A) :
    out (e.tree a t) = Part.map (e.visibleEquiv a (e.treeEquiv a)) (out t) := by
  rw [← out_roll (Part.map (e.visibleEquiv a (e.treeEquiv a)) (out t))]
  congr 1
  apply Tree.ext
  intro n
  cases n with
  | zero => rfl
  | succ n =>
    change Part.map (e.visibleEquiv a (e.approx a n)) (t.observe (n + 1)) = _
    rw [observe_succ_eq_out, Part.map_eq_map]
    simp only [roll, Part.map_eq_map, Part.map_map]
    apply congrArg (fun f => Part.map f (out t))
    funext node
    cases node <;> rfl

private theorem out_tree_some_iff (e : SignatureEquiv E F) (a : A ≃ B) (t : Tree E A)
    (node : Visible E A (Tree E A)) :
    out (e.tree a t) = Part.some (e.visibleEquiv a (e.treeEquiv a) node) ↔
      out t = Part.some node := by
  rw [out_tree]
  simp [Part.eq_some_iff, Part.mem_map_iff]

theorem hasTrace_tree_iff (e : SignatureEquiv E F) (a : A ≃ B) (t : Tree E A)
    (p : Trace E A) : HasTrace (e.tree a t) (e.trace a p) ↔ HasTrace t p := by
  induction p generalizing t with
  | «prefix» => rfl
  | result b => exact out_tree_some_iff e a t (.ret b)
  | @request R ev =>
    let q : Request E := ⟨R, ev⟩
    let ek := Equiv.arrowCongr (e.reply q) (e.treeEquiv a)
    change (∃ k, out (e.tree a t) = Part.some (.vis (e.request q).2 k)) ↔ _
    constructor
    · rintro ⟨k, h⟩
      refine ⟨ek.symm k, (out_tree_some_iff e a t (.vis ev (ek.symm k))).mp ?_⟩
      change out (e.tree a t) = Part.some (.vis (e.request q).2 (ek (ek.symm k)))
      rwa [ek.apply_symm_apply]
    · rintro ⟨k, h⟩
      exact ⟨ek k, (out_tree_some_iff e a t (.vis ev k)).mpr h⟩
  | @exchange R ev r tail ih =>
    let q : Request E := ⟨R, ev⟩
    let ek := Equiv.arrowCongr (e.reply q) (e.treeEquiv a)
    change (∃ k, out (e.tree a t) = Part.some (.vis (e.request q).2 k) ∧
      HasTrace (k (e.reply q r)) (e.trace a tail)) ↔ _
    have cont (k : R → Tree E A) : ek k (e.reply q r) = e.tree a (k r) := by
      change e.tree a (k ((e.reply q).symm (e.reply q r))) = _
      rw [Equiv.symm_apply_apply]
    constructor
    · rintro ⟨k, h, ht⟩
      have hk := ek.apply_symm_apply k
      refine ⟨ek.symm k, (out_tree_some_iff e a t (.vis ev (ek.symm k))).mp ?_, ?_⟩
      · change out (e.tree a t) = Part.some (.vis (e.request q).2 (ek (ek.symm k)))
        rwa [hk]
      · apply (ih (ek.symm k r)).mp
        rwa [← cont, hk]
    · rintro ⟨k, h, ht⟩
      refine ⟨ek k, (out_tree_some_iff e a t (.vis ev k)).mpr h, ?_⟩
      rw [cont]
      exact (ih (k r)).mpr ht

variable {S : Type w} {T : Type w'} {step : Handler S E} {step' : Handler T F}

theorem replay_iff (e : SignatureEquiv E F) (a : A ≃ B) (s : S ≃ T)
    (hstep : ∀ q x r y, step' (e.request q) (s x) (e.reply q r) (s y) ↔ step q x r y)
    (x : S) (p : Trace E A) :
    Replay step' (s x) (e.trace a p) ↔ Replay step x p := by
  induction p generalizing x with
  | «prefix» | request | result => rfl
  | @exchange R ev r tail ih =>
    change (∃ y, step' (e.request ⟨R, ev⟩) (s x) (e.reply ⟨R, ev⟩ r) y ∧
      Replay step' y (e.trace a tail)) ↔ _
    constructor
    · rintro ⟨y, hy, hr⟩
      obtain ⟨y, rfl⟩ := s.surjective y
      exact ⟨y, (hstep _ _ _ _).mp hy, (ih y).mp hr⟩
    · rintro ⟨y, hy, hr⟩
      exact ⟨s y, (hstep _ _ _ _).mpr hy, (ih y).mpr hr⟩

theorem trace_surjective (e : SignatureEquiv E F) (a : A ≃ B) :
    Function.Surjective (e.trace a) := by
  intro p
  induction p with
  | «prefix» => exact ⟨.prefix, rfl⟩
  | @request R ev =>
    obtain ⟨q, hq⟩ := e.request.surjective ⟨R, ev⟩
    exact ⟨.request q.2, congrArg (fun q : Request F => (Trace.request q.2 : Trace F B)) hq⟩
  | @exchange R ev r tail ih =>
    obtain ⟨past, hpast⟩ := ih
    have lift (q' : Request F) (r' : q'.1) (hq' : ∃ q, e.request q = q') :
        ∃ p, e.trace a p = .exchange q'.2 r' tail := by
      obtain ⟨q, rfl⟩ := hq'
      exact ⟨.exchange q.2 ((e.reply q).symm r') past, by
        change Trace.exchange (e.request q).2 (e.reply q ((e.reply q).symm r')) (e.trace a past) = _
        rw [Equiv.apply_symm_apply, hpast]⟩
    exact lift ⟨R, ev⟩ r (e.request.surjective _)
  | result b => exact ⟨.result (a.symm b), by simp [SignatureEquiv.trace]⟩

end Silmaril.Proofs.ITree.Reindex
