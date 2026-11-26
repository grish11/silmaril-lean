module

public import Silmaril.Semantics.ITree.Signature.Trace.Defs

public section

namespace Silmaril.Elgot.ITree.TraceSignature.Proofs

open CategoryTheory

universe u v w

variable {S T U : TraceSignature.{u}} {A : Type v} {X : Type w}

@[simp] theorem reply_forward_backward (f : S ⟶ T) (q : Request S.toSignature.Event) (r : q.1) :
    f.hom.reply q ((f.replyEquiv q).symm r) = r :=
  (f.replyEquiv q).apply_symm_apply r

@[simp] theorem reply_backward_forward (f : S ⟶ T) (q : Request S.toSignature.Event)
    (r : (f.hom.request q).1) : (f.replyEquiv q).symm (f.hom.reply q r) = r :=
  (f.replyEquiv q).symm_apply_apply r

theorem trace_id (p : Trace S.toSignature.Event A) : (𝟙 S : S ⟶ S).trace p = p := by
  induction p with
  | «prefix» | request | result => rfl
  | @exchange R ev r p ih =>
    have hr : ((𝟙 S : S ⟶ S).replyEquiv ⟨R, ev⟩).symm r = r :=
      reply_forward_backward (𝟙 S) ⟨R, ev⟩ r
    change Trace.exchange ev _ _ = _
    rw [hr, ih]

theorem trace_comp (f : S ⟶ T) (g : T ⟶ U) (p : Trace S.toSignature.Event A) :
    (f ≫ g).trace p = g.trace (f.trace p) := by
  induction p with
  | «prefix» | request | result => rfl
  | @exchange R ev r p ih =>
    let q : Request S.toSignature.Event := ⟨R, ev⟩
    have hr : ((f ≫ g).replyEquiv q).symm r =
        (g.replyEquiv (f.hom.request q)).symm ((f.replyEquiv q).symm r) := by
      apply ((f ≫ g).replyEquiv q).injective
      change (f ≫ g).hom.reply q (((f ≫ g).replyEquiv q).symm r) =
        f.hom.reply q (g.hom.reply (f.hom.request q) _)
      simp only [reply_forward_backward]
    change Trace.exchange (g.hom.request (f.hom.request q)).2 _ _ = Trace.exchange _ _ _
    rw [hr, ih]

theorem trace_ofEquiv (e : SignatureEquiv S.toSignature.Event T.toSignature.Event)
    (p : Trace S.toSignature.Event A) : (ofEquiv e).trace p = e.trace (Equiv.refl A) p := by
  induction p with
  | «prefix» | request | result => rfl
  | @exchange R ev r p ih =>
    let q : Request S.toSignature.Event := ⟨R, ev⟩
    have hr : (((ofEquiv e : S ⟶ T).replyEquiv q).symm r) = e.reply q r := by
      apply (e.reply q).symm.injective
      exact (reply_forward_backward (ofEquiv e) q r).trans ((e.reply q).symm_apply_apply r).symm
    change Trace.exchange (e.request q).2 _ _ = Trace.exchange (e.request q).2 _ _
    rw [hr, ih]

theorem trace_injective (f : S ⟶ T) : Function.Injective (f.trace (A := A)) := by
  intro p p' h
  induction p generalizing p' with
  | «prefix» | result =>
    cases p' <;> cases h
    rfl
  | @request R ev =>
    cases p' with
    | @request R' ev' =>
      have eq := congrArg (fun
        | .request ev => some (⟨_, ev⟩ : Request T.toSignature.Event)
        | _ => none) h
      exact congrArg (fun q : Request S.toSignature.Event => Trace.request q.2)
        (f.request_injective (Option.some.inj eq))
    | «prefix» | result | exchange => cases h
  | @exchange R ev r p ih =>
    cases p' with
    | @exchange R' ev' r' p' =>
      have parts := Option.some.inj (congrArg (fun
        | .exchange ev r tail => some (⟨⟨_, ev⟩, r, tail⟩ :
            (q : Request T.toSignature.Event) × (q.1 × Trace T.toSignature.Event A))
        | _ => none) h)
      have requests : (⟨R, ev⟩ : Request S.toSignature.Event) = ⟨R', ev'⟩ :=
        f.request_injective (congrArg Sigma.fst parts)
      cases requests
      have eq := eq_of_heq (Sigma.mk.inj_iff.mp parts).2
      exact congrArg₂ (Trace.exchange ev) ((f.replyEquiv ⟨R, ev⟩).symm.injective
        (congrArg Prod.fst eq)) (ih (congrArg Prod.snd eq))
    | «prefix» | request | result => cases h

private theorem out_translate (f : S ⟶ T) (t : Tree S.toSignature.Event A)
    (node : Visible S.toSignature.Event A (Tree S.toSignature.Event A))
    (h : out t = Part.some node) :
    out (f.hom.tree id t) = Part.some (f.hom.visible id (f.hom.tree id) node) := by
  rw [f.hom.out_tree, h, Part.map_some]

private theorem out_reflect (f : S ⟶ T) (t : Tree S.toSignature.Event A)
    (node : Visible T.toSignature.Event A (Tree T.toSignature.Event A))
    (h : out (f.hom.tree id t) = Part.some node) :
    ∃ source, out t = Part.some source ∧ f.hom.visible id (f.hom.tree id) source = node := by
  rw [f.hom.out_tree, Part.eq_some_iff, Part.mem_map_iff] at h
  obtain ⟨source, hs, eq⟩ := h
  exact ⟨source, Part.eq_some_iff.mpr hs, eq⟩

private theorem handled_forward (f : S ⟶ T) (step : Handler X T.toSignature.Event)
    (x : X) (t : Tree S.toSignature.Event A) (p : Trace S.toSignature.Event A) :
    HandledTrace (f.hom.restrict step) x t p → HandledTrace step x (f.hom.tree id t) (f.trace p) := by
  induction p generalizing x t with
  | «prefix» => exact id
  | result a => exact fun h => ⟨out_translate f t (.ret a) h.1, trivial⟩
  | @request R ev =>
    rintro ⟨⟨k, hk⟩, _⟩
    exact ⟨⟨_, out_translate f t (.vis ev k) hk⟩, trivial⟩
  | @exchange R ev r p ih =>
    rintro ⟨⟨k, hk, ht⟩, y, ⟨r', hr, hs⟩, hp⟩
    let q : Request S.toSignature.Event := ⟨R, ev⟩
    change f.hom.reply q r' = r at hr
    subst r
    obtain ⟨ht', hp'⟩ := ih y (k (f.hom.reply q r')) ⟨ht, hp⟩
    have eq := reply_backward_forward f q r'
    refine ⟨⟨_, out_translate f t (.vis ev k) hk, ?_⟩, y, ?_, hp'⟩
    · change HasTrace (f.hom.tree id (k (f.hom.reply q ((f.replyEquiv q).symm
        (f.hom.reply q r'))))) (f.trace p)
      rwa [eq]
    · change step (f.hom.request q) x ((f.replyEquiv q).symm (f.hom.reply q r')) y
      rwa [eq]

private theorem handled_reflect (f : S ⟶ T) (step : Handler X T.toSignature.Event)
    (x : X) (t : Tree S.toSignature.Event A) (p : Trace T.toSignature.Event A) :
    HandledTrace step x (f.hom.tree id t) p →
      ∃ source, HandledTrace (f.hom.restrict step) x t source ∧ f.trace source = p := by
  induction p generalizing x t with
  | «prefix» => exact fun _ => ⟨.prefix, ⟨trivial, trivial⟩, rfl⟩
  | result a =>
    intro h
    obtain ⟨node, hn, eq⟩ := out_reflect f t (.ret a) h.1
    cases node <;> cases eq
    exact ⟨.result _, ⟨hn, trivial⟩, rfl⟩
  | @request R ev =>
    rintro ⟨⟨k, hk⟩, _⟩
    obtain ⟨node, hn, eq⟩ := out_reflect f t (.vis ev k) hk
    cases node with
    | ret => cases eq
    | vis ev' k' =>
      cases eq
      exact ⟨.request ev', ⟨⟨k', hn⟩, trivial⟩, rfl⟩
  | @exchange R ev r p ih =>
    rintro ⟨⟨k, hk, ht⟩, y, hy, hp⟩
    obtain ⟨node, hn, eq⟩ := out_reflect f t (.vis ev k) hk
    cases node with
    | ret => cases eq
    | @vis R' ev' k' =>
      cases eq
      let q : Request S.toSignature.Event := ⟨R', ev'⟩
      obtain ⟨tail, ⟨ht', hp'⟩, rfl⟩ := ih y (k' (f.hom.reply q r)) ⟨ht, hp⟩
      refine ⟨.exchange ev' (f.hom.reply q r) tail,
        ⟨⟨k', hn, ht'⟩, y, ⟨r, rfl, hy⟩, hp'⟩, ?_⟩
      change Trace.exchange (f.hom.request q).2 ((f.replyEquiv q).symm (f.hom.reply q r)) _ = _
      rw [reply_backward_forward]

theorem handledTrace_image (f : S ⟶ T) (step : Handler X T.toSignature.Event)
    (x : X) (t : Tree S.toSignature.Event A) (p : Trace T.toSignature.Event A) :
    HandledTrace step x (f.hom.tree id t) p ↔
      ∃ source, HandledTrace (f.hom.restrict step) x t source ∧ f.trace source = p :=
  ⟨handled_reflect f step x t p, fun ⟨source, hs, h⟩ => h ▸ handled_forward f step x t source hs⟩

end Silmaril.Elgot.ITree.TraceSignature.Proofs
