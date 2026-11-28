module

public import Silmaril.Semantics.TrackA.Interaction.Relabel.Defs
public import Silmaril.Semantics.TrackA.Interaction.UB.Thms

public section

namespace Silmaril.Proofs.Semantics.TrackA.Interaction.Relabel

open Silmaril.Semantics.TrackA.Interaction

universe u v w x y z a

variable {S : Signature.{u,v}} {T : Signature.{w,x}} {U : Signature.{y,z}} {A : Type a}

private theorem decode_reply (f : Signature.TraceHom S T) (q : S.Request) (r : S.Response q) :
    f.hom.response q (f.reply q r) = r := (f.reply q).symm_apply_apply r

private theorem exchange_id (e : S.Exchange) : (Signature.TraceHom.id S).exchange e = e := by
  rcases e with ⟨q, r⟩
  exact Sigma.ext rfl (heq_of_eq (decode_reply (Signature.TraceHom.id S) q r))

private theorem exchange_comp (f : Signature.TraceHom S T) (g : Signature.TraceHom T U)
    (e : S.Exchange) : (g.comp f).exchange e = g.exchange (f.exchange e) := by
  rcases e with ⟨q, r⟩
  have replies : (g.comp f).reply q r = g.reply (f.hom.request q) (f.reply q r) := by
    apply (g.comp f).bijective q |>.1
    change (g.comp f).hom.response q ((g.comp f).reply q r) =
      f.hom.response q (g.hom.response (f.hom.request q) (g.reply _ (f.reply q r)))
    rw [decode_reply, decode_reply, decode_reply]
  exact Sigma.ext (show (g.comp f).hom.request q = g.hom.request (f.hom.request q) from rfl)
    (heq_of_eq replies)

theorem trace_id (t : Trace S A) : Trace.relabel (Signature.TraceHom.id S) t = t := by
  have exchanges : (Signature.TraceHom.id S).exchange = id := funext exchange_id
  cases t with
  | finite events ending =>
    simp only [Trace.relabel, exchanges, List.map_id]
    congr 1
    cases ending <;> rfl
  | infinite events => simp only [Trace.relabel, exchanges, Function.id_comp]

theorem trace_comp (f : Signature.TraceHom S T) (g : Signature.TraceHom T U) (t : Trace S A) :
    t.relabel (g.comp f) = (t.relabel f).relabel g := by
  have exchanges : (g.comp f).exchange = g.exchange ∘ f.exchange := funext (exchange_comp f g)
  cases t with
  | finite events ending =>
    simp only [Trace.relabel, exchanges, List.map_map]
    congr 1
    cases ending <;> rfl
  | infinite events => simp only [Trace.relabel, exchanges, Function.comp_assoc]

theorem classify_relabel (f : Signature.TraceHom S T) (t : Trace S (Option A)) :
    UB.classify (t.relabel f) = (UB.classify t).map (Trace.relabel f) := by
  cases t with
  | finite events ending =>
    cases ending with
    | returned value => cases value <;> rfl
    | stuck | deadlock | diverge => rfl
  | infinite => rfl

theorem atBoundary_relabel (f : Signature.TraceHom S T) (runs : Set (Trace S (Option A))) :
    UB.atBoundary (Trace.relabel f '' runs) = Option.map (Trace.relabel f) '' UB.atBoundary runs := by
  simp only [UB.atBoundary, Set.image_image, classify_relabel]


theorem boundary_ub_iff (runs : Set (Trace S (Option A))) :
    none ∈ UB.atBoundary runs ↔ ∃ events, Trace.finite events (.returned none) ∈ runs := by
  constructor
  · rintro ⟨trace, observed, classified⟩
    cases trace with
    | finite events ending =>
      cases ending with
      | returned value =>
        cases value with
        | none => exact ⟨events, observed⟩
        | some => contradiction
      | stuck | deadlock | diverge => contradiction
    | infinite => contradiction
  · rintro ⟨events, observed⟩
    exact ⟨.finite events (.returned none), observed, rfl⟩

end Silmaril.Proofs.Semantics.TrackA.Interaction.Relabel
