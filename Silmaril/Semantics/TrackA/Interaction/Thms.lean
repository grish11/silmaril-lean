module

public import Silmaril.Semantics.TrackA.Interaction.Defs
import Silmaril.Proofs.Semantics.TrackA.Interaction.Core

public section

namespace Silmaril.Semantics.TrackA.Interaction

universe u v w x y z b c t r

variable {S : Signature.{u,v}} {T : Signature.{w,x}} {U : Signature.{t,r}}
variable {B : Signature.{b,c}} {A : Type y} {X : Type z}

@[simp] theorem Signature.Hom.id_comp (f : Signature.Hom S T) :
    (Signature.Hom.id T).comp f = f := rfl

@[simp] theorem Signature.Hom.comp_id (f : Signature.Hom S T) :
    f.comp (Signature.Hom.id S) = f := rfl

@[simp] theorem Node.relabel_id (n : Node S B A X) :
    n.relabel (Signature.Hom.id S) = n := by cases n <;> rfl

theorem Node.relabel_comp (f : Signature.Hom S T) (g : Signature.Hom T U) (n : Node S B A X) :
    n.relabel (g.comp f) = (n.relabel f).relabel g := by cases n <;> rfl

namespace Coalgebra

variable {c : Coalgebra S B A X} {start next : X}

/-- An internal edge admits every may observation of its successor. -/
theorem observes_mono_internal (edge : c.Internal start next) :
    c.observes next ⊆ c.observes start :=
  Proofs.Semantics.TrackA.Interaction.Coalgebra.observes_mono_internal edge

/-- A leading tau preserves all observations, including divergence and
infinite exchange streams. -/
theorem observes_tau (h : c start = .tau next) : c.observes start = c.observes next :=
  Proofs.Semantics.TrackA.Interaction.Coalgebra.observes_tau h

theorem observes_silent_loop (h : c start = .tau start) :
    Trace.finite [] .diverge ∈ c.observes start :=
  Proofs.Semantics.TrackA.Interaction.Coalgebra.observes_silent_loop h

theorem observes_visible_loop {q : S.Request} (reply : S.Response q)
    (h : c start = .vis q (fun _ => start)) :
    Trace.infinite (fun _ => ⟨q, reply⟩) ∈ c.observes start :=
  Proofs.Semantics.TrackA.Interaction.Coalgebra.observes_visible_loop reply h

/-- A handled request takes its own typed response and resumes in the updated
handler state. The resulting administrative step is observation-transparent. -/
theorem observes_handle_vis {H : Type*} (handler : Handler S H) (h : H) {q : S.Request}
    {k : S.Response q → X} (layer : c start = .vis q k) :
    (c.handle (T := T) handler).observes (start, h) =
      (c.handle (T := T) handler).observes (k (handler h q).1, (handler h q).2) := by
  apply observes_tau
  simp [handle, layer]

theorem iterate_feedback_diverges {I : Type*} (body : Coalgebra S B (A ⊕ I) X)
    (entry : I → X) (i : I) (loop : body (entry i) = .ret (.inr i)) :
    Trace.finite [] .diverge ∈ (body.iterate entry).observes (entry i) := by
  apply observes_silent_loop
  simp [iterate, loop]

end Coalgebra

theorem obsEq_iff_mutual_refines {left right : Set (Trace S A)} :
    ObsEq left right ↔ Refines left right ∧ Refines right left :=
  ⟨fun h => h ▸ ⟨Set.Subset.rfl, Set.Subset.rfl⟩, fun h => h.1.antisymm h.2⟩

end Silmaril.Semantics.TrackA.Interaction
