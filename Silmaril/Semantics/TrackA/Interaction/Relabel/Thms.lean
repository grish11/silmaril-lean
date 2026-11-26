module

public import Silmaril.Semantics.TrackA.Interaction.Relabel.Defs
public import Silmaril.Semantics.TrackA.Interaction.UB.Thms
import Silmaril.Proofs.Semantics.TrackA.Interaction.Relabel.Observes
import Silmaril.Proofs.Semantics.TrackA.Interaction.Relabel.Laws

@[expose] public section

namespace Silmaril.Semantics.TrackA.Interaction

universe u v w x y z a b d s i k l

variable {S : Signature.{u,v}} {T : Signature.{w,x}} {U : Signature.{y,z}} {V : Signature.{k,l}}
  {A : Type a} {B : Signature.{b,d}} {I : Type i} {X : Type*}

theorem Signature.Hom.comp_assoc (f : Signature.Hom S T) (g : Signature.Hom T U)
    (h : Signature.Hom U V) : (h.comp g).comp f = h.comp (g.comp f) := rfl

@[simp] theorem Trace.relabel_id (t : Trace S A) :
    t.relabel (Signature.TraceHom.id S) = t :=
  Proofs.Semantics.TrackA.Interaction.Relabel.trace_id t

theorem Trace.relabel_comp (f : Signature.TraceHom S T) (g : Signature.TraceHom T U)
    (t : Trace S A) : t.relabel (g.comp f) = (t.relabel f).relabel g :=
  Proofs.Semantics.TrackA.Interaction.Relabel.trace_comp f g t

@[simp] theorem Forest.relabel_id (forest : Forest S B A I) :
    forest.relabel (Signature.Hom.id S) = forest := by
  cases forest with | mk state unfold root =>
    exact congrArg (fun layers => (⟨state, layers, root⟩ : Forest S B A I))
      (funext fun x => Node.relabel_id (unfold x))

theorem Forest.relabel_comp (f : Signature.Hom S T) (g : Signature.Hom T U)
    (forest : Forest S B A I) : forest.relabel (g.comp f) = (forest.relabel f).relabel g := by
  cases forest with | mk state unfold root =>
    exact congrArg (fun layers => (⟨state, layers, root⟩ : Forest U B A I))
      (funext fun x => Node.relabel_comp f g (unfold x))

/-- Relabeling transports actual finite and infinite observations along their
state paths. The target may identify observations with different requests. -/
theorem Coalgebra.observes_relabel (f : Signature.TraceHom S T) (c : Coalgebra S B A X)
    (state : X) : (c.relabel f.hom).observes state = Trace.relabel f '' c.observes state :=
  Proofs.Semantics.TrackA.Interaction.Relabel.coalgebra_observes f c state

theorem Forest.observes_relabel (f : Signature.TraceHom S T)
    (forest : Forest.{u,v,b,d,a,i,s} S B A I) :
    (forest.relabel f.hom).observes = Trace.relabel f '' forest.observes :=
  Proofs.Semantics.TrackA.Interaction.Relabel.forest_observes f forest

theorem UB.classify_relabel (f : Signature.TraceHom S T) (t : Trace S (Option A)) :
    classify (t.relabel f) = (classify t).map (Trace.relabel f) :=
  Proofs.Semantics.TrackA.Interaction.Relabel.classify_relabel f t

theorem UB.atBoundary_relabel (f : Signature.TraceHom S T) (runs : Set (Trace S (Option A))) :
    atBoundary (Trace.relabel f '' runs) = Option.map (Trace.relabel f) '' atBoundary runs :=
  Proofs.Semantics.TrackA.Interaction.Relabel.atBoundary_relabel f runs

/-- UB at the boundary witnesses an actual completed run returning the UB marker. -/
theorem UB.atBoundary_ub_iff (runs : Set (Trace S (Option A))) :
    none ∈ atBoundary runs ↔ ∃ events, Trace.finite events (.returned none) ∈ runs :=
  Proofs.Semantics.TrackA.Interaction.Relabel.boundary_ub_iff runs

/-- Extract the ordinary complete observations and the whole-run UB marker. -/
def Forest.toExplicit (forest : Forest S B (Option A) I) : UB.Explicit (Trace S A) :=
  UB.atBoundary forest.observes

/-- The saturated whole-run behavior is an overapproximation at the UB boundary. -/
def Forest.toCatastrophic (forest : Forest S B (Option A) I) : UB.Catastrophic (Trace S A) :=
  UB.collapse forest.toExplicit

theorem Forest.toExplicit_relabel (f : Signature.TraceHom S T)
    (forest : Forest.{u,v,b,d,a,i,s} S B (Option A) I) :
    (forest.relabel f.hom).toExplicit = Option.map (Trace.relabel f) '' forest.toExplicit := by
  simp only [Forest.toExplicit, Forest.observes_relabel, UB.atBoundary_relabel]

theorem Forest.toExplicit_subset_catastrophic (forest : Forest S B (Option A) I) :
    forest.toExplicit ⊆ forest.toCatastrophic.val := fun _ h => Or.inl h

theorem Forest.toCatastrophic_val_of_safe (forest : Forest S B (Option A) I)
    (safe : none ∉ forest.toExplicit) : forest.toCatastrophic.val = forest.toExplicit :=
  UB.val_collapse_of_safe _ safe

theorem Forest.toCatastrophic_eq_top_iff (forest : Forest S B (Option A) I) :
    forest.toCatastrophic = ⊤ ↔ none ∈ forest.toExplicit := UB.collapse_eq_top_iff _

end Silmaril.Semantics.TrackA.Interaction
