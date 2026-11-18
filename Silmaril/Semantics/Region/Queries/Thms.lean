module

public import Silmaril.Semantics.Region.Queries.Defs
import Silmaril.Proofs.Semantics.Region.Queries

@[expose] public section
namespace Silmaril.Semantics.Region.Queries
universe u v w x
variable {S : Type u} {L : Type v} {Ev : Type w} {Stop : Type x}
variable {T : TransitionSystem S L Ev Stop} {U : L → Prop}

theorem exit_outside {s t : S} {es : List Ev} (h : FirstExit T U s es t) : ¬ U (T.pc t) :=
  Proofs.exit_outside h

/-- Universal first-exit queries are weakest preconditions for the chosen
normal-exit observation. This says nothing about excluded halt outcomes. -/
theorem partial_weakest {A : S → Prop} {target : S → L → Prop} :
    region (partialWP T U target) A ↔
      ∀ s es t, A s → FirstExit T U s es t → target t (T.pc t) :=
  ⟨fun h s es t ha => h s ha es t, fun h s ha es t => h s es t ha⟩

theorem partial_mono {P Q : S → L → Prop} (h : ∀ s l, P s l → Q s l) {s : S}
    (wp : partialWP T U P s) : partialWP T U Q s := fun es t exits => h t _ (wp es t exits)

theorem may_mono {P Q : S → L → Prop} (h : ∀ s l, P s l → Q s l) {s : S}
    (wp : mayWP T U P s) : mayWP T U Q s :=
  let ⟨es, t, exits, hp⟩ := wp; ⟨es, t, exits, h t _ hp⟩

theorem must_implies_may {target : S → L → Prop} {s : S} (h : mustWP T U target s) : mayWP T U target s :=
  Proofs.must_may h

theorem must_implies_partial {target : S → L → Prop} {s : S} (h : mustWP T U target s) : partialWP T U target s :=
  h.2.1

theorem exact_state_implies_label {l : L} {state s : S} (h : partialWP T U (stateAt l state) s) :
    partialWP T U (label l) s := fun es t exits => (h es t exits).1

theorem predicate_implies_label {l : L} {post : S → Prop} {s : S} (h : partialWP T U (predicateAt l post) s) :
    partialWP T U (label l) s := fun es t exits => (h es t exits).1

theorem singleton_labels {l : L} {s : S} : partialWP T U (labels {l}) s ↔ partialWP T U (label l) s := Iff.rfl

/-- An existing partial Hoare triple also controls halts; these normal-target
queries deliberately expose a weaker observation, without relabeling halts. -/
theorem of_partial_hoare {A : S → Prop} {target : S → L → Prop}
    {R : Stop → List Ev → S → Prop}
    (h : PartialHoare T A U (fun l _ s => target s l) R) : region (partialWP T U target) A := fun s hs es t exits => h.1 s es t hs exits

end Silmaril.Semantics.Region.Queries
