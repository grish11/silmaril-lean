module

public import Silmaril.Semantics.Region.Semantic.Defs

/-! # Targeted region-exit problems

Partial means conditional on a normal first exit; halts, divergence and
stuckness remain possible. Must means all runs must normally leave: internal
accessibility, progress, and exclusion of reachable halts are explicit. May
means a finite normal-exit witness exists. Labels alone carry no semantics;
the entry-only form still needs T, support and the admitted-state predicate.
-/

@[expose] public section
namespace Silmaril.Semantics.Region.Queries
universe u v w x
variable {S : Type u} {L : Type v} {Ev : Type w} {Stop : Type x}

def label (target : L) : S → L → Prop := fun _ l => l = target
def stateAt (target : L) (state : S) : S → L → Prop := fun s l => l = target ∧ s = state
def predicateAt (target : L) (post : S → Prop) : S → L → Prop := fun s l => l = target ∧ post s
def labels (targets : Set L) : S → L → Prop := fun _ l => l ∈ targets

def partialWP (T : TransitionSystem S L Ev Stop) (U : L → Prop) (target : S → L → Prop) (s : S) : Prop :=
  ∀ es t, FirstExit T U s es t → target t (T.pc t)

def mayWP (T : TransitionSystem S L Ev Stop) (U : L → Prop) (target : S → L → Prop) (s : S) : Prop :=
  ∃ es t, FirstExit T U s es t ∧ target t (T.pc t)

def noHalts (T : TransitionSystem S L Ev Stop) (U : L → Prop) (s : S) : Prop :=
  ∀ es t, Inside T U s es t → ∀ k, ¬ T.halt t k

def mustWP (T : TransitionSystem S L Ev Stop) (U : L → Prop) (target : S → L → Prop) (s : S) : Prop :=
  U (T.pc s) ∧ partialWP T U target s ∧ Finishes T U s ∧ noHalts T U s

/-- Region-level problems quantify over an explicit admitted state domain. -/
def region (problem : S → Prop) (admit : S → Prop) : Prop := ∀ s, admit s → problem s

/-- Entry-label-only query; the image, interface, support and operational
semantics are supplied by the surrounding problem, never recovered from l. -/
def atEntry (T : TransitionSystem S L Ev Stop) (admit : L → S → Prop) (problem : S → Prop) (entry : L) : Prop :=
  region problem (fun s => admit entry s ∧ T.pc s = entry)

end Silmaril.Semantics.Region.Queries
