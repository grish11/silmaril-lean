module

public import Silmaril.Compiler.Explorer.Defs

/-!
# Text-file problems: the primary form, with or without semantics

The explorer's primary problem is about **files**: some source files, some target files, and a
relation between them. Nothing here requires a semantics.

* `Files`: an immutable map from file names to bytes (the database content-addresses each file).
* `IncludeEnv`: what a C preprocessor reads besides the main file: the files it may include,
  the search order, the predefined macros and the compiler options. A formal preprocessor would
  be a `Stage` from `(IncludeEnv × Files)` to the preprocessed text; none exists yet.
* `Stage α β`: one step of a pipeline (parse, preprocess, elaborate, disassemble, lower), a
  partial function with a name and a trust tag. A stage's exact output is an artifact the
  explorer shows next to its input; a trusted stage is later replaced by a verified one or by a
  translation-validation problem of its own (`Stage.validated`).
* `RelProblem α β`: an arbitrary proposition-valued relation, not necessarily about execution.
  `Segments` independently gives a relation on selected fragments. A receipt without even a
  Lean proposition is recorded separately (`Semantics.none`).
* `Reading`: the semantic specialisation. Parse each side with a stage, and relate the results
  by a compilation `Problem` (`Silmaril.Compiler.Explorer.Problem`); `Reading.toRel` is the
  induced relation on files. A `SegmentDiscipline` is an optional execution-based specialization,
  not a prerequisite for a relation on fragments.
-/

@[expose] public section

namespace Silmaril.Compiler.Explorer

/-- An immutable map from file names to bytes; the first entry with a name wins. -/
abbrev Files := List (String × List UInt8)

/-- The bytes of a file. -/
def Files.read (fs : Files) (name : String) : Option (List UInt8) := fs.lookup name

/-- **A preprocessor's environment**: the files it may include, the directories searched in
order, the predefined macros (`none`: defined without a value) and the compiler options. -/
structure IncludeEnv where
  files : Files
  search : List String
  macros : List (String × Option String)
  options : List String

/-- How far a stage is to be trusted. -/
inductive Trust where
  /-- Its output is checked by the kernel against its input (a theorem). -/
  | verified
  /-- Its output is checked by compiled evaluation (`#guard`), not by the kernel. -/
  | evaluated
  /-- Its output is used as given (an external tool, an unverified reader). -/
  | trusted
  deriving Repr, DecidableEq

/-- **A stage**: a named partial function, with its trust. -/
structure Stage (α β : Type) where
  name : String
  trust : Trust
  run : α → Except String β

/-- Run one stage, then another; the composite is as trusted as its least trusted part. -/
def Stage.comp {α β γ : Type} (f : Stage α β) (g : Stage β γ) : Stage α γ where
  name := f.name ++ " ; " ++ g.name
  trust := if f.trust = .verified ∧ g.trust = .verified then .verified
    else if f.trust = .trusted ∨ g.trust = .trusted then .trusted else .evaluated
  run a := f.run a >>= g.run

/-- **A stage validated against a relation**: every output is related to its input. The
translation-validation problem of a trusted stage. -/
def Stage.validated {α β : Type} (f : Stage α β) (R : α → β → Prop) : Prop :=
  ∀ a b, f.run a = .ok b → R a b

/-- Relate inputs via two independently chosen stages. A failed stage does not witness the pullback. -/
def Stage.pullback {α β σ τ : Type} (source : Stage α σ) (target : Stage β τ)
    (Rel : σ → τ → Prop) (a : α) (b : β) : Prop :=
  ∃ s t, source.run a = .ok s ∧ target.run b = .ok t ∧ Rel s t

/-- **An arbitrary relation problem**: a source, a target and a relation; nothing more. -/
structure RelProblem (α β : Type) where
  source : α
  target : β
  Rel : α → β → Prop

/-- The problem's statement. -/
def RelProblem.Statement {α β : Type} (P : RelProblem α β) : Prop := P.Rel P.source P.target

/-- Pointwise refinement of relations, independent of any execution model. -/
def RelProblem.Refines {α β : Type} (narrow wide : α → β → Prop) : Prop :=
  ∀ a b, narrow a b → wide a b

/-- An independently selected relation on fragments of the two artifacts. -/
structure RelProblem.Segments {α β : Type} (P : RelProblem α β) (σ τ : Type) where
  sourceSegment : σ → α → Prop
  targetSegment : τ → β → Prop
  Rel : σ → τ → Prop

/-- A segment claim requires membership on both sides, not a claim about executions or coverage. -/
def RelProblem.Segments.Holds {α β σ τ : Type} {P : RelProblem α β}
    (segs : P.Segments σ τ) (s : σ) (t : τ) : Prop :=
  segs.sourceSegment s P.source ∧ segs.targetSegment t P.target ∧ segs.Rel s t

/-- A map preserving the relation and sending the chosen pair to the chosen pair. -/
structure RelProblem.Morphism {α β σ τ : Type} (P : RelProblem α β) (Q : RelProblem σ τ) where
  sourceMap : α → σ
  targetMap : β → τ
  onSource : sourceMap P.source = Q.source
  onTarget : targetMap P.target = Q.target
  preserves : ∀ a b, P.Rel a b → Q.Rel (sourceMap a) (targetMap b)

/-- The identity maps preserve a problem. -/
def RelProblem.Morphism.identity {α β : Type} (P : RelProblem α β) : P.Morphism P :=
  ⟨id, id, rfl, rfl, fun _ _ related => related⟩

/-- Compose maps on each side, and compose their preservation proofs. -/
def RelProblem.Morphism.comp {α β σ τ γ δ : Type}
    {P : RelProblem α β} {Q : RelProblem σ τ} {R : RelProblem γ δ}
    (first : P.Morphism Q) (next : Q.Morphism R) : P.Morphism R where
  sourceMap := next.sourceMap ∘ first.sourceMap
  targetMap := next.targetMap ∘ first.targetMap
  onSource := (congrArg next.sourceMap first.onSource).trans next.onSource
  onTarget := (congrArg next.targetMap first.onTarget).trans next.onTarget
  preserves a b related := next.preserves _ _ (first.preserves a b related)

/-- What is known of a statement: proved, refuted (its negation proved) or unknown. -/
inductive Verdict (p : Prop) where
  | proved : p → Verdict p
  | refuted : ¬ p → Verdict p
  | unknown : Verdict p

/-- Whether a relation has a semantics in Lean. -/
inductive Semantics where
  /-- No semantics: the relation is recorded (a receipt, a debug table) but not stated. -/
  | none
  /-- A Lean statement (`decl` names it) relates the two sides. -/
  | stated (decl : String)
  deriving Repr, DecidableEq

/-- **A semantic reading** of files: parse each side by a stage, then relate the parses by a
compilation problem built from them. -/
structure Reading (α β σ τ R T : Type) where
  parseSource : Stage α σ
  parseTarget : Stage β τ
  problem : σ → τ → Problem σ τ R T

/-- **The relation a reading induces** on files: both sides parse, and the problem of their
parses is refined. A side that does not parse is not related. -/
def Reading.toRel {α β σ τ R T : Type} (r : Reading α β σ τ R T) (a : α) (b : β) : Prop :=
  Stage.pullback r.parseSource r.parseTarget (fun s t => (r.problem s t).Refines) a b

end Silmaril.Compiler.Explorer

end
