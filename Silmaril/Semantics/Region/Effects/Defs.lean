module

public import Silmaril.Semantics.Region.Semantic.Defs
public import Mathlib.Order.CompleteLattice.Basic

/-! # Abstract may-effect upper envelopes

Observation and coverage belong to an interpretation, outside the positive
region-law lattice. The complete lattice can be a powerset, product, or a
coarser domain with Top; no finite enumeration or basic-block partition is
required. Bounds below describe possible effects, never mandatory effects.
-/

@[expose] public section
namespace Silmaril.Semantics.Region.Effects
universe u v w x y
variable {S : Type u} {L : Type v} {Ev : Type w} {Stop : Type x} {E : Type y}

/-- Least sound upper bound of every observable effect of every admitted
internal prefix or boundary-crossing step. Diverging prefixes are included. -/
noncomputable def envelope [CompleteLattice E] (T : TransitionSystem S L Ev Stop)
    (A : S → Prop) (U : L → Prop) (observe : Ev → E) : E :=
  ⨆ e, ⨆ (_ : MayEffect T A U e), observe e

def SoundBound [LE E] (T : TransitionSystem S L Ev Stop) (A : S → Prop)
    (U : L → Prop) (observe : Ev → E) (bound : E) : Prop :=
  ∀ e, MayEffect T A U e → observe e ≤ bound

/-- Must effects quantify over an explicitly chosen outcome/trace family.
The separate witness prevents vacuity when the chosen family is empty;
termination/divergence policy is the client's choice of `runs`. -/
def MustOccur (runs : List Ev → Prop) (e : Ev) : Prop :=
  (∃ es, runs es) ∧ ∀ es, runs es → e ∈ es

/-- Observable steps and reachable distinguished halts. This includes an
abnormal halt that has no outgoing step and emits no direct event. -/
def MayObservation (T : TransitionSystem S L Ev Stop) (A : S → Prop)
    (U : L → Prop) : Sum Ev Stop → Prop
  | .inl e => MayEffect T A U e
  | .inr k => ∃ s es t, A s ∧ Inside T U s es t ∧ T.halt t k

noncomputable def outcomeEnvelope [CompleteLattice E] (T : TransitionSystem S L Ev Stop)
    (A : S → Prop) (U : L → Prop) (observe : Sum Ev Stop → E) : E :=
  ⨆ o, ⨆ (_ : MayObservation T A U o), observe o

/-- Open effect alphabet: categories and their payload domains are supplied
independently. A client can extend the category type without changing this API. -/
abbrev Atom {Kind : Type u} (Payload : Kind → Type v) := Sigma Payload

/-- Projection at one category; no common payload type is required. -/
def atKind {Kind : Type u} {Payload : Kind → Type v}
    (effects : Set (Atom Payload)) (kind : Kind) : Set (Payload kind) :=
  {value | ⟨kind, value⟩ ∈ effects}

/-- A reusable direct-observation vocabulary, not a closed core signature.
`call` records the instruction's own call event, not the callee's effects.
UB and abnormal outcomes are explicit observations, never empty effects.
Use/def summaries are deliberately separate. -/
inductive DirectKind where
  | clobber | read | write | instruction | call | syscall | ub | trap | fault | raise
  deriving DecidableEq

/-- Category and payload maps together support changing observation domains. -/
structure Renaming {K : Type u} {H : Type w}
    (P : K → Type v) (Q : H → Type x) where
  kind : K → H
  payload : ∀ k, P k → Q (kind k)

def Renaming.atom {K : Type u} {H : Type w} {P : K → Type v} {Q : H → Type x}
    (f : Renaming P Q) (a : Atom P) : Atom Q := ⟨f.kind a.1, f.payload a.1 a.2⟩

def Renaming.map {K : Type u} {H : Type w} {P : K → Type v} {Q : H → Type x}
    (f : Renaming P Q) (effects : Set (Atom P)) : Set (Atom Q) := f.atom '' effects

def Renaming.id {K : Type u} (P : K → Type v) : Renaming P P := ⟨fun k => k, fun _ x => x⟩

def Renaming.then {K : Type u} {H : Type w} {J : Type*}
    {P : K → Type v} {Q : H → Type x} {R : J → Type*}
    (f : Renaming P Q) (g : Renaming Q R) : Renaming P R :=
  ⟨g.kind ∘ f.kind, fun k => g.payload (f.kind k) ∘ f.payload k⟩

/-- Upward-exposed uses need definite definitions to kill later uses. A
may-clobber/write set is not a valid substitute for `definiteDefs`. -/
structure UseDef (R : Type u) where
  uses : Set R
  definiteDefs : Set R

def UseDef.sequence {R : Type u} (a b : UseDef R) : UseDef R :=
  ⟨a.uses ∪ (b.uses \ a.definiteDefs), a.definiteDefs ∪ b.definiteDefs⟩
def UseDef.selection {R : Type u} (a b : UseDef R) : UseDef R :=
  ⟨a.uses ∪ b.uses, a.definiteDefs ∩ b.definiteDefs⟩

/-- Signature packaging keeps block APIs at one explicit signature argument.
The indexed alphabet itself remains open and independent of this packaging. -/
structure BlockSignature where
  Kind : Type u
  Payload : Kind → Type v
  Register : Type w
  Control : Type x

/-- Direct means effects of this instruction, excluding effects reached through
calls. `useDef` is a transfer summary; `control` describes the instruction's
own normal successors and abnormal outcomes under a chosen policy. -/
structure InstructionSummary (sig : BlockSignature.{u, v, w, x}) where
  direct : Set (Atom sig.Payload)
  useDef : UseDef sig.Register
  control : Set sig.Control

/-- Sequential summary where the left instruction is certified to fall through.
Only the right summary contributes control flow. This operation alone asserts
no fallthrough, execution coverage, or absence of interior faults. -/
def InstructionSummary.prepend {sig : BlockSignature} (a b : InstructionSummary sig) :
    InstructionSummary sig :=
  ⟨a.direct ∪ b.direct, a.useDef.sequence b.useDef, b.control⟩

/-- Nonempty block shape: a body followed by a final instruction. A final
ordinary instruction may have a fallthrough successor; it need not branch. -/
structure Block (I : Type u) where
  body : List I
  final : I

def Block.effects {I : Type*} {sig : BlockSignature}
    (analyze : I → InstructionSummary sig) (b : Block I) : InstructionSummary sig :=
  b.body.foldr (fun i tail => (analyze i).prepend tail) (analyze b.final)

/-- Adapter-specific soundness predicates. `interior` must justify reaching the
next instruction with no escaping control outcome under the adapter's policy.
For a policy observing faults/traps/UB, this excludes or explicitly discharges
such interior escapes. Call summaries need their own resumption justification. -/
structure BlockContract (I : Type u) (sig : BlockSignature) where
  analyze : I → InstructionSummary sig
  interior : I → Prop
  directSound : I → Set (Atom sig.Payload) → Prop
  controlSound : I → Set sig.Control → Prop

/-- Proof decoration, outside the positive region-model lattice. These are
certificates relative to the supplied contract, not an implicit ISA theorem. -/
structure CertifiedBlock {I : Type*} {sig : BlockSignature} (c : BlockContract I sig) where
  block : Block I
  interior : ∀ i ∈ block.body, c.interior i
  direct : ∀ i ∈ block.body ++ [block.final], c.directSound i (c.analyze i).direct
  control : c.controlSound block.final (c.analyze block.final).control

def CertifiedBlock.effects {I : Type*} {sig : BlockSignature} {c : BlockContract I sig}
    (b : CertifiedBlock c) : InstructionSummary sig := b.block.effects c.analyze

/-- A possible control outcome is distinct from a direct instruction effect.
Normal fallthrough is `next`; trap/fault/UB/raise/return can be distinguished
`halt` values. An adapter may additionally emit a corresponding direct event. -/
inductive ControlOutcome (Lab : Type u) (Stop : Type v) where
  | next (label : Lab)
  | halt (reason : Stop)

def ControlBound (T : TransitionSystem S L Ev Stop) (A : S → Prop)
    (U : L → Prop) (bound : Set (ControlOutcome L Stop)) : Prop :=
  Sound T A U (fun l => .next l ∈ bound) ∧
    ∀ s es t k, A s → Inside T U s es t → T.halt t k → .halt k ∈ bound

end Silmaril.Semantics.Region.Effects
