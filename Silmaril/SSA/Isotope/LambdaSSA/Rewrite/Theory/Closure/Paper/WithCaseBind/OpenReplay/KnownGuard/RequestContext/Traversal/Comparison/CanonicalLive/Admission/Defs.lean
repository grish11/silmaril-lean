module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Traversal.Comparison.CanonicalLive.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Exits.Thms

/-! # Infer exact admission to the canonical live selected grammar -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay.CanonicalLive

open Silmaril CategoryTheory
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy
attribute [local instance] payloadInstrDecEq

namespace AdmissionParser

abbrev Syntax := AcyclicSyntax signature.Instr
abbrev Subst := Nat → Tm signature.Instr

/-- Enter a case arm with its original input and its newly bound payload. -/
def enter (outer : Subst) : Subst
  | 0 => .pair ((outer 0).rename Nat.succ) (.var 0)
  | i + 1 => (outer (i + 1)).rename Nat.succ

/-- Recover the emitted prefix of a selected discriminator or return term. -/
def readEmits : Tm signature.Instr → List Bool × Tm signature.Instr
  | .let₁ (.pair (.op (.emit label) .unit) next) (.let₂ (.var 0) (.var 0)) =>
    let (labels, body) := readEmits next
    (label :: labels, body)
  | body => ([], body)

/-- Read a direct exit or a bit tag attached to the bound unit payload. -/
def readExit : Syntax → Option (Nat × Option Bool)
  | .br label (.var 0) => some (label, none)
  | .br label (.inl (.var 0)) => some (label, some false)
  | .br label (.inr (.var 0)) => some (label, some true)
  | .let₁ _ body => readExit body
  | _ => none

def readReturnEmits : Syntax → List Bool
  | .let₁ (.pair (.op (.emit label) .unit) next) _ => label :: (readEmits next).1
  | .let₁ value _ => (readEmits value).1
  | _ => []

def readReturn {L : List (Ty Empty)} {n : Nat} {X : Ty Empty}
    (slots : Fin n → Term signature.Instr X Bit) (subst : Subst) (node : Syntax) :
    Option (CanonicalLive L n) := do
  let (label, tag) ← readExit node
  let pos ← (List.finRange L.length).findSome? fun i =>
    if h : i.val = label ∧ L.get i = Bit then some (⟨i, h.2⟩ : Position L) else none
  let emits := readReturnEmits node
  let matchesTerminal (result : Finite.Expr n) :=
    let compiled := selectTerminal pos result slots emits
    let key := (AcyclicSyntax.read (compiled.elaborate.val.substVars subst)).map Subtype.val
    key == some node
  let terminal ← match tag with
    | none => do
      let slot ← (List.finRange n).find? fun i => matchesTerminal (.read i)
      some (.ret pos slot)
    | some bit => if matchesTerminal (.literal bit) then some (.literal pos bit) else none
  pure (emits.foldr CanonicalLive.emit terminal)

def decode {L : List (Ty Empty)} (node : Syntax) {n : Nat} {X : Ty Empty}
    (slots : Fin n → Term signature.Instr X Bit) (subst : Subst) : Option (CanonicalLive L n) :=
  match node with
  | .case discr left right =>
    let (emits, body) := readEmits discr
    match body with
    | .op (.ask label) .unit => do
      let l ← decode left (bindReply slots) (enter subst)
      let r ← decode right (bindReply slots) (enter subst)
      pure (emits.foldr CanonicalLive.emit (.request label l r))
    | _ =>
      match n, left, right with
      | k + 1, .case (.op (.ask low) .unit) fl fr, .case (.op (.ask high) .unit) tl tr => do
        if high != !low then none else
          let test ← (List.finRange (k + 1)).find? fun i =>
            ((slots i).elaborate.val.subst subst) == body
          let next := guardReplies slots test
          let inner := enter (enter subst)
          let fl ← decode fl next inner
          let fr ← decode fr next inner
          let tl ← decode tl next inner
          let tr ← decode tr next inner
          pure (emits.foldr CanonicalLive.emit (.guard test low fl fr tl tr))
      | _, _, _ => none
  | _ => readReturn slots subst node
termination_by structural node

end AdmissionParser

/-- A recovered tree and its exact elaboration at the original typed interface. -/
structure Admission {L : List (Ty Empty)} {n : Nat} (target : ScopedTarget (replyContext n) L) where
  tree : CanonicalLive L n
  target_eq : target = tree.target

/-- Read the normalized region with its standard logical slots, then check
the entire re-elaborated syntax at the original typed input and exits. -/
def admit? {L : List (Ty Empty)} {n : Nat} (target : ScopedTarget (replyContext n) L) :
    Option (Admission target) := do
  let key ← AcyclicSyntax.read target.val
  let tree ← AdmissionParser.decode key.val (readReply n) Tm.var
  match target.compare tree.target with
  | .equal exactTarget => some ⟨tree, exactTarget⟩
  | .unknown => none

/-- Infer admission from the selected source’s projection-canonical target. -/
def admitSelected? {L : List (Ty Empty)} {n : Nat} (p : SelectedAt (replyContext n) L) :
    Option (Admission p.projectionCanonical) :=
  admit? p.projectionCanonical

/-- An exact admission also identifies the source target's readback key. -/
theorem Admission.readback_eq {L : List (Ty Empty)} {n : Nat} {target : ScopedTarget (replyContext n) L}
    (a : Admission target) : (AcyclicSyntax.read target.val).map Subtype.val = a.tree.readback :=
  congrArg (fun (t : ScopedTarget (replyContext n) L) => (AcyclicSyntax.read t.val).map Subtype.val) a.target_eq

namespace AssignmentSearch

deriving instance DecidableEq for Reply.Normal

/-- The finite assignments in order, with the newest bit as the outer choice. -/
def assignments : (n : Nat) → List (Finite.Assignment n)
  | 0 => [Fin.elim0]
  | n + 1 => (assignments n).map (fun env => env.push false) ++
      (assignments n).map (fun env => env.push true)

@[instance_reducible]
def valueDecEq : (A : Ty Empty) → DecidableEq (Kleisli.value A)
  | .base a => a.elim
  | .unit => inferInstanceAs (DecidableEq PUnit)
  | .empty => inferInstanceAs (DecidableEq PEmpty)
  | .product A B =>
    letI := valueDecEq A
    letI := valueDecEq B
    inferInstanceAs (DecidableEq (Kleisli.value A × Kleisli.value B))
  | .coprod A B =>
    letI := valueDecEq A
    letI := valueDecEq B
    inferInstanceAs (DecidableEq (Kleisli.value A ⊕ Kleisli.value B))

local instance {L : List (Ty Empty)} : DecidableEq (Reply.Exits.Exit L) :=
  letI : ∀ i : Fin L.length, DecidableEq (Kleisli.value (L.get i)) := fun i => valueDecEq (L.get i)
  inferInstanceAs (DecidableEq (Σ i : Fin L.length, Kleisli.value (L.get i)))

/-- Search typed exit payloads and the full tagged trace on each input. -/
def normalDifference? {L : List (Ty Empty)} {n : Nat} (p q : Finite.Normal L n) :
    Option {env : Finite.Assignment n // p.traceTree env ≠ q.traceTree env} :=
  (assignments n).findSome? fun env =>
    if h : p.traceTree env ≠ q.traceTree env then some ⟨env, h⟩ else none

def difference? {L : List (Ty Empty)} {n : Nat} (p q : CanonicalLive L n) :
    Option {env : Finite.Assignment n // p.normal.traceTree env ≠ q.normal.traceTree env} :=
  normalDifference? p.normal q.normal

end AssignmentSearch

/-- The validated observation on the original packed source at a named input. -/
noncomputable def observations {L : List (Ty Empty)} {n : Nat}
    (p : SelectedAt (replyContext n) L) (env : Finite.Assignment n) :=
  ((payloadDenote.map p.packedSource).of (replyInput n env)).outcomes

/-- Exact admission identifies the packed original with the recovered tree. -/
theorem Admission.packed_eq {L : List (Ty Empty)} {n : Nat} {p : SelectedAt (replyContext n) L}
    (a : Admission p.projectionCanonical) : p.packedSource = a.tree.target.packed :=
  p.packed_projectionCanonical.trans (congrArg ScopedTarget.packed a.target_eq)

/-- Exact admission lets the existing model proof evaluate the original arrow. -/
theorem Admission.observations_eq {L : List (Ty Empty)} {n : Nat}
    {p : SelectedAt (replyContext n) L} (a : Admission p.projectionCanonical) (env : Finite.Assignment n) :
    observations p env = a.tree.normal.outcomes env := by
  exact (congrArg (fun arrow => ((payloadDenote.map arrow).of (replyInput n env)).outcomes)
    a.packed_eq).trans (a.tree.map_outcomes env)

/-- A positive native witness, a validated input with both admission proofs,
or an unknown result. A readback mismatch alone cannot construct separation. -/
inductive Verdict {L : List (Ty Empty)} {n : Nat} (p q : SelectedAt (replyContext n) L) where
  | equal (proof : p.packedSource = q.packedSource)
  | different (left : Admission p.projectionCanonical) (right : Admission q.projectionCanonical)
      (input : Finite.Assignment n) (proof : observations p input ≠ observations q input)
  | unknown

/-- Use exact normalized equality first. A distinguishing decision requires
two admissions and a checked tagged trace difference at an explicit input. -/
def compareSelected {L : List (Ty Empty)} {n : Nat} (p q : SelectedAt (replyContext n) L) : Verdict p q :=
  match p.compareProjectionQuotes q with
  | .equal proof => .equal proof
  | .unknown => Id.run do
    let some left := admitSelected? p | return .unknown
    let some right := admitSelected? q | return .unknown
    let some input := AssignmentSearch.difference? left.tree right.tree | return .unknown
    return .different left right input.val (by
      rw [left.observations_eq, right.observations_eq]
      exact fun same => input.property (Reply.Normal.outcomesWith_injective _ (Reply.Exits.Exit.packed_injective L) same))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay.CanonicalLive
