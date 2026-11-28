module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Traversal.Comparison.OrderedTables.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedTerminalTables

/-! # Native ordered-table replay and validated separation -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay.OrderedTables

open Silmaril
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open Paper.WithCaseBind.SelectedTerminal (Seed)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy

/-- The structural frame is determined by its input type. -/
theorem frame_eq {X : Ty Empty} (frame other : ReplyFrame X) : frame = other :=
  OrderedTerminalTables.frame_eq frame other

/-- Native replay of the recovered key at the original ordered interface. -/
theorem recovered_packed {L : List (Ty Empty)} {n : Nat} (p : SelectedAt (replyContext (n + 1)) L)
    (frameEq : p.frame = ReplyFrame.standard (n + 1)) (key : Finite.Normal L (n + 1))
    (found : recoverSplit p.split (frameEq ▸ p.slots) (ReplyFrame.standardSlots (n + 1)) = some key) :
    p.packedSource = (target key).packed :=
  OrderedTerminalTables.recovered_packed p frameEq key found

/-- The initial quote order lists distinct projections. -/
theorem standardSlots_injective (n : Nat) : Function.Injective (ReplyFrame.standardSlots n) :=
  OrderedTerminalTables.standardSlots_injective n

/-- Adding a reply preserves distinctness of the ordered fields. -/
theorem bindSlots_injective {X : Ty Empty} {frame : ReplyFrame X} {n : Nat}
    (slots : Fin n → ReplyFrame.Slot frame) (distinct : Function.Injective slots) :
    Function.Injective (ReplyFrame.bindSlots slots) :=
  OrderedTerminalTables.bindSlots_injective slots distinct

/-- A guard removes the tested field and preserves distinctness of the
untested projections and the fresh reply. -/
theorem guardSlots_injective {X : Ty Empty} {frame : ReplyFrame X} {n : Nat}
    (slots : Fin (n + 1) → ReplyFrame.Slot frame) (distinct : Function.Injective slots) (test : Fin (n + 1)) :
    Function.Injective (ReplyFrame.guardSlots slots test) :=
  OrderedTerminalTables.guardSlots_injective slots distinct test

/-- The test fact stays valid after forwarding the actual payload and
opening a fresh reply. -/
theorem guardFacts_hold {Γ : List (Ty Empty)} {X : Ty Empty} {frame : ReplyFrame X}
    {v : ReplyFrame.Value Γ frame} {known : CompactTerminal.Known frame} (valid : FactsHold known v)
    (slot : ReplyFrame.Slot frame) (tag reply : Bool) (chosen : (slot.read v).1 = tag) :
    FactsHold (guardFacts known slot tag) (extendReply (.unit v (slot.read v).2) reply) :=
  OrderedTerminalTables.guardFacts_hold valid slot tag reply chosen

/-- Replay both reply arms under their two actual constructor packets. -/
theorem request_regions_at {Γ : List (Ty Empty)} {X : Ty Empty} {frame : ReplyFrame X}
    {L : List (Ty Empty)} (emits : List Bool) (label : Bool) (v : ReplyFrame.Value Γ frame)
    {l r l' r' : Region signature.Instr}
    (hl : ValueBranches [product X Bit] l L) (hr : ValueBranches [product X Bit] r L)
    (hl' : ValueBranches [product X Bit] l' L) (hr' : ValueBranches [product X Bit] r' L)
    (left : ∀ b, Paper.Extension.Eqv Seed (unit :: Bit :: Γ)
      (l.substVars (Tm.singleSubst (extendReply v b).elaborate.val))
      (l'.substVars (Tm.singleSubst (extendReply v b).elaborate.val)) L)
    (right : ∀ b, Paper.Extension.Eqv Seed (unit :: Bit :: Γ)
      (r.substVars (Tm.singleSubst (extendReply v b).elaborate.val))
      (r'.substVars (Tm.singleSubst (extendReply v b).elaborate.val)) L) :
    Paper.Extension.Eqv Seed Γ ((KnownGuardTraversal.requestRegion
      (KnownGuardTraversal.requestTerm (X := X) emits label) l r).substVars (Tm.singleSubst v.elaborate.val))
      ((KnownGuardTraversal.requestRegion (KnownGuardTraversal.requestTerm (X := X) emits label) l' r').substVars
        (Tm.singleSubst v.elaborate.val)) L :=
  OrderedTerminalTables.request_regions_at emits label v hl hr hl' hr' left right

/-- Residual terminal rows agree on every constructor packet satisfying
the supplied facts about its exact structural projections. -/
theorem reindexWithFacts_sound {X : Ty Empty} {frame : ReplyFrame X} {Γ : List (Ty Empty)} {n m : Nat}
    (e : Finite.Expr m) (slots : Fin m → ReplyFrame.Slot frame)
    (kept : Fin n → ReplyFrame.Slot frame) (known : CompactTerminal.Known frame) (table : Finite.Table n)
    (found : reindexWithFacts? kept known e slots = some table) (v : ReplyFrame.Value Γ frame)
    (valid : FactsHold known v) :
    e.eval (fun j => ((slots j).read v).1) = table (fun j => ((kept j).read v).1) :=
  OrderedTerminalTables.reindexWithFacts_sound e slots kept known table found v valid

/-- Replay the recovered tree natively after substituting any exact
constructor frame that satisfies the incoming path facts. -/
theorem recoverTreeWithFacts_at {L : List (Ty Empty)} {X : Ty Empty} {frame : ReplyFrame X} {n m : Nat}
    (tree : ReadTree L m) (known : CompactTerminal.Known frame) (slots : Fin m → ReplyFrame.Slot frame)
    (kept : Fin n → ReplyFrame.Slot frame) (normal : Finite.Normal L n)
    (found : recoverTreeWithFacts tree known slots kept = some normal)
    {Γ : List (Ty Empty)} (v : ReplyFrame.Value Γ frame) (valid : FactsHold known v) :
    Paper.Extension.Eqv Seed Γ ((tree.selectedWith (fun j => (slots j).term)).elaborate.val.substVars
        (Tm.singleSubst v.elaborate.val))
      (((renderWith normal []).selectedWith (fun j => (kept j).term)).elaborate.val.substVars
        (Tm.singleSubst v.elaborate.val)) L :=
  OrderedTerminalTables.recoverTreeWithFacts_at tree known slots kept normal found v valid

/-- Recover a key from the original selected program and prove native equality
with its standard-order quotation. -/
@[expose] def admit? {L : List (Ty Empty)} : {n : Nat} → (p : SelectedAt (replyContext n) L) → Option (Admission p)
  | 0, _ => none
  | n + 1, p =>
    let frameEq := frame_eq p.frame (ReplyFrame.standard (n + 1))
    match found : recoverSplit p.split (frameEq ▸ p.slots) (ReplyFrame.standardSlots (n + 1)) with
    | some key => some ⟨key, recovered_packed p frameEq key found⟩
    | none => none

/-- Interpret the original packed arrow at the supplied assignment. -/
theorem Admission.observations_eq {L : List (Ty Empty)} {n : Nat} {p : SelectedAt (replyContext n) L}
    (a : Admission p) (env : Finite.Assignment n) :
    CanonicalLive.observations p env = a.key.outcomes env :=
  OrderedTerminalTables.observations_eq a env

/-- Equality of the single canonical key characterizes native equality at
the original endpoints. All terminal presentations share the same key type. -/
theorem key_eq_iff_packed {L : List (Ty Empty)} {n : Nat} {p q : SelectedAt (replyContext n) L}
    (l : Admission p) (r : Admission q) : l.key = r.key ↔ p.packedSource = q.packedSource :=
  ⟨fun eq => l.packed_eq.trans ((congrArg (fun key => (target key).packed) eq).trans r.packed_eq.symm),
    OrderedTerminalTables.key_eq_of_packed_eq l r⟩

/-- Exact comparison of the emitted quotations already decides native
equality for admitted sources. -/
theorem target_compare_iff_packed {L : List (Ty Empty)} {n : Nat} {p q : SelectedAt (replyContext n) L}
    (l : Admission p) (r : Admission q) :
    ((target l.key).compare (target r.key)).accepted = true ↔ p.packedSource = q.packedSource :=
  (ScopedTarget.compare_accepted_iff (target l.key) (target r.key)
    (AcyclicSyntax.selected_readable (renderWith l.key []).selected)).trans
    ⟨fun eq => l.packed_eq.trans ((congrArg ScopedTarget.packed eq).trans r.packed_eq.symm),
      fun eq => congrArg target ((key_eq_iff_packed l r).mpr eq)⟩

/-- Decide an admitted pair. Exact re-elaboration supplies the fast positive
case. An exhaustive trace search either supplies an input or identifies the
same ordered key, whose two native replay certificates yield equality. -/
@[expose] def compareAdmitted {L : List (Ty Empty)} {n : Nat} {p q : SelectedAt (replyContext n) L}
    (l : Admission p) (r : Admission q) : Decision p q :=
  match (target l.key).compare (target r.key) with
  | .equal same => .equal (l.packed_eq.trans ((congrArg ScopedTarget.packed same).trans r.packed_eq.symm))
  | .unknown =>
    match found : CanonicalLive.AssignmentSearch.normalDifference? l.key r.key with
    | some ⟨env, different⟩ => .different env (fun same =>
        different (Reply.Normal.outcomesWith_injective _ (Reply.Exits.Exit.packed_injective L)
          ((l.observations_eq env).symm.trans (same.trans (r.observations_eq env)))))
    | none => .equal ((key_eq_iff_packed l r).mp
        (Finite.Normal.traceTree_inj _ _ (CanonicalLive.AssignmentSearch.trace_agrees_of_no_difference _ _ found)))

/-- Distinct keys expose an actual distinguishing input in the validated model. -/
theorem key_ne_separated {L : List (Ty Empty)} {n : Nat} {p q : SelectedAt (replyContext n) L}
    (l : Admission p) (r : Admission q) (ne : l.key ≠ r.key) :
    ∃ env, CanonicalLive.observations p env ≠ CanonicalLive.observations q env :=
  match compareAdmitted l r with
  | .equal eq => False.elim (ne ((key_eq_iff_packed l r).mpr eq))
  | .different env diff => ⟨env, diff⟩

/-- Return a decision when both native recoveries succeed. -/
@[expose] def compare {L : List (Ty Empty)} {n : Nat} (p q : SelectedAt (replyContext n) L) :
    Option (Decision p q) := do
  let l ← admit? p
  let r ← admit? q
  pure (compareAdmitted l r)

/-- Executable comparison is complete on the recovered fragment. -/
theorem compare_isSome_iff {L : List (Ty Empty)} {n : Nat} (p q : SelectedAt (replyContext n) L) :
    (compare p q).isSome ↔ (admit? p).isSome ∧ (admit? q).isSome := by
  cases l : admit? p <;> cases r : admit? q <;> simp [compare, l, r]

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay.OrderedTables
