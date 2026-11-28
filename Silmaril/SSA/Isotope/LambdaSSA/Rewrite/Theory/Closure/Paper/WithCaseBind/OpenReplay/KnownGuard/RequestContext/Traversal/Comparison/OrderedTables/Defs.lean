module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Traversal.Comparison.Compact.Thms

/-! # Canonical ordered truth tables for selected programs -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay.OrderedTables

open Silmaril
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy

/-- Each terminal gets the full quote of one Boolean table, including
constant and projection results. The existing normal form records effects,
reply choices, and ordered typed exits. -/
def renderWith {L : List (Ty Empty)} : {n : Nat} → Finite.Normal L n → List Bool → ReadTree L n
  | n, .ret pos table, emits => .retExpr emits pos (Finite.Expr.quote n table)
  | _, .emit bit next, emits => renderWith next (emits ++ [bit])
  | _, .request label l r, emits => .request emits label false (renderWith l []) (renderWith r [])
  | _, .testRequest test low fl fr tl tr, emits =>
    .testRequest emits test low false false
      (renderWith fl []) (renderWith fr []) (renderWith tl []) (renderWith tr [])

def target {L : List (Ty Empty)} {n : Nat} (p : Finite.Normal L n) : ScopedTarget (replyContext n) L :=
  (renderWith p []).selected.elaborate

/-- Locate the very same typed projection in the retained order. -/
def locate {X : Ty Empty} {frame : ReplyFrame X} {n : Nat}
    (slots : Fin n → ReplyFrame.Slot frame) (slot : ReplyFrame.Slot frame) : Option (Fin n) :=
  letI := ReplyFrame.Slot.decEq frame
  (List.finRange n).find? fun j => decide (slots j = slot)

theorem rename_branch {Γ Δ : List (Ty Empty)} {ρ : Nat → Nat} (hρ : Ren Γ Δ ρ)
    {a : Tm signature.Instr} {X : Ty Empty} (h : Tm.BranchValue Γ a X) :
    Tm.BranchValue Δ (a.rename ρ) X := by
  rw [Tm.rename_eq_subst]
  exact h.subst (fun _ _ hi => .var (hρ hi))

def renameFrame {Γ Δ : List (Ty Empty)} {ρ : Nat → Nat} (hρ : Ren Γ Δ ρ) :
    {X : Ty Empty} → {frame : ReplyFrame X} → ReplyFrame.Value Γ frame → ReplyFrame.Value Δ frame
  | _, _, .base u => .base ⟨_, rename_branch hρ u.property⟩
  | _, _, .unit v u => .unit (renameFrame hρ v) ⟨_, rename_branch hρ u.property⟩
  | _, _, .bit v b u => .bit (renameFrame hρ v) b ⟨_, rename_branch hρ u.property⟩

/-- The complete constructor packet in a selected reply arm after opening
the Bit variable with its fresh unit payload. -/
def extendReply {Γ : List (Ty Empty)} {X : Ty Empty} {frame : ReplyFrame X}
    (v : ReplyFrame.Value Γ frame) (b : Bool) : ReplyFrame.Value (unit :: Bit :: Γ) (.bit frame) :=
  .bit (renameFrame ((Ren.wk Γ Bit).comp (Ren.wk (Bit :: Γ) unit)) v) b ⟨.var 0, .var rfl⟩

/-- A new reply exposes a fresh field and carries facts about older fields. -/
def replyFacts {X : Ty Empty} {frame : ReplyFrame X} (known : CompactTerminal.Known frame) :
    CompactTerminal.Known (.bit frame)
  | .newest _ => none
  | .retainBit slot => known slot

/-- A selected guard binds the original unit payload, then its request binds
a fresh reply. Remember the tag of the tested projection in the older frame. -/
def guardFacts {X : Ty Empty} {frame : ReplyFrame X} (known : CompactTerminal.Known frame)
    (slot : ReplyFrame.Slot frame) (tag : Bool) : CompactTerminal.Known (.bit (.unit frame)) :=
  replyFacts fun
    | .retainUnit old => CompactTerminal.remember known slot tag old

/-- Resolve a tag only from a checked path or an available exact projection. -/
def readWithFacts? {X : Ty Empty} {frame : ReplyFrame X} {n : Nat}
    (kept : Fin n → ReplyFrame.Slot frame) (known : CompactTerminal.Known frame)
    (slot : ReplyFrame.Slot frame) : Option (Finite.Table n) :=
  match known slot with
  | some tag => some (fun _ => tag)
  | none => (locate kept slot).map fun j env => env j

/-- Read known fields as constants and select known tests before visiting
their arms. Otherwise a read or nonredundant test needs a retained field. -/
def reindexWithFacts? {X : Ty Empty} {frame : ReplyFrame X} {n : Nat}
    (kept : Fin n → ReplyFrame.Slot frame) (known : CompactTerminal.Known frame) :
    {m : Nat} → Finite.Expr m → (Fin m → ReplyFrame.Slot frame) → Option (Finite.Table n)
  | _, .literal bit, _ => some (fun _ => bit)
  | _, .read i, slots => readWithFacts? kept known (slots i)
  | _, .split low high, slots =>
    let older := fun i => slots i.succ
    match known (slots 0) with
    | some false => reindexWithFacts? kept known low older
    | some true => reindexWithFacts? kept known high older
    | none =>
      if low = high then reindexWithFacts? kept known low older else do
        let test ← locate kept (slots 0)
        let l ← reindexWithFacts? kept known low older
        let r ← reindexWithFacts? kept known high older
        pure fun env => if env test then r env else l env

def reindex? {X : Ty Empty} {frame : ReplyFrame X} {n m : Nat} (kept : Fin n → ReplyFrame.Slot frame)
    (e : Finite.Expr m) (slots : Fin m → ReplyFrame.Slot frame) : Option (Finite.Table n) :=
  reindexWithFacts? kept (fun _ => none) e slots

/-- Recover the same effect skeleton while recording the constructor tag
selected by each pure guard on the path to a terminal. -/
def recoverTreeWithFacts {L : List (Ty Empty)} :
    {m : Nat} → ReadTree L m → {X : Ty Empty} → {frame : ReplyFrame X} →
      CompactTerminal.Known frame → (Fin m → ReplyFrame.Slot frame) →
      {n : Nat} → (Fin n → ReplyFrame.Slot frame) → Option (Finite.Normal L n)
  | _, .ret emits pos i, _, _, known, slots, _, kept => do
    let table ← readWithFacts? kept known (slots i)
    pure (emits.foldr Finite.Normal.emit (.ret pos table))
  | _, .retExpr emits pos e, _, _, known, slots, _, kept => do
    let table ← reindexWithFacts? kept known e slots
    pure (emits.foldr Finite.Normal.emit (.ret pos table))
  | _, .request emits label _ l r, _, _, known, slots, _, kept => do
    let l ← recoverTreeWithFacts l (replyFacts known) (ReplyFrame.bindSlots slots) (ReplyFrame.bindSlots kept)
    let r ← recoverTreeWithFacts r (replyFacts known) (ReplyFrame.bindSlots slots) (ReplyFrame.bindSlots kept)
    pure (emits.foldr Finite.Normal.emit (.request label l r))
  | _, .testRequest emits test low _ _ fl fr tl tr, _, _, known, slots, _ + 1, kept => do
    let i ← locate kept (slots test)
    let children := ReplyFrame.guardSlots slots test
    let retained := ReplyFrame.guardSlots kept i
    let lowFacts := guardFacts known (slots test) false
    let highFacts := guardFacts known (slots test) true
    let fl ← recoverTreeWithFacts fl lowFacts children retained
    let fr ← recoverTreeWithFacts fr lowFacts children retained
    let tl ← recoverTreeWithFacts tl highFacts children retained
    let tr ← recoverTreeWithFacts tr highFacts children retained
    pure (emits.foldr Finite.Normal.emit (.testRequest i low fl fr tl tr))
  | _, .testRequest .., _, _, _, _, 0, _ => none

def recoverTree {L : List (Ty Empty)} {X : Ty Empty} {frame : ReplyFrame X} {n m : Nat}
    (tree : ReadTree L m) (slots : Fin m → ReplyFrame.Slot frame) (kept : Fin n → ReplyFrame.Slot frame) :
    Option (Finite.Normal L n) :=
  recoverTreeWithFacts tree (fun _ => none) slots kept

/-- Compare the original selected split with the canonical guard shell.
Both branches begin with their literal complementary requests. -/
def recoverSplit {L : List (Ty Empty)} {X : Ty Empty} {frame : ReplyFrame X} {m n : Nat}
    (p : SelectedGuardSplit L m) (slots : Fin m → ReplyFrame.Slot frame)
    (kept : Fin (n + 1) → ReplyFrame.Slot frame) : Option (Finite.Normal L (n + 1)) := do
  let i ← locate kept (slots p.test)
  match p.onFalse, p.onTrue with
  | .request [] low _ fl fr, .request [] high _ tl tr =>
    if high = !low then do
      let children := ReplyFrame.bindSlots (fun j => ReplyFrame.Slot.retainUnit (slots j))
      let retained := ReplyFrame.guardSlots kept i
      let lowFacts := guardFacts (fun _ => none) (slots p.test) false
      let highFacts := guardFacts (fun _ => none) (slots p.test) true
      let fl ← recoverTreeWithFacts fl lowFacts children retained
      let fr ← recoverTreeWithFacts fr lowFacts children retained
      let tl ← recoverTreeWithFacts tl highFacts children retained
      let tr ← recoverTreeWithFacts tr highFacts children retained
      pure (p.emits.foldr Finite.Normal.emit (.testRequest i low fl fr tl tr))
    else none
  | _, _ => none

/-- A path fact is valid at a packet only when its typed projection
actually reads that constructor tag. -/
def FactsHold {X : Ty Empty} {frame : ReplyFrame X} {Γ : List (Ty Empty)}
    (known : CompactTerminal.Known frame) (packet : ReplyFrame.Value Γ frame) : Prop :=
  ∀ slot tag, known slot = some tag → (slot.read packet).1 = tag

/-- A canonical key with a native certificate for the actual original arrow. -/
structure Admission {L : List (Ty Empty)} {n : Nat} (p : SelectedAt (replyContext n) L) where
  key : Finite.Normal L n
  packed_eq : p.packedSource = (target key).packed

/-- On admitted programs the result either proves native equality or
returns a distinguishing input in the validated payload trace model. -/
inductive Decision {L : List (Ty Empty)} {n : Nat} (p q : SelectedAt (replyContext n) L) where
  | equal (proof : p.packedSource = q.packedSource)
  | different (input : Finite.Assignment n)
      (proof : CanonicalLive.observations p input ≠ CanonicalLive.observations q input)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay.OrderedTables
