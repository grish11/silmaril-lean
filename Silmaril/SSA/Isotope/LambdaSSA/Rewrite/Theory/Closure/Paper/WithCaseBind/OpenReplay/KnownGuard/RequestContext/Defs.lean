module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.Frames.Defs

/-! # Certificates for carrying a known guard through selected requests -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay

open Silmaril
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open Paper.WithCaseBind.SelectedTerminal (Seed)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
open CategoryTheory

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy

/-- A finite selected request context indexed by its actual slot projections
and the known bit's projection. Request nodes extend both coordinates. A
pruning leaf certifies that the selected test reads the transported bit. -/
inductive KnownGuardContext (L : List (Ty Empty)) :
    {X : Ty Empty} → {n : Nat} → (Fin n → Term signature.Instr X Bit) →
      Term signature.Instr X Bit → Type where
  | keep {X : Ty Empty} {n : Nat} {slots : Fin n → Term signature.Instr X Bit}
      {known : Term signature.Instr X Bit} (tree : ReadTree L n) : KnownGuardContext L slots known
  | prune {X : Ty Empty} {n : Nat} {slots : Fin (n + 1) → Term signature.Instr X Bit}
      {known : Term signature.Instr X Bit} (test : Fin (n + 1)) (guard : GuardRequest L (n + 1))
      (survives : slots test = known) : KnownGuardContext L slots known
  | request {X : Ty Empty} {n : Nat} {slots : Fin n → Term signature.Instr X Bit}
      {known : Term signature.Instr X Bit} (emits : List Bool) (label : Bool)
      (left right : KnownGuardContext L (bindReply slots) (retainSlot (A := Bit) known)) :
      KnownGuardContext L slots known

/-- Recover the actual source syntax for the existing selected compiler. -/
def KnownGuardContext.tree {L : List (Ty Empty)} :
    {X : Ty Empty} → {n : Nat} → {slots : Fin n → Term signature.Instr X Bit} →
      {known : Term signature.Instr X Bit} → KnownGuardContext L slots known → ReadTree L n
  | _, _, _, _, .keep tree => tree
  | _, _ + 1, _, _, .prune test guard _ => guard.tree test
  | _, _, _, _, .request emits label left right => .request emits label false left.tree right.tree

/-- Compile only the certified changes. A pruning leaf forwards the prior
unit payload and uses the guard's original survivor map in the live arm. -/
def KnownGuardContext.pruned {L : List (Ty Empty)} :
    {X : Ty Empty} → {n : Nat} → {slots : Fin n → Term signature.Instr X Bit} →
      {known : Term signature.Instr X Bit} → KnownGuardContext L slots known →
      Term signature.Instr X unit → Bool → Region signature.Instr
  | _, _, slots, _, .keep tree, _, _ => (tree.selectedWith slots).elaborate.val
  | _, _ + 1, slots, _, .prune test guard _, payload, tag =>
    prependEmits guard.emits (.let₁ payload.elaborate.val
      (Paper.PackedBody.applyPacked (guard.live test slots tag).elaborate.val))
  | X, _, _, _, .request emits label left right, payload, tag =>
    let carried := Term.seq (.fst X Bit) payload
    .case (emitPrefix (X := X) emits (.call (show signature.Instr from Op.ask label) .unit)).elaborate.val
      (Paper.PackedBody.applyPacked (left.pruned carried tag))
      (Paper.PackedBody.applyPacked (right.pruned carried tag))

/-- Test a structural bit once, retaining the original input and its unit
payload in each arm for the independently certified request contexts. -/
structure KnownGuardSplit (L : List (Ty Empty)) {X : Ty Empty} {n : Nat}
    (slots : Fin n → Term signature.Instr X Bit) where
  test : Fin n
  emits : List Bool
  onFalse : KnownGuardContext L (fun j => retainSlot (A := unit) (slots j)) (retainSlot (slots test))
  onTrue : KnownGuardContext L (fun j => retainSlot (A := unit) (slots j)) (retainSlot (slots test))

def KnownGuardSplit.source {L : List (Ty Empty)} {X : Ty Empty} {n : Nat}
    {slots : Fin n → Term signature.Instr X Bit} (p : KnownGuardSplit L slots) :
    CaseTree signature.Instr X L :=
  let retained := fun j => retainSlot (A := unit) (slots j)
  .case unit unit (emitPrefix p.emits (slots p.test))
    (p.onFalse.tree.selectedWith retained) (p.onTrue.tree.selectedWith retained)

def KnownGuardSplit.pruned {L : List (Ty Empty)} {X : Ty Empty} {n : Nat}
    {slots : Fin n → Term signature.Instr X Bit} (p : KnownGuardSplit L slots) : Region signature.Instr :=
  let payload := Term.snd (Φ := signature.Instr) X unit
  .case (emitPrefix p.emits (slots p.test)).elaborate.val
    (Paper.PackedBody.applyPacked (p.onFalse.pruned payload false))
    (Paper.PackedBody.applyPacked (p.onTrue.pruned payload true))

def KnownGuardSplit.packedSource {L : List (Ty Empty)} {n : Nat} (p : KnownGuardSplit L (readReply n)) :
    Paper.Extension.Singleton.ofType Seed (replyContext n) ⟶
      Paper.Extension.Singleton.ofType Seed (packedExitType L) :=
  Paper.Extension.Singleton.ofRegion Seed p.source.elaborate.property.packExits

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay
