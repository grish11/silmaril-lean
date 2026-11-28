module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.BranchEntry.Defs

/-! # Outline one request in a written entry case leaf -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry

open LambdaSSA (FiniteCFG Region Tm)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
  (Expr PacketType PrimitiveSignature elaborateArg elaborateBranch elaborateExpr)

variable {F : Type} {blocks exits captures newBlocks n : Nat} {Γ Δ : List PacketType}
  {sig : PrimitiveSignature F} {packets : Fin blocks → PacketType} {outputs : Fin exits → PacketType}

/-- Reuse the prefix frame to pack the case payload and all enclosing
slots, listed newest first. -/
def scopeFrame (ty : PacketType) : (older : List PacketType) → Frame (ty :: older)
  | [] => .entry ty
  | head :: rest => .push ty (scopeFrame head rest)

def packScope : {Γ : List PacketType} → Frame Γ → Positions Γ → Tm F
  | _, .entry _, layout => .var (layout .here)
  | _, .push _ older, layout =>
    .pair (packScope older (fun slot => layout (.there slot))) (.var (layout .here))

structure Request (sig : PrimitiveSignature F) (packets : Fin blocks → PacketType)
    (outputs : Fin exits → PacketType) (Γ : List PacketType) where
  op : F
  arg : Expr Γ (sig.argument op)
  tail : CaseTail packets outputs (sig.reply op :: Γ)
  frame : Frame Γ

def Request.row (request : Request sig packets outputs Γ) : Row sig packets outputs Γ :=
  .request request.op request.arg (.branch request.tail)

/-- A path to the selected leaf, with a structural tree on each bypass.
The indices retain the types of the enclosing case binders. -/
inductive Path (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType)
    (leaf : List PacketType) : List PacketType → Type
  | here : Path packets outputs leaf leaf
  | left {Γ : List PacketType} {a b : PacketType} (test : Expr Γ (.coprod a b))
      (selected : Path packets outputs leaf (a :: Γ)) (bypass : CaseTail packets outputs (b :: Γ)) :
      Path packets outputs leaf Γ
  | right {Γ : List PacketType} {a b : PacketType} (test : Expr Γ (.coprod a b))
      (bypass : CaseTail packets outputs (a :: Γ)) (selected : Path packets outputs leaf (b :: Γ)) :
      Path packets outputs leaf Γ

def Path.erase (old : Fin blocks → Fin newBlocks) (leaf : Region F) :
    {Γ : List PacketType} → Path packets outputs Δ Γ → Region F
  | _, .here => leaf
  | _, .left test selected bypass =>
    .case (operand position test) (selected.erase old leaf) (CaseTail.erase old position bypass)
  | _, .right test bypass selected =>
    .case (operand position test) (CaseTail.erase old position bypass) (selected.erase old leaf)

structure Selection (sig : PrimitiveSignature F) (packets : Fin blocks → PacketType)
    (outputs : Fin exits → PacketType) (Γ : List PacketType) where
  scope : List PacketType
  request : Request sig packets outputs scope
  path : Path packets outputs scope Γ

/-- Check exactly one request and use the shared structural tail elaborator
in the scope extended by its typed reply. -/
def readRequest (sig : PrimitiveSignature F) (packets : Fin blocks → PacketType)
    (outputs : Fin exits → PacketType) : (Γ : List PacketType) → Region F → Option (Request sig packets outputs Γ)
  | ty :: rest, .let₁ (.op op arg) tail => do
    let value ← elaborateArg (ty :: rest) (sig.argument op) arg
    let next ← elaborateBranch (Sum.elim packets outputs) (sig.reply op :: ty :: rest) tail
    return ⟨op, value, next, scopeFrame ty rest⟩
  | _, _ => none

/-- False selects the left arm and true selects the right arm. The selected
leaf has one primitive application followed by a structural tail. All
off-path subtrees must elaborate as pure branches. -/
def read (sig : PrimitiveSignature F) (packets : Fin blocks → PacketType)
    (outputs : Fin exits → PacketType) :
    (Γ : List PacketType) → List Bool → Region F → Option (Selection sig packets outputs Γ)
  | Γ, [], leaf => do
    let request ← readRequest sig packets outputs Γ leaf
    return ⟨Γ, request, .here⟩
  | Γ, false :: path, .case test left right => do
    let ⟨.coprod a b, discr⟩ ← elaborateExpr Γ test | none
    let selected ← read sig packets outputs (a :: Γ) path left
    let bypass ← elaborateBranch (Sum.elim packets outputs) (b :: Γ) right
    return ⟨selected.scope, selected.request, .left discr selected.path bypass⟩
  | Γ, true :: path, .case test left right => do
    let ⟨.coprod a b, discr⟩ ← elaborateExpr Γ test | none
    let bypass ← elaborateBranch (Sum.elim packets outputs) (a :: Γ) left
    let selected ← read sig packets outputs (b :: Γ) path right
    return ⟨selected.scope, selected.request, .right discr bypass selected.path⟩
  | _, _, _ => none

/-- Emit a request and its reply continuation at two allocated labels. -/
def Request.cellsAt (request : Request sig packets outputs Γ) (old : Fin blocks → Fin newBlocks)
    (labels : Fin 2 → Fin newBlocks) : Fin 2 → PacketType × Region F :=
  request.row.cells old request.frame labels

def Request.jumpAt (request : Request sig packets outputs Γ) (label : Fin newBlocks) : Region F :=
  .br label.val (packScope request.frame position)

def Request.cells (request : Request sig packets outputs Γ) : Fin 2 → PacketType × Region F :=
  request.cellsAt (oldLabel 2) (freshLabel blocks)

def Request.jump (request : Request sig packets outputs Γ) : Region F :=
  request.jumpAt (freshLabel blocks (0 : Fin 2))

/-- Concatenate two finite tables in their written order. -/
def appendTable {A : Type} (initial : Fin blocks → A) (suffix : Fin n → A) : Fin (blocks + n) → A :=
  fun i => if old : i.val < blocks then initial ⟨i.val, old⟩
    else suffix ⟨i.val - blocks, by omega⟩

theorem appendTable_left {A : Type} (initial : Fin blocks → A) (suffix : Fin n → A) (i : Fin blocks) :
    appendTable initial suffix (i.castAdd n) = initial i := by
  simp [appendTable, i.isLt]

theorem appendTable_right {A : Type} (initial : Fin blocks → A) (suffix : Fin n → A) (i : Fin n) :
    appendTable initial suffix (i.natAdd blocks) = suffix i := by
  have fresh : ¬ blocks + i.val < blocks := by omega
  simp only [appendTable, Fin.val_natAdd, dite_eq_right fresh]
  exact congrArg suffix (Fin.ext (Nat.add_sub_cancel_left _ _))

def Request.profile (request : Request sig packets outputs Γ) : Fin (blocks + 2) → PacketType :=
  appendTable packets fun i => (request.cells i).1

/-- Exact readback of an entry and its appended row table. Original
positions stay fixed, and only the absolute outward labels are shifted. -/
structure Assembly (source : FiniteCFG F blocks exits captures) (written entry : Region F)
    (suffix : Fin n → PacketType × Region F) where
  code : FiniteCFG F (blocks + n) exits captures
  sourceEntry : source.entry.erase = written
  entry_eq : code.entry.erase = entry
  old_eq : ∀ i : Fin blocks, (code.block (oldLabel n i)).erase =
    (source.block i).erase.renameLabels (moveExit blocks n)
  leaf_eq : ∀ i : Fin n, (code.block (freshLabel blocks i)).erase = (suffix i).2

def assemble [DecidableEq F] (source : FiniteCFG F blocks exits captures) (written entry : Region F)
    (suffix : Fin n → PacketType × Region F) : Option (Assembly source written entry suffix) := do
  let reconstructed ← scopedRow (blocks + exits) captures written
  if exactEntry : source.entry = reconstructed.val then
    let labels := blocks + n + exits
    let start ← scopedRow labels captures entry
    let oldRows ← tabulateDependent blocks fun i =>
      scopedRow labels (captures + 1) ((source.block i).erase.renameLabels (moveExit blocks n))
    let leafRows ← tabulateDependent n fun i => scopedRow labels (captures + 1) (suffix i).2
    let code : FiniteCFG F (blocks + n) exits captures :=
      ⟨start.val, appendTable (fun i => (oldRows i).val) (fun i => (leafRows i).val)⟩
    return ⟨code, (congrArg LambdaSSA.Flat.erase exactEntry).trans reconstructed.property, start.property,
      fun i => by simpa only [code, oldLabel, appendTable_left] using (oldRows i).property,
      fun i => by simpa only [code, freshLabel, appendTable_right] using (leafRows i).property⟩
  else none

structure Outlined (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType)
    (source : FiniteCFG F blocks exits captures) where
  selection : Selection sig packets outputs context.toList
  code : FiniteCFG F (blocks + 2) exits captures
  sourceEntry : source.entry.erase = selection.path.erase id selection.request.row.erase
  entry_eq : code.entry.erase = selection.path.erase (oldLabel 2) selection.request.jump
  old_eq : ∀ i : Fin blocks, (code.block (oldLabel 2 i)).erase =
    (source.block i).erase.renameLabels (moveExit blocks 2)
  leaf_eq : ∀ i : Fin 2, (code.block (freshLabel blocks i)).erase = (selection.request.cells i).2

def outline [DecidableEq F] (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType)
    (source : FiniteCFG F blocks exits captures) (path : List Bool) :
    Option (Outlined sig context packets outputs source) := do
  if path.isEmpty then none else
    let selection ← read sig packets outputs context.toList path source.entry.erase
    let emitted ← assemble source (selection.path.erase id selection.request.row.erase)
      (selection.path.erase (oldLabel 2) selection.request.jump) selection.request.cells
    return ⟨selection, emitted.code, emitted.sourceEntry, emitted.entry_eq, emitted.old_eq, emitted.leaf_eq⟩

structure Compiled (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType)
    (source : FiniteCFG F blocks exits captures) where
  outlined : Outlined sig context packets outputs source
  sourceTyped : letI := sig.typing; source.HasType context packets outputs
  prepared : BranchEntry.Prepared sig context outlined.selection.request.profile outputs outlined.code
  publicReadback : Constructed sig (BranchEntry.profile context outlined.selection.request.profile)
    outputs prepared.emitted.code

/-- Check the written CFG, outline its selected request, and use the
structural entry checker and exact public packed readback on the emitted table. -/
def compile [DecidableEq F] (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType)
    (source : FiniteCFG F blocks exits captures) (path : List Bool) :
    Option (Compiled sig context packets outputs source) :=
  letI := sig.typing;
  if original : NamedFlat.check source context packets outputs = true then
    match outline sig context packets outputs source path with
    | none => none
    | some outlined =>
      match BranchEntry.prepare sig context outlined.selection.request.profile outputs outlined.code with
      | none => none
      | some prepared =>
        (construct sig (BranchEntry.profile context outlined.selection.request.profile)
          outputs prepared.emitted.code).map fun result =>
          ⟨outlined, NamedFlat.check_sound _ _ _ _ original, prepared, result⟩
  else none

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry
