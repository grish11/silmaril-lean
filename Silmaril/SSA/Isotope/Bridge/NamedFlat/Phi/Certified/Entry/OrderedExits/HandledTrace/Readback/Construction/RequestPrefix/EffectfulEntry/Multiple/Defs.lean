module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.EffectfulEntry.Defs

/-! # Outline checked requests and reply continuations in a written entry tree -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple

open LambdaSSA (FiniteCFG Region)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
  (Expr PacketType PrimitiveSignature elaborateArg elaborateBranch elaborateExpr)

variable {F : Type} {blocks exits captures n newBlocks : Nat} {Γ : List PacketType}
  {sig : PrimitiveSignature F} {packets : Fin blocks → PacketType} {outputs : Fin exits → PacketType}

/-- A checked entry tree indexed by the number of appended rows.
A request owns its application and reply rows, followed by the rows
of its continuation. An unpack owns one row, followed by its
continuation. Cases divide the suffix into disjoint intervals. -/
inductive EntryTree (sig : PrimitiveSignature F) (packets : Fin blocks → PacketType)
    (outputs : Fin exits → PacketType) : List PacketType → Nat → Type
  | pure {Γ : List PacketType} (tail : CaseTail packets outputs Γ) : EntryTree sig packets outputs Γ 0
  | request {Γ : List PacketType} (leaf : Request sig packets outputs Γ) : EntryTree sig packets outputs Γ 2
  | requestThen {Γ : List PacketType} {n : Nat} (op : F) (arg : Expr Γ (sig.argument op)) (frame : Frame Γ)
      (next : EntryTree sig packets outputs (sig.reply op :: Γ) n) : EntryTree sig packets outputs Γ (2 + n)
  | unpack {Γ : List PacketType} {a b : PacketType} {n : Nat}
      (value : Expr Γ (.product a b)) (frame : Frame Γ)
      (next : EntryTree sig packets outputs (b :: a :: Γ) n) : EntryTree sig packets outputs Γ (1 + n)
  | case {Γ : List PacketType} {a b : PacketType} {l r : Nat} (test : Expr Γ (.coprod a b))
      (left : EntryTree sig packets outputs (a :: Γ) l) (right : EntryTree sig packets outputs (b :: Γ) r) :
      EntryTree sig packets outputs Γ (l + r)

def EntryTree.written : {Γ : List PacketType} → {n : Nat} → EntryTree sig packets outputs Γ n → Region F
  | _, _, .pure tail => CaseTail.erase id position tail
  | _, _, .request leaf => leaf.row.erase
  | _, _, .requestThen op arg _ next => .let₁ (.op op (operand position arg)) next.written
  | _, _, .unpack value _ next => .let₂ (operand position value) next.written
  | _, _, .case test left right => .case (operand position test) left.written right.written

/-- Render an entry in the current slot layout. A reply row uses the
restored frame's positions where the written entry uses lexical positions. -/
def EntryTree.entryAt (old : Fin blocks → Fin newBlocks) :
    {Γ : List PacketType} → {n : Nat} → EntryTree sig packets outputs Γ n →
      (Fin n → Fin newBlocks) → Positions Γ → Region F
  | _, _, .pure tail, _, layout => CaseTail.erase old layout tail
  | _, _, .request leaf, labels, layout => .br (labels 0).val (packScope leaf.frame layout)
  | _, _, .requestThen (n := n) _ _ frame _, labels, layout =>
    .br (labels ((0 : Fin 2).castAdd n)).val (packScope frame layout)
  | _, _, .unpack (n := n) _ frame _, labels, layout =>
    .br (labels ((0 : Fin 1).castAdd n)).val (packScope frame layout)
  | _, _, .case (r := r) test left right, labels, layout =>
    .case (operand layout test) (left.entryAt old (fun i => labels (i.castAdd r)) (bindPosition layout))
      (right.entryAt old (fun i => labels (i.natAdd _)) (bindPosition layout))

def EntryTree.entry (tree : EntryTree sig packets outputs Γ n) (old : Fin blocks → Fin newBlocks)
    (labels : Fin n → Fin newBlocks) : Region F :=
  tree.entryAt old labels position

def EntryTree.cells (old : Fin blocks → Fin newBlocks) :
    {Γ : List PacketType} → {n : Nat} → EntryTree sig packets outputs Γ n →
      (Fin n → Fin newBlocks) → Fin n → PacketType × Region F
  | _, _, .pure _, _ => Fin.elim0
  | _, _, .request leaf, labels => leaf.cellsAt old labels
  | _, _, .requestThen (n := n) op arg frame next, labels =>
    let reply := Frame.push (sig.reply op) frame
    let childLabels := fun i : Fin n => labels (i.natAdd 2)
    appendTable (Fin.cases
      (frame.packet, frame.requestCell op arg (labels ((1 : Fin 2).castAdd n)))
      (fun _ : Fin 1 => (reply.packet, reply.unpack 0 (next.entryAt old childLabels (reply.position 0)))))
      (next.cells old childLabels)
  | _, _, .unpack (n := n) value frame next, labels =>
    let childLabels := fun i : Fin n => labels (i.natAdd 1)
    let layout : Positions _ := frame.position 0
    appendTable (fun _ : Fin 1 => (frame.packet, frame.unpack 0
      (.let₂ (operand layout value) (next.entryAt old childLabels (bindPosition (bindPosition layout))))))
      (next.cells old childLabels)
  | _, _, .case (r := r) _ left right, labels =>
    appendTable (left.cells old (fun i => labels (i.castAdd r))) (right.cells old (fun i => labels (i.natAdd _)))

/-- Check both case arms and reply continuations in their extended scopes.
The existing structural tail checker still handles a request with a pure
continuation without allocating additional subtree rows. -/
def read (sig : PrimitiveSignature F) (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType) :
    (Γ : List PacketType) → Region F → Option (Σ n, EntryTree sig packets outputs Γ n)
  | Γ, .case test left right => do
    let ⟨.coprod a b, discr⟩ ← elaborateExpr Γ test | none
    let ⟨_, left⟩ ← read sig packets outputs (a :: Γ) left
    let ⟨_, right⟩ ← read sig packets outputs (b :: Γ) right
    return ⟨_, .case discr left right⟩
  | ty :: rest, .let₁ (.op op arg) tail => do
    let value ← elaborateArg (ty :: rest) (sig.argument op) arg
    let frame := scopeFrame ty rest
    match elaborateBranch (Sum.elim packets outputs) (sig.reply op :: ty :: rest) tail with
    | some pureTail => return ⟨2, .request ⟨op, value, pureTail, frame⟩⟩
    | none => do
      let ⟨n, next⟩ ← read sig packets outputs (sig.reply op :: ty :: rest) tail
      return ⟨2 + n, .requestThen op value frame next⟩
  | ty :: rest, .let₂ value tail => do
    let ⟨.product a b, value⟩ ← elaborateExpr (ty :: rest) value | none
    let ⟨n, next⟩ ← read sig packets outputs (b :: a :: ty :: rest) tail
    return ⟨1 + n, .unpack value (scopeFrame ty rest) next⟩
  | Γ, .br label arg => do
    let tail ← elaborateBranch (Sum.elim packets outputs) Γ (.br label arg)
    return ⟨0, .pure tail⟩
  | _, _ => none

def EntryTree.profile (tree : EntryTree sig packets outputs Γ n) : Fin (blocks + n) → PacketType :=
  appendTable packets fun i => (tree.cells (oldLabel n) (freshLabel blocks) i).1

structure Outlined (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType)
    (source : FiniteCFG F blocks exits captures) where
  count : Nat
  tree : EntryTree sig packets outputs context.toList count
  emitted : Assembly source tree.written (tree.entry (oldLabel count) (freshLabel blocks))
    (tree.cells (oldLabel count) (freshLabel blocks))

def outline [DecidableEq F] (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType)
    (source : FiniteCFG F blocks exits captures) : Option (Outlined sig context packets outputs source) := do
  let ⟨count, tree⟩ ← read sig packets outputs context.toList source.entry.erase
  let emitted ← assemble source tree.written (tree.entry (oldLabel count) (freshLabel blocks))
    (tree.cells (oldLabel count) (freshLabel blocks))
  return ⟨count, tree, emitted⟩

structure Compiled (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType)
    (source : FiniteCFG F blocks exits captures) where
  outlined : Outlined sig context packets outputs source
  sourceTyped : letI := sig.typing; source.HasType context packets outputs
  prepared : BranchEntry.Prepared sig context outlined.tree.profile outputs outlined.emitted.code
  publicReadback : Constructed sig (BranchEntry.profile context outlined.tree.profile)
    outputs prepared.emitted.code

/-- Use the ordinary structural entry adapter and exact public row
checker on the table with all requests and reply continuations outlined. -/
def compile [DecidableEq F] (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType)
    (source : FiniteCFG F blocks exits captures) : Option (Compiled sig context packets outputs source) :=
  letI := sig.typing;
  if original : NamedFlat.check source context packets outputs = true then
    match outline sig context packets outputs source with
    | none => none
    | some outlined =>
      match BranchEntry.prepare sig context outlined.tree.profile outputs outlined.emitted.code with
      | none => none
      | some prepared =>
        (construct sig (BranchEntry.profile context outlined.tree.profile) outputs prepared.emitted.code).map
          fun result => ⟨outlined, NamedFlat.check_sound _ _ _ _ original, prepared, result⟩
  else none

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple
