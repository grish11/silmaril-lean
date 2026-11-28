module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Lexical.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Version.Flat.Defs
public import Silmaril.SSA.LambdaRTL.Version.Defs
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Version.Flat

/-! # Versioning named cyclic CFGs

Every internal edge carries its argument and the finite register snapshot
needed by the destination block. The layout uses a common support collected
from syntactic free reads of the entry and all bodies, omitting the
destination's parameter from its packet. External exits keep their payload.
The first matching label determines the destination layout, just as it
determines the block in cyclic execution.
-/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic

open Silmaril.Elgot

universe v w
variable {V K : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}

section Lexical

variable [DecidableEq V] [DecidableEq K] [Monad M]

/-- A lexical table step. On each hit, restart from the initial environment
extended by the block's parameter. -/
def stepSSA (model : Model F M α) (table : List (K × Block V K F)) (input : V → α)
    (transfer : K × α) : M ((K × α) ⊕ (K × α)) :=
  match table.lookup transfer.1 with
  | none => pure (.inl transfer)
  | some block =>
      Sum.inr <$> block.body.evalJump model (upd input block.param transfer.2)

/-- Execute the entry and iterate lexical table steps. -/
def runSSA [Iterate M] (model : Model F M α) (graph : CFG V K F) (input : V → α) :
    M (K × α) :=
  graph.entry.evalJump model input >>= iter (stepSSA model graph.blocks input)

/-- Execute the mutable entry up to its first transfer. -/
def enter (model : Model F M α) (graph : CFG V K F) (input : V → α) :
    M (Transfer V K α) :=
  graph.entry.exec model (fun label value store => pure (label, value, store)) input

end Lexical

namespace Versioning

variable [DecidableEq V]

/-- The deduplicated union of the entry and block bodies' syntactic free reads. -/
def registers (graph : CFG V K F) : List V :=
  (graph.entry.toRegion.fvList ++
    graph.blocks.flatMap (fun item => item.2.body.toRegion.fvList)).dedup

/-- Every supported register except the destination's incoming parameter. -/
def slots (graph : CFG V K F) (block : Block V K F) : List V :=
  (registers graph).filter fun reg => decide (reg ≠ block.param)

/-- After unpacking the packet, the parameter is at version 1. The other
registers use the versions installed by the tuple decoder. -/
def blockVersions (graph : CFG V K F) (block : Block V K F) : V → Nat :=
  Version.unpackCur (slots graph block) (Version.setv (fun _ => 0) block.param 1) 2

variable [DecidableEq K]

/-- Select the layout of the first matching destination. -/
def destinationsWith (graph : CFG V K F) (layout : Block V K F → List V) (label : K) : Option (List V) :=
  (graph.blocks.lookup label).map layout

/-- The default destination-indexed packet layout. -/
def destinations (graph : CFG V K F) (label : K) : Option (List V) :=
  destinationsWith graph (slots graph) label

open Silmaril.Proofs.SSA.LambdaRTL.CFG.FlatVersion in
/-- Run the existing structured versioner on a single block body and
reify its result. The proof of reifiability is erased. -/
def versionBody (body : Body V K F) (labels : K → Option (List V)) (live : List V)
    (current : V → Nat) (depth : Nat) : Body (V × Nat) K F :=
  (Body.ofRegion? (Version.version labels live current depth body.toRegion)).get (by
    obtain ⟨target, eq⟩ := body_version body labels live current depth
    rw [← eq, body_roundtrip]
    rfl)

open Silmaril.Proofs.SSA.LambdaRTL.CFG.FlatVersion in
/-- Prefix a flat body with the existing structured tuple decoder. -/
def unpackBody (regs : List V) (src : V × Nat) (depth : Nat)
    (body : Body (V × Nat) K F) : Body (V × Nat) K F :=
  (Body.ofRegion? (Version.unpack regs src depth body.toRegion)).get (by
    obtain ⟨target, eq⟩ := unpack_body regs src depth body
    rw [← eq, body_roundtrip]
    rfl)

/-- Compile a block with the chosen incoming record and outgoing layouts.
The argument is at version one after the outer packet is unpacked. -/
def compileBlockWith (labels : K → Option (List V)) (live regs : List V)
    (block : Block V K F) : Block (V × Nat) K F :=
  let reg := block.param
  let current := Version.unpackCur regs (Version.setv (fun _ => 0) reg 1) 2
  ⟨(reg, 0), .let2 (reg, 1) (reg, 2) (.val (.var (reg, 0)))
    (unpackBody regs (reg, 2) 2 (versionBody block.body labels live current (2 + 2 * regs.length)))⟩

/-- Compile one destination with its default saved record. -/
def compileBlock (graph : CFG V K F) (block : Block V K F) : Block (V × Nat) K F :=
  compileBlockWith (destinations graph) (registers graph) (slots graph block) block

/-- Compile the entry and all labelled blocks, preserving table order. -/
def compile (graph : CFG V K F) : CFG (V × Nat) K F :=
  ⟨versionBody graph.entry (destinations graph) (registers graph) (fun _ => 0) 0,
    graph.blocks.map fun item => (item.1, compileBlock graph item.2)⟩

/-- Opt in to empty extra records. This path is intended for packet-local
tables whose blocks read only their original argument and local bindings. -/
def compilePacketLocal (graph : CFG V K F) : CFG (V × Nat) K F :=
  let labels := destinationsWith graph (fun _ => [])
  ⟨versionBody graph.entry labels [] (fun _ => 0) 0,
    graph.blocks.map fun item => (item.1, compileBlockWith labels [] [] item.2)⟩

/-- Encode a pending mutable transfer by the default destination layout. -/
def encode [Monad M] (model : Model F M α) (graph : CFG V K F)
    (transfer : Transfer V K α) : K × α :=
  Version.enc model (destinations graph) transfer

/-- Encode the same transfer with empty extra records at internal labels. -/
def encodePacketLocal [Monad M] (model : Model F M α) (graph : CFG V K F)
    (transfer : Transfer V K α) : K × α :=
  Version.enc model (destinationsWith graph (fun _ => [])) transfer

end Versioning
end Silmaril.SSA.LambdaRTL.CFG.Cyclic
