module

public import Silmaril.Formats.Compression.Zstd.Huffman.LiteralSection.Defs
public import Silmaril.Formats.Compression.Zstd.LiteralBlock.Defs

/-! # Zstandard literal sections with checked Huffman table state

RFC 8878 §3.1.1.3.1. A dictionary-free frame starts empty. A successful
new-tree part installs its canonical table. Treeless, raw and RLE
sections never replace the prior table.
-/

public section

namespace Silmaril.Formats.Compression.Zstd.Huffman.LiteralState

open LiteralSection (Limits Header Envelope StreamsWire)
open LiteralSection.Internal (readFields cutEnvelope readStreams)

/-- The tree limits are fixed for the life of the state. The checked source
    is a proof witness and is erased at runtime. -/
structure State (profile : TreeDescription.Limits) where
  private mk ::
  table : Option SingleStream.Table
  provenance : ∀ table', table = some table' →
    ∃ body description, TreeDescription.readTable profile body = .ok (description, table')

/-- Start a dictionary-free stream or reset at a dictionary-free frame boundary. -/
def State.empty (profile : TreeDescription.Limits) : State profile :=
  ⟨none, by intro table impossible; cases impossible⟩

@[simp] theorem State.empty_table (profile : TreeDescription.Limits) :
    (State.empty profile).table = none := by
  unfold State.empty
  rfl

structure Result (profile : TreeDescription.Limits) where
  literals : LiteralBlock.Literals
  consumed : Nat
  rest : List UInt8
  next : State profile

inductive Error where
  | plain (reason : LiteralBlock.BoundedError)
  | compressed (reason : LiteralSection.Error)
  | unavailableTable
  deriving DecidableEq, Repr

inductive Wire (limits : Limits) (prior : State limits.tree) (input : List UInt8) :
    Result limits.tree → Prop where
  | plain {parsed : LiteralBlock.Prefix} :
      parsed.Wire input →
      Wire limits prior input ⟨parsed.literals, parsed.consumed, parsed.rest, prior⟩
  | newTree {part : Envelope} {description : TreeDescription.Prefix} {table : SingleStream.Table}
      {out : List UInt8} {next : State limits.tree} :
      part.Wire 2 input →
      TreeDescription.readTable limits.tree part.body = .ok (description, table) →
      description.rest.length = part.header.compressed - description.consumed →
      StreamsWire part.header table (part.header.compressed - description.consumed) description.rest out →
      out.length = part.header.regenerated →
      next.table = some table →
      Wire limits prior input ⟨.raw out, part.header.extent, part.rest, next⟩
  | treeless {part : Envelope} {table : SingleStream.Table} {out : List UInt8} :
      part.Wire 3 input → prior.table = some table →
      StreamsWire part.header table part.header.compressed part.body out →
      out.length = part.header.regenerated →
      Wire limits prior input ⟨.raw out, part.header.extent, part.rest, prior⟩

namespace Internal

def install {profile : TreeDescription.Limits} {body : List UInt8}
    {description : TreeDescription.Prefix} {table : SingleStream.Table}
    (checked : TreeDescription.readTable profile body = .ok (description, table)) : State profile :=
  ⟨some table, by intro table' same; cases same; exact ⟨body, description, checked⟩⟩

theorem install_table {profile : TreeDescription.Limits} {body : List UInt8}
    {description : TreeDescription.Prefix} {table : SingleStream.Table}
    (checked : TreeDescription.readTable profile body = .ok (description, table)) :
    (install checked).table = some table := by
  unfold install
  rfl

@[expose] def readEnvelope (limits : Limits) (first : UInt8) (rest : List UInt8) : Except LiteralSection.Error Envelope := do
  let (header, body) ← readFields first rest
  cutEnvelope limits header body

@[expose] def readNew (limits : Limits) (part : Envelope) : Except Error (Result limits.tree) :=
  match checked : TreeDescription.readTable limits.tree part.body with
  | .error reason => .error (.compressed (.tree reason))
  | .ok (description, table) => do
    let out ← (readStreams limits part.header (part.header.compressed - description.consumed)
      description.rest table).mapError Error.compressed
    return ⟨.raw out, part.header.extent, part.rest, install checked⟩

@[expose] def readTreeless (limits : Limits) (prior : State limits.tree) (part : Envelope) :
    Except Error (Result limits.tree) :=
  match prior.table with
  | none => .error .unavailableTable
  | some table => do
    let out ← (readStreams limits part.header part.header.compressed part.body table)
      |>.mapError Error.compressed
    return ⟨.raw out, part.header.extent, part.rest, prior⟩

end Internal

/-- Read exactly one literal prefix and return its accepted successor. -/
@[expose] def read (limits : Limits) (prior : State limits.tree) : List UInt8 → Except Error (Result limits.tree)
  | [] => .error (.compressed .truncatedHeader)
  | first :: rest => do
    let kind := first.toNat % 4
    if kind < 2 then
      let parsed ← (LiteralBlock.parseLiteralsBounded limits.inputCap limits.outputCap (first :: rest))
        |>.mapError Error.plain
      return ⟨parsed.literals, parsed.consumed, parsed.rest, prior⟩
    else
      let part ← (Internal.readEnvelope limits first rest).mapError Error.compressed
      if kind = 2 then Internal.readNew limits part else Internal.readTreeless limits prior part

end Silmaril.Formats.Compression.Zstd.Huffman.LiteralState
