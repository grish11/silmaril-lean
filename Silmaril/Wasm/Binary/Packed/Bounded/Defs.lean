module

public import Silmaril.Wasm.Binary.Packed.Defs
public import Silmaril.Wasm.Component.Chunked.Defs

/-! Read the header and section envelopes directly from packed bytes, then run the
reference body reader on just the bounded payload of each ordinary section. -/

@[expose] public section

namespace Silmaril.Wasm.Binary.Packed.Bounded

open Core.Decode (Sections readCode readSectionBody sectionRank)
open Silmaril.Wasm.Component.Chunked (runAll)

abbrev CodeEntry := List Wasm.ValType × Wasm.Expr

/-- Proposals are end offsets relative to the section. Only one entry is unpacked at a time;
the reference reader checks its declared size, locals cap, and expression. -/
def readCodeEntries (source : KBytes) : List Nat → Nat → Option (List CodeEntry)
  | [], pos => if pos = source.len then some [] else none
  | stop :: ends, pos =>
    if pos < stop ∧ stop ≤ source.len then
      match runAll readCode (source.slice pos (stop - pos)).toList with
      | some entry => (readCodeEntries source ends stop).map (entry :: ·)
      | none => none
    else none

/-- The supplied tree contains only the code section, with position zero at its count. -/
def readCodes (source : KBytes) (wf : source.wf = true) (ends : List Nat) : Option (List CodeEntry) :=
  match (readU 32).run ⟨source, wf, 0⟩ with
  | .ok (count, start) =>
    if count = ends.length ∧ count ≤ source.len - start.pos then readCodeEntries source ends start.pos else none
  | .error _ => none

/-- Read an ordinary section from its own bounded tree. With proposals, read code entry by entry. -/
def readBody (id : Nat) (sections : Sections) (body : KBytes) (wf : body.wf = true)
    (codeEnds : Option (List Nat)) : Option Sections :=
  match codeEnds with
  | some ends => if id = 10 then (readCodes body wf ends).map (fun code => { sections with code := code })
    else runAll (readSectionBody id sections) body.toList
  | none => runAll (readSectionBody id sections) body.toList

/-- Successful runs reach the end of the source. Custom sections are not supported. -/
def readSections (source : KBytes) (wf : source.wf = true) (codeEnds : Option (List Nat)) :
    Nat → Nat → Nat → Sections → Option Sections
  | fuel, pos, last, sections =>
    if pos = source.len then some sections else
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match source.get? pos, (readU 32).run ⟨source, wf, pos + 1⟩ with
      | some byte, .ok (size, start) =>
        let id := byte.toNat
        let rank := sectionRank id
        if bound : id ≠ 0 ∧ last < rank ∧ start.pos + size ≤ source.len then
          let body := source.slice start.pos size
          match readBody id sections body (source.wf_slice _ _ wf bound.2.2) codeEnds with
          | some next => readSections source wf codeEnds fuel (start.pos + size) rank next
          | none => none
        else none
      | _, _ => none

def assemble (sections : Sections) : Wasm.Module :=
  { types := sections.types
    imports := sections.imports
    tags := sections.tags
    globals := sections.globals
    tables := sections.tables
    memories := sections.memories
    elems := sections.elems
    funcs := Core.zipFuncs sections.funcTypes sections.code
    data := sections.data
    start := sections.start
    exports := sections.exports }

/-- The reference decoder's checks that relate multiple sections, followed by assembly. -/
def finish (sections : Sections) : Option Wasm.Module :=
  if sections.funcTypes.length == sections.code.length &&
      sections.dataCount.all (· == sections.data.length) &&
      (sections.dataCount.isSome || (Core.codesDataIdxs sections.code).isEmpty) then some (assemble sections)
  else none

/-- A successful result certifies the exact result of `Core.decode?`. Failure makes no
claim about the reference decoder. A code plan, if supplied, is checked rather than trusted. -/
def decode? (source : KBytes) (wf : source.wf = true) (codeEnds : Option (List Nat) := none) :
    Option Wasm.Module :=
  match readHeader.run ⟨source, wf, 0⟩ with
  | .ok ((), cursor) =>
    if cursor.pos = 8 then (readSections source wf codeEnds source.len 8 0 {}).bind finish else none
  | .error _ => none

end Silmaril.Wasm.Binary.Packed.Bounded
