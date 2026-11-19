module

public import Silmaril.Elf.Region.Calls.Defs
public import Silmaril.Elf.Staged.Decomp.Defs

/-! # Candidate windows from one ELF64 symbol table

The existing staged readers supply layout and symbol records from one byte
array. Names are display labels, and aliases stay as separate declarations.
This adapter does not infer PLT bindings, IFUNC resolver targets, or a load bias.
-/

@[expose] public section
namespace Silmaril.Elf.Region.Calls
open Silmaril.Elf.Staged (Layout fastRead readLayout)
open Silmaril.Elf.Staged.Decomp (IsExec IsSymTab STT_FUNC)
open Silmaril.Elf.Staged.Symbols (Tab)
open Silmaril.Formats.ELF (ObjectSymbol)
open Silmaril.Machine.Region (BinaryObject ByteSource)
open Silmaril.X86.Decompile (FunctionSpec)

def symbolWindow (layout : Layout) (symbol : ObjectSymbol) : Option FunctionSpec := do
  let raw := symbol.raw
  if symbol.kind ≠ STT_FUNC ∨ raw.size = 0 ∨ raw.sectionIndex = 0 ∨ 0xff00 ≤ raw.sectionIndex then none else
    let owner ← layout.shs[raw.sectionIndex]?
    if IsExec owner ∧ owner.address ≤ raw.value ∧ raw.value + raw.size ≤ owner.address + owner.size then
      let name := (String.fromUTF8? (symbol.name.map UInt8.ofBitVec).toByteArray).getD s!"@{raw.value}"
      pure ⟨name, raw.value, raw.size⟩
    else none

/-- Select a single `.symtab` or `.dynsym` by section index. Only x86-64
ET_EXEC/ET_DYN virtual-address extents are in profile. Addressable executable
bytes are checked separately by `extract`. -/
def readSymbolPlan (bytes : ByteArray) (tableIndex : Nat) (stubs : List Stub := [])
    (tailSites : List Nat := []) : Option (BinaryObject × Plan) := do
  let reader := fastRead bytes
  let layout ← readLayout.run reader
  if layout.header.machine ≠ 62 ∨ (layout.header.fileType ≠ 2 ∧ layout.header.fileType ≠ 3) then none else
    let table ← layout.shs[tableIndex]?
    let strings ← layout.shs[table.link]?
    if ¬ IsSymTab table ∨ strings.kind ≠ 3 ∨
        table.entrySize ≠ 24 ∨ table.size % 24 ≠ 0 then none else
      let tab : Tab := ⟨strings, table⟩
      let entries ← (List.range tab.count).mapM fun index => (tab.entry index).run reader
      pure (Silmaril.Elf.Region.object (ByteSource.ofByteArray bytes) layout.phdrs,
        ⟨entries.filterMap (symbolWindow layout), stubs, tailSites⟩)

end Silmaril.Elf.Region.Calls
