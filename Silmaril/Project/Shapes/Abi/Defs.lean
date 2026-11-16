module

public import Silmaril.Machine.Abi.Conformance.Defs
public import Silmaril.Project.Shapes.X86.Defs

/-!
# Standard problem shapes: ABI conformance

**Genuine ABI conformance** of machine code, as a standard problem: the code, called as a
versioned ABI requires for the prototype a C header declares, returns as the ABI requires, with
a result the ABI reads back and a C-level spec allows, writing only what it may
(`Silmaril.Machine.Abi.Conformance`, guide `docs/projects/abi-conformance.md`).

| name | statement |
| --- | --- |
| `silmaril.shapes.abi.conforms` | `Conforms A M mode hdr f p code frame S` |
| `silmaril.shapes.abi.conforms.sysv_int_open` | the same for the System V AMD64 INTEGER fragment (`sysvInt`) on the open machine (`Open.isa`) |
| `silmaril.shapes.abi.conforms.sysv_int_open9` | … on `Open9.isa` |
| `silmaril.shapes.abi.header_sat` | `HeaderSat A M hdr cov impl`: the claimed part of a header, each claimed function conforming, every other declaration excluded for a checked reason |
| `silmaril.shapes.abi.header_sat.sysv_int_open` | … for `sysvInt` on `Open.isa` |

The ELF-bound form (the code is the file's, at its symbol's address and size) is
`silmaril.shapes.elf.abi_conforms` (`Silmaril.Elf.Abi`).

These are distinct from the shapes that state less:

* **symbol presence** (`silmaril.shapes.elf.lookup`, `binds`): an ELF symbol has a value and a
  size; it carries no C signature;
* **layout** (`Silmaril.Data.Layout`): sizes and offsets of C types under a data model;
* **a function contract** (`silmaril.shapes.x86.abi_function`, `elf.fn_contract`): a
  System V *entry* and *return* discipline (`AbiEntry`/`AbiReturn`) around a hand-written spec,
  with no prototype, argument placement or result read-back;
* **translation validation** (`silmaril.shapes.sysv.implements`, `c.compiles_to`): the code
  against a source meaning, on INTEGER scalars, for leaf functions writing only their frame.

`conforms` adds to the function-contract shapes the prototype from a header, its lowering by a
versioned ABI (argument registers and stack slots, `%al`, sret, the control-state and
thread-pointer obligations of `Ffi.Entry`/`Ffi.Return`), the result read-back, and the memory
the ABI owns.
-/

@[expose] public section

namespace Silmaril.Project.Shapes.Abi

open Silmaril.Machine.Abi.Conformance

/-- **The code conforms to the ABI `A`** as the function `f` of the header `hdr`
(`Silmaril.Machine.Abi.Conformance.Conforms`). -/
@[problem "silmaril.shapes.abi.conforms"
  (title := "Machine code conforms to a versioned ABI as its C header declares it")]
def AbiConforms (A : AbiDef) (M : Mach) (mode : Mode) (hdr : HeaderSrc) (f : String)
    (p : A.V.Proto) (c : Code) (frame : Nat) (S : CallSpec A.V p) : Prop :=
  Conforms A M mode hdr f p c frame S

/-- **A binary satisfies the claimed part of a header** (`HeaderSat`). -/
@[problem "silmaril.shapes.abi.header_sat"
  (title := "A binary satisfies the claimed part of a C header under a versioned ABI")]
def AbiHeaderSat (A : AbiDef) (M : Mach) (hdr : HeaderSrc) (cov : Coverage)
    (impl : String → Option (Impl A)) : Prop :=
  HeaderSat A M hdr cov impl

end Silmaril.Project.Shapes.Abi

end

silmaril instance silmaril.shapes.abi.conforms.sysv_int_open
    (title := "conforms, System V AMD64 INTEGER fragment, on the open machine (Open)") :=
  silmaril.shapes.abi.conforms (A := Silmaril.Machine.Abi.Conformance.sysvInt)
    (M := Silmaril.X86.Open.isa)
silmaril instance silmaril.shapes.abi.conforms.sysv_int_open9
    (title := "conforms, System V AMD64 INTEGER fragment, on the open machine (Open9)") :=
  silmaril.shapes.abi.conforms (A := Silmaril.Machine.Abi.Conformance.sysvInt)
    (M := Silmaril.X86.Open9.isa)
silmaril instance silmaril.shapes.abi.header_sat.sysv_int_open
    (title := "header_sat, System V AMD64 INTEGER fragment, on the open machine (Open)") :=
  silmaril.shapes.abi.header_sat (A := Silmaril.Machine.Abi.Conformance.sysvInt)
    (M := Silmaril.X86.Open.isa)
