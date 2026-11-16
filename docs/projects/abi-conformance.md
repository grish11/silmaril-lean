# ABI conformance as a standard problem

A **conformance** row says that machine code, called the way a versioned ABI requires for the
prototype a C header declares, behaves as a conforming callee. It returns the way the ABI
requires, with a result the ABI reads back and a C-level spec allows, and it writes only
memory it is allowed to write. In total mode it also returns. The statement is
`Silmaril.Machine.Abi.Conformance.Conforms`. The standard problems are
`silmaril.shapes.abi.conforms` (code) and `silmaril.shapes.elf.abi_conforms` (the function of
an ELF file). Header satisfaction is `silmaril.shapes.abi.header_sat` and
`silmaril.shapes.elf.abi_header_sat`.

## What a row binds

```lean
structure Conforms (A : AbiDef) (M : Mach) (mode : Mode) (hdr : HeaderSrc) (f : String)
    (p : A.V.Proto) (c : Code) (frame : Nat) (S : CallSpec A.V p) : Prop where
  declared : Declares A hdr f p
  extent : c.off + c.len ≤ c.bytes.length
  nonvacuous : ∃ a s, Admit A M p c frame a s ∧ S.pre a s
  progress : mode = .total → ∀ a s, Admit A M p c frame a s → S.pre a s →
    (callModelOf M s).Nonempty
  sound : ∀ a s, Admit A M p c frame a s → S.pre a s →
    ∀ t ∈ callModelOf M s, Good A p frame S a s t
```

| ingredient | definition | content |
| --- | --- | --- |
| ABI and its version | `AbiDef` | `id` and `source` (the versioned document); the data model; `lower` from a C prototype to the ABI's prototype, or an explicit refusal; a `Convention` with `Entry`, `Return` and `ResultAt`; `argArea` and `owned` (memory the callee gets) |
| prototype | `Declares A hdr f p` | the header files parse (`Data.Layout.Header.read`) to a header that declares `f` with a C prototype, and `A.lower` maps it to `p`; checked by `decide`, not attached by hand |
| code identity | `Code`, `Placed` | the bytes, their load address, the entry offset and the function's extent, plus read-only data the code reads at fixed addresses. An admitted state has them loaded, `rip` at the entry, and the return address outside the code |
| ELF identity | `Elf.Abi.CodeOf` | the symbol lookup (`.symtab`, or ld.so's versioned `.dynsym` lookup) names `f` and finds a plain function with `st_value` = entry and `st_size` = extent; a read-only executable `PT_LOAD` maps the bytes, and read-only segments map the data |
| admissible calls | `Admit` | a live state; `A.conv.Entry p a s`: arguments in their registers and stack slots, `rsp + 8 ≡ 0 (mod 16)`, the return address, DF clear, x87 mode, `%al` for varargs, sret; `frame` bytes of usable stack below `rsp` and the argument area, apart from the code; and `S.pre a s` (C-level validity, no undefined behaviour) |
| execution | `callModelOf M` | the **first return** of the machine `M` (`FnContract.FirstReturn`); the result is read at the function's own return |
| call/return | `Good.ret` = `A.conv.Return` | `rip` = the return address, `rsp` + 8, the callee-saved registers, DF clear, x87 mode, the MXCSR control bits, the x87 control word, the thread pointer |
| result | `Good.result` | some `r` with `A.conv.ResultAt` (the ABI's read-back; excess register bits unspecified) and `S.post a s r t` |
| frame | `Good.frame` | memory written only inside `S.writes` (caller-visible effects) or `Owned`: the `frame` bytes below the entry `rsp` (they contain the red zone), the incoming argument area, and `A.owned` (sret storage) |
| non-vacuity | `nonvacuous` | some admitted call exists |
| divergence | `mode` | `.total`: every admitted call returns. `.ifReturns`: only calls that return are constrained (partial correctness), so divergence and stuck runs are allowed |

The ingredients the user asked about map to definitions as follows. There is no uninterpreted
`conforms` predicate, and no signature is attached to a symbol by hand.

## Assumptions that are explicit, not hidden

- **The machine.** `M` is a parameter: the open machines `Open.isa` and `Open9.isa` are the
  standard instances. Behaviour comes only from `M`. On the open machines there are no
  external calls: a call to code that is not loaded is stuck. A total row then fails, and an
  `.ifReturns` row says nothing about that call.
- **External calls and the runtime.** A row about code that calls a library is stated on a
  machine whose steps include the callee contracts (`Silmaril.Elf.Link.Dyn.Proc`, where glibc
  functions are trusted atomic steps). Those contracts are then the row's assumptions.
- **State the integer machine lacks.** `Ffi.State` carries vectors, x87, DF, MXCSR, the x87
  control word and the thread pointer. `callModelOf` carries them unchanged
  (`callModelOf_carried`), so those `Return` obligations hold *by the model* on the integer
  machines. This is sound because those machines have no instruction that touches that state:
  a run reaching one is stuck and never returns. It is a statement about the model, as
  `Machine.Abi.FsBase` records, not a proof about such instructions.
- **Recursive callers.** `Placed.retOutside` admits only callers whose return address lies
  outside the function's bytes. A self-recursive call is outside the admitted calls.

## Standard ABIs

| `AbiDef` | id | source | supported subset |
| --- | --- | --- | --- |
| `sysvInt` | `x86_64-sysv-psabi@e1ce0983/lp64/integer` | System V AMD64 psABI, x86-psABIs/x86-64-ABI@e1ce098331da5dbd66e1ffc74162380bcc213236, §3.2 | fixed-arity prototypes of 4- and 8-byte integers and pointers, up to 127 parameters; the full `Ffi.Entry`/`Ffi.Return` discipline; the planner `SystemV.Abi.plan` (`intPlan` on this subset) |

`lowerInt` refuses everything else with a message: `_Bool`, `char` and `short`; floating types
(the SSE/x87 classes); structs and unions by value; enums; and varargs (`%al`, `va_list`).
A refusal becomes an `unsupported` exclusion in a coverage (below). The coverage check
confirms that the lowering refuses that prototype.

The psABI planner already classifies aggregates and SSE/x87 values and handles sret and varargs
(`Machine.SystemV.Abi.plan`, `Ffi.Entry`). Extending `sysvInt` to them adds:

- C types with layouts, for the `Object` of each argument;
- representations, for the bytes of each value.

The `Conforms` statement stays the same. Microsoft x64 (`Machine.Abi.Win64`) is the second
convention over the same `Ffi.State`. As an `AbiDef` it has a 32-byte home area in
`argArea`, and every aggregate over 8 bytes is passed by reference.

## Header satisfaction, coverage and versions

A header is read once. A coverage per binary lists the claimed functions and excludes every
other declared function for a reason:

```lean
inductive Exclusion
  | unsupported (why : String)   -- the ABI's lowering refuses the prototype (checked)
  | absent (why : String)        -- the binary does not define it: an API version gap (checked)
  | unclaimed (why : String)     -- defined, in the subset, not claimed (open or out of model)
```

- `Coverage.check A hdr cov` is a computation: the header reads; every declared name is claimed
  or excluded, and not both; nothing else is listed; and the lowering refuses every
  `unsupported` prototype.
- `HeaderSat A M hdr cov impl` is the check plus a `Conforms` row for every claimed function.
- `Elf.Abi.AbiHeaderSat` also checks every `absent` exclusion against the file: the lookup
  finds nothing. It also asks for the ELF binding of every claimed row.

A header shared by several binaries gives **separate rows per binary**. The header and the
specs are the same values; the file, the selector and the code differ. For a shared library
the selector is ld.so's versioned lookup (`.dyn ⟨name, weak, some ver⟩`), so `crc32_z@ZLIB_1.2.9`
and an unversioned definition are different rows. An API version gap shows up in two places:

- as an `absent` exclusion for the older binary;
- as a header-reading error if the declaration itself is new.

## Distinct from the shapes that state less

| shape | says | does not say |
| --- | --- | --- |
| `elf.lookup`, `elf.binds`, function tables | a symbol has a value and a size; the bytes there | anything about a C signature or the ABI |
| `Data.Layout` problems | sizes, offsets and padding of C types under a data model | how a value is passed |
| `x86.abi_function`, `elf.fn_contract` | a contract with the System V *entry* and *return* discipline (`AbiEntry`/`AbiReturn`) | the prototype, argument placement, result read-back, control state, owned memory |
| **`abi.conforms`, `elf.abi_conforms`** | the code is a conforming callee for the header's prototype under a versioned ABI, with a C-level spec | that a compiler produced it (below) |
| `sysv.implements`, `c.compiles_to` | the code implements a source meaning (translation validation) | — |

With `CallSpec.abiOnly` (every call admitted, any result) a row states ABI conformance alone. A
spec with a postcondition adds a semantic contract. Compiler correctness is a different
statement (`c.compiles_to`).

## The worked example: `arith.h` and the pinned `leaf-arith`

`examples/elf-ladder/01-leaf-arith/arith.h` and the `rt.h` it includes are read as text by the
header reader. The code is the pinned gcc 13.3 `-O2` executable
`examples/elf-ladder/01-leaf-arith/pinned/leaf-arith` (SHA-256 `d9cf1e5d…`), read by the
per-part ELF reader (`Silmaril.Elf.Staged.Pinned.LeafArith`).

| row | statement | status |
| --- | --- | --- |
| `silmaril.elf.abi.leaf_arith.clamp_i32` | `int clamp_i32(int, int, int)` at `0x4013a0`, 19 bytes, conforms to `sysvInt` on `Open.isa`, total, result `clampSpec x lo hi`, no frame, nothing written | proved (`clamp_row`) |
| `silmaril.elf.abi.leaf_arith.sat_add_u32` | `u32 sat_add_u32(u32, u32)` at `0x401400`, 29 bytes, result `satAddSpec a b` | proved (`sat_row`) |
| `silmaril.elf.abi.leaf_arith.gcd_u32` | `u32 gcd_u32(u32, u32)` at `0x401370`, 37 bytes, result `Nat.gcd` | open: `Task.gcd_conforms` (the block certificate is proved, its first-return form is not); file facts proved |
| `silmaril.elf.abi.leaf_arith.bswap32_manual` | `u32 bswap32_manual(u32)` at `0x401420`, 5 bytes | open: `Task.bswap_conforms`; file facts proved |
| `silmaril.elf.abi.leaf_arith.arith_h` | the claimed part of `arith.h`: the two proved functions; 9 declarations `absent` from the file (checked); the rest `unclaimed` with reasons (`popcount32`: `imul r32, r/m32, imm32` is outside the open machine; `ilog2_u32`: `bsr`) | proved (`header_row`) |

The statement also rejects wrong specs: `clamp_rejects_first` proves that `clamp_i32` does not
conform with the spec "returns its first argument". The non-vacuity witness is a concrete state
for `clamp_i32(5, 0, 3)`.

## How the proofs are made

`conforms_of_strict` turns a first-return function contract (`FnContract.Spec.Strict`, as block
certificates give through `BlockCert.FunCert.strict`) into a row. It needs:

- the contract's entry from `Admit`;
- a conforming return from the contract's result.

`Proofs.Machine.Abi.Conformance.SysvInt` has the `sysvInt` lemmas: the entry obligations, a
result as a System V return, and the 32-bit read-back.

## Modules

| module | content |
| --- | --- |
| `Silmaril.Data.Layout.Header` | the header subset reader (`read`), `CProto`, `Header` |
| `Silmaril.Machine.Abi.Conformance` | `AbiDef`, `sysvInt`, `Code`, `CallSpec`, `Admit`, `Good`, `Conforms`, `Coverage`, `HeaderSat`; `conforms_of_strict` |
| `Silmaril.Machine.Abi.Conformance.LeafArith` | the example's header, code, specs, coverage, open tasks and proofs |
| `Silmaril.Project.Shapes.Abi` | `silmaril.shapes.abi.conforms`, `header_sat` and their `sysv_int` instances |
| `Silmaril.Elf.Abi`, `Silmaril.Elf.Abi.LeafArith` | `silmaril.shapes.elf.abi_conforms`, `abi_header_sat`, the rows and the group `silmaril.abi` |
| `Silmaril.X86.Ladder.LeafArith.Realizes` | rung 01's `*_realizes` certificates, split from `LeafArith.Thms`. Their proofs import `Silmaril.X86.FnContract.SystemV`, which cannot be loaded together with the `Silmaril.Machine.X86` copies the registry also loads |

## Next

- zlib's checksum functions as rows per binary under one header excerpt:
  - the static `zlib-checksums`, whose total contracts are proved but whose first-return forms
    are open;
  - Ubuntu's `libz.so.1.3`, with versioned selectors.
- `Open9.isa` rows.
- `sysvInt` extended to aggregates, SSE and varargs through the psABI planner.
- `Win64` as an `AbiDef`.
- The explorer's prototype and ABI views over these rows.
