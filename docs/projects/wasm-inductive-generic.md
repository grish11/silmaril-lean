# Structural references and interchangeable Wasm function bodies

This is an alternative to the existing [intrinsic Core AST](wasm-intrinsic.md),
not a replacement for it or for the binary decoder.

| Layer | Representation | Checked relationship |
| --- | --- | --- |
| Context reference | `Validation.Inductive.Path.here/there` | `Bounded.equiv` preserves the selected occurrence and its u32 index, with inverses in both directions. `Path` itself does not impose a binary bound. |
| Raw function | `Declaration.Func ValType Body` | A Core function is the `List Instr` specialization; `mapBody` keeps the type index and locals. Binaryen already uses the `List BExpr` specialization. |
| Raw module | `ModuleParts F` | `Module.splitEquiv` splits and rejoins a Core module exactly; `map`/`traverse` preserve non-function sections and slot order. |
| Typed function | `Generic.Typed.Function B context signature` | The type reference is structural. `B` ranges over a body family indexed by the actual function-body context and stack effect. `intrinsicEquiv` is an exact iso at `Intrinsic.Body`. |
| Typed module | `Generic.Typed.Module F interface` | A checked declaration header computes the common environment, then a dependent `Definitions` spine supplies one function per local signature. `intrinsicEquiv` recovers the current typed module exactly at the Core specialization, including all section data. |

## Sections, declarations, and bodies

`Wasm.Module` and `Wasm.Func` still have their original representations.
Import `Silmaril.Wasm.ModuleParts.Thms` for the total projections and assembly:

| Core fields | Projection and role |
| --- | --- |
| `types`, `imports` | `Module.sections` keeps recursive groups and imported declarations in source order. Imports contribute to the combined index spaces. |
| `tags`, `globals`, `memories`, `tables` | Section declarations, including global and table initializer expressions. |
| `data`, `elems` | Segment bytes/expressions, exact modes and offsets; element initializers can refer to local functions. |
| `start`, `exports` | Start and export references into the assembled module, not information about a standalone sections-only module. |
| `funcs` | `Module.split` retains the ordered definitions. A function's `declaration` contains its type use and additional locals; its `body` is separate. `FuncDecl.withBody` reassembles it. |

`ModuleSections` has no function field and makes no standalone validity claim.
Use `sections.assemble defs` or `parts.toCore` to combine the pieces;
`Module.splitEquiv` and `Declaration.Func.splitEquiv` prove both directions.
`ModuleParts.functionSignature?` resolves a function's type use through the
combined imported/local index space. This query is syntactic; the closed,
validated interface comes from `ModuleParts.validate?` on the complete parts.

The intrinsic and generic headers compute the real validation contexts from
sections, resolved imports, and the full declared signature list. Locals and
the parameter/return types then establish the context for a particular body.
`sectionBaseContext_sections` and `sectionContext_sections` compare with the
existing Core checker; `intrinsicEquiv_context` preserves the resulting scope.
`split_mapBody` and `functionDecls_mapBody` distinguish rewriting code from
changing declarations. The Binaryen adapter preserves lowering, not the
contents of the ignored legacy `BModule.base.funcs` field.

`Path.lookup_value`, `Path.lookup_path` and `Path.rename_toNat` connect structural
lookup and renaming to numeric lookup. Repeated equal types do not identify
different slots. `Definitions.get` reduces by pattern matching on a spine and a
path; `Definitions.toList_get` derives the corresponding raw list lookup. The
spine's tail does not shrink function scope: imported, forward and self calls
still use the combined Core scope. A path through `Definitions` enumerates only
defined functions, so its numeric index must not be used as a combined index in
a module with function imports.

`Module.intrinsicEquiv_erase` makes the Core diagram commute:

```text
Intrinsic.Module interface ── intrinsicEquiv ──▶ Typed.Module (Function Intrinsic.Body) interface
              │ erase                                       │ forget Function.erase
              ▼                                             ▼
          Core.Module ───────── split ────────▶ ModuleParts Core.Func
```

`Module.forget_commutes` lifts a commuting payload square to this module level.
Typed maps preserve context/signature indices; the identity and composition
laws do not assume that arbitrary IR transformations preserve semantics. Module
and function erasure prove the existing Core judgments (`sound`), and every
well-typed raw module/function has an exact lift (`lift_erase`). The typed iso
preserves the old *witness*, not a canonical witness for each raw term; distinct
typing trees for one raw term stay distinct. The structural type reference
converts without a stored lookup proof, and the module header computes its
contexts instead of accepting two stored context equalities. Existing Core
instruction bodies are unchanged. A path lookup is linear in depth; this patch
does not replace numeric decoding or establish a kernel speedup.

## Actual LambdaSSA and Binaryen fixture

The regression packages two exported integer functions (increment and unsigned
division) using the existing Wasm LambdaSSA `SFunc` and real `compileFunc`.
`compileFunc_iff` gives the return of 42 and the division-by-zero trap in the
dialect's evaluation relation. The regression then uses `decompileFunc` and
`toBFunc?`, followed by actual Binaryen lowering. The module-level lowering
agrees exactly with mapping the Binaryen body lowering and rejoining the Core
sections. The existing Core validator accepts the output; the straight-line
intrinsic reifier rejects it. These are different checks. The per-function
terminating-outcome equivalences do not prove whole-module semantic equivalence
or an inverse on arbitrary SSA or Binaryen programs.

This fixture exercises **raw** SSA/Binaryen payload packaging. The indexed Core
iso does not provide a translation between `Intrinsic.Body` and the dialect.

```sh
lake build --wfail +Silmaril.Wasm.Validation.Generic.Thms +Silmaril.Wasm.SSA.Translate.Thms \
  +Silmaril.Wasm.SSA.OutOfSSA.Thms +Silmaril.Wasm.SSA.Bridge.Thms \
  +Silmaril.Wasm.SSA.Fragment.Thms +Silmaril.Wasm.Validation.Intrinsic.ReifyThms
lake env lean -DwarningAsError=true tests/wasm/inductive-generic/Regression.lean
```

## Type-parametric LambdaSSA payloads

`Validation.Generic.SSA.AtCore` is an independent LambdaSSA type carrier at a
*fixed Core boundary*: it stores a real `Region.HasType` proof under the
reverse parameter context and two exits, return and trap. A partial boundary
encoding relates its input and return types to `DefType.funcType?`. In
particular, arbitrary SSA tuple and sum types can occur internally without
being silently assigned a Wasm value type at an export. SSA locals are not
identified with Wasm locals.

`TypeMap.region` preserves the actual typing judgment, including typed CFG
block arguments, when the map preserves the type-formers and primitive
signatures. `AtCore.retype` also checks coherence of the boundary encoding.
`retype_module_syntax` says that type re-representation commutes with erasure
of annotated types; `retype_module_roundtrip` proves an exact inverse when
the type maps are inverse. These laws leave the code and actual checked Core
declaration unchanged; they do not lower an SSA region to Core or change the
types in arbitrary Core recursive groups.

The regression represents the same two exported functions under actual
LambdaSSA `Ty IntType` and `FreeTy all IntType`. Its scoped opcode signature
contains integer constants and addition and a division returning a sum for
the trap branch. The erased fixture regions are definitionally equal to the
existing Wasm LambdaSSA compiler's output. Thus the return and trap checks
use the actual dialect's evaluation, not an evaluation invented for the
abstract types. The small opcode embedding is a fixture, not a verified
translation for all opcodes. For arbitrary Wasm primitives, the next typing
prerequisite is a faithful representation of overloaded operations such as
`select` (one monomorphic `HasTy` signature cannot express its variants).

```sh
lake build --wfail +Silmaril.Wasm.Validation.Generic.SSA.Thms \
  +Silmaril.Wasm.SSA.Translate.Thms +Silmaril.Wasm.SSA.Fragment.Thms \
  +Silmaril.Wasm.Validation.Intrinsic.ReifyThms +Silmaril.SSA.Isotope.Types.Thms
lake env lean -DwarningAsError=true tests/wasm/inductive-generic/TypeBoundary.lean
```

## Type-parametric declarations and checked lowering

`Validation.Generic.Signature.Module` has no fixed Core header. Its declared
parameter and result codes index the function payload. For real LambdaSSA,
`DeclaredBody` uses those codes for the reverse parameter context and return
label in `Region.HasType`, with a separate trap label. `Module.map_id` and
`map_comp` make the dependent transports explicit; `signatureAt_map` shows
that a numeric function reference still selects the same slot after retyping.
Two equal signatures may occupy different slots.

`Module.specialize?` makes a final singleton Core type group for each function
slot and returns the fixed-Core `ModuleParts` above. The numeric encoding is
partial; it does not assign an external Wasm value type to arbitrary SSA
products or sums. Export names and indices, memories, and data survive
specialization. This profile has no imports, start, tags, globals, tables,
elements, GC reference types, or recursive type groups. It is not an iso to
arbitrary modules or a new constraint on their type declarations.

The commuting square is `TypeMap.declared_specialize`: with coherent signature
encodings, first retyping (including the payload's actual typing proof) then
specializing equals specializing directly. It holds for code erasure and
for any partial emitter that depends only on the encoded signature, type
index, and region syntax. This equality includes failure and does not require
the two type carriers to be isomorphic.

The regression declares the increment and division regions under `Ty IntType`
and `FreeTy all IntType`. With the same scoped opcode projection as above,
`lowerRegion?` uses the existing `decompileFunc`, `toBFunc?`, and Binaryen
`lowerList` at the emitted integer signature. Both paths give the same Core
AST, including the two distinct type slots, two function exports, and a passive
data segment. The real Core validator accepts it. `checkedLift` proves existence
of a fixed-Core `Typed.Module` with **exact** erasure, using validation soundness
and the existing intrinsic lifting theorem. It does not run the intrinsic
reifier or return a computable typed witness. The regression shows the ordinary
reifier rejecting this lowering, which includes a `local.set`; the reifier's
step checker does not cover that instruction, `return`, or the emitted
`unreachable`. A constructive checker for initialized-local updates and a
polymorphic terminal rule would enable a computable lift for these bodies.
Lowering success alone does not establish Core typing or semantic preservation.

```sh
lake build --wfail +Silmaril.Wasm.Validation.Generic.SSA.Thms \
  +Silmaril.Wasm.Validation.Generic.Signature.Lowering
lake env lean -DwarningAsError=true tests/wasm/inductive-generic/TypeBoundary.lean
```
