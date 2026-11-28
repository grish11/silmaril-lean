# Toward standard ACL2 world ingestion

The current institutions and checked books cover a nonrecursive logical fragment. They are a
foundation for C2/C4. The target is a versioned formalization of standard ACL2 that can ingest
the pinned upstream x86isa semantics through its dependency closure and track the evidence for
every admission used in a Lean result. The separate dependency inventory will identify the x86isa
revision, its ACL2 configuration, and the required syntactic and logical features. The two
authored fixture books establish interoperability for the current profile. [Fragment and checks](acl2-institutions.md)

## Representation decisions

| Current representation | Constraint for standard books |
| --- | --- |
| One logical value sort, with `Primitives.Value` supplied by each model | Keep the single sort and universal non-`NIL` satisfaction. Add concrete standard ACL2 objects with canonical equality. Use exact rational arithmetic with complex rationals normalized when the imaginary part is zero, byte-valued characters and strings, interned symbols, and conses. `NIL` and `T` are distinguished symbols. The fragment's arbitrary lawful carriers still serve as abstract models. |
| `Name` stores package and symbol strings. The source matcher accepts the `ACL2` package profile. | Treat a resolved name as the symbol's home-package identity. Retain raw token spelling, access syntax, and the active package until resolution. Carry package imports and visibility in the world. In stock ACL2, reading `ACL2::CAR` resolves to the imported `COMMON-LISP::CAR`. Host string equality on the written qualifier is insufficient. |
| `Term S n` has a `Fin n` context and a closed set of primitive constructors. | Keep indexed bound variables and arity-checked applications after elaboration. Extend the standard translated syntax with quoted ACL2 objects and lambda application, or prove a lowering for the latter. Preserve the calling and result conventions for multiple values and single-threaded objects through translation. Multiple results have a logical representation within the same object sort. A pure fragment evaluator with all user functions already denoted gives no definition of recursive calls. |
| `World` stores arities, named bodies and named theorem statements. Every definition body is typed in the preceding signature. | Use a finite ordered event history with lookups for packages, constants, macros, modes, declarations, cliques and theorem provenance. Use a temporary signature containing fresh names for a recursive clique, and commit the clique atomically after obligations are discharged. Track local events and encapsulation with scoped admission and export. The fragment's monotone signature extension applies to visible compatible worlds; a local event scope can hide names. |
| `admitSource` compares a file to a supplied checked fragment book. `Standard.Interface` describes external ACL2 observations using strings and a host world. | Keep this as fragment interoperability. For standard ingestion use typed translated event records with a source-to-event mapping, a pinned ACL2 build and configuration, dependency digests, and ordered world references. Treat a pushed host export or native certificate as external evidence with its own trust boundary. |

ACL2 8.7 probes on the fixture toolchain confirmed the home packages of `NIL`, `T` and
`ACL2::CAR`, normalization of a zero imaginary part, and character code 255. The intended
baseline excludes the optional ACL2(r) extension. [ACL2 8.7 axioms](https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/axioms.lisp) ·
[Package admission](https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/other-events.lisp#L1582) ·
[Term translation](https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/translate.lisp#L24726)

## Next deliverable

**Build the concrete object and package layer, then admit a package-sensitive nonrecursive
definition from translated source.** This is the next PR boundary. It establishes the data
and name invariants shared by recursion, theorem replay and book imports.

### Proposed public interfaces

| Interface | Contract |
| --- | --- |
| `Object`, `Object.equal`, `objectPrimitives : Primitives` | A concrete standard ACL2 object type and computable equality. The interpretation of the current fragment primitives proves the laws in `Primitives` on this carrier. Quoted values use the same object type. |
| `SymbolRef`, `PackageEnv.resolve` | Resolve a reader reference in its active package to a canonical `Name`, with checked package declarations and imports. Report unknown packages, visibility errors and import conflicts. Keep Common Lisp parsing in `ProofFormats` and package resolution in `Logic`. |
| `TranslatedTerm`, `elaborateTerm` | Preserve quoted objects, variable binding and resolved, arity-checked calls. Elaborate relative to a package environment and prior world. Expose the projection of the current fragment's terms into this syntax and prove evaluation agreement for the shared primitives. |
| Nonrecursive admission and world lookup | Admit a freshly named logical definition using a body scoped over prior declarations. Return the resulting world, its named body and the extension witness. Use a checked package event and definition in a small authored fixture. |

The fixture should exercise imported symbol identity, distinct symbols with the same printed name
in different packages, quoted lists and exact numbers, and rejection of a bad package or call
arity. Check the translated definition and its logical evaluation in Lean. Run the same source in
pinned stock ACL2 and compare observations. That comparison is evidence for the fixture, with
the general interpreter correspondence tracked separately.

## Subsequent deliverables in order

1. **Recursive and mutual admission.** Represent calls within a fresh clique explicitly. Evaluate
   the test of `if` before entering the selected branch so unused branches create no recursive
   obligations. Use a well-founded relation on tagged function calls, with a checked decrease
   for each reachable recursive call under its translated governing tests. Keep the ACL2 measure
   and relation in the evidence, including the default ordinal ordering and separately justified
   custom well-founded relations. Construct the clique interpretation by well-founded recursion
   and prove its defining equations and preservation of the old world's model. Check a simple
   recursive function and a mutually recursive pair before applying the API to library cliques.
   [ACL2 definition admission](https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/defuns.lisp#L11565)
2. **Theorem admissions and scoped books.** Extend the sound calculus for the needed reasoning,
   including induction derived from admitted termination evidence. Record theorem references,
   proof evidence and explicit assumptions against the exact input world. Keep replayed Lean
   evidence, externally certified statements and explicit axioms distinguishable. An ACL2
   theorem consumed only through native evidence leaves a named assumption on any resulting
   Lean theorem. Model book paths, certification environments and local visibility, with
   encapsulation checked against its constraints and witnesses. Track theorem rule classes and
   prover controls as event metadata. `:program` definitions and guard verification have
   separate admission and execution status from logical definitions.
   [ACL2 theorem admission](https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/defthm.lisp#L12245) ·
   [ACL2 book inclusion](https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/other-events.lisp#L14287)
3. **Replay the pinned x86isa closure.** Use the separate inventory to order primitive coverage,
   package setup, macro and generated events, admitted cliques, and theorem imports. A pinned
   native export can supply translated terms and generated-event provenance while standalone
   source elaboration is extended. Report which events were decoded, which were admitted with
   checked evidence, and which depend on an external trust assumption. For x86isa execution,
   select a logical entry point and validate the single-threaded state operations, multiple
   results and executable counterparts it uses. Tie evaluation of the imported definition to
   ACL2 observations and prove the required agreement before connecting it to a machine model.
   Closure ingestion requires an accounted-for result for every event in the pinned dependency
   order, with any blocked events and remaining native assumptions visible at the entry point.
   [ACL2 8.7 Community Books](https://github.com/acl2/acl2/tree/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books)

## APIs usable now

| Module | Declarations |
| --- | --- |
| `Silmaril.Logic.ACL2.Thms` | `Signature.resolve`, `Term.map`, `Term.subst`, `Term.eval`, `Sentence.holds_map`, `Derives.sound`, `logic`, and `inst` for abstract single-sort syntax, semantics and proof transport. |
| `Silmaril.Logic.ACL2.Books.Thms` | `Presentation.body`, `Event.defun`, `Event.defthm`, `Book.includeBook`, `Book.checked`, `Book.expand` and `Book.entails_iff` for the checked fragment. |
| `Silmaril.ProofFormats.ACL2.Defs` | `admitSource` attaches source to a supplied checked book and expected dependency paths. |
| `Silmaril.Logic.ACL2.Standard.Thms` | `Standard.source` emits fragment events. `Standard.Realizes.sound_after_include` transfers fragment derivability when the caller supplies realization of the output world. Native certification alone does not supply that realization. |
| `Silmaril.Logic.ACL2.Equational.Thms` and `Consequence.Thms` | `Equational.toEquational` gives the typed graph edge. `Consequence.presentationRoom`, `Consequence.exampleDerives`, `Consequence.exampleEntails` and `Consequence.exampleSound` support room and consequence records. |
