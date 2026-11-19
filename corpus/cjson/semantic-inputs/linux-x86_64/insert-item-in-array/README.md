# Actual cJSON insertion caller/helper source closure

This unregistered candidate retains unchanged saved-TU definitions of `get_array_item`, `suffix_object`, `add_item_to_array` and `cJSON_InsertItemInArray`, including the real helper bodies. The exact type/definition spans and current upstream/TU hashes are in `projection.json`. The actual O0 insertion body is226 bytes at0x5eca; no binary or symbol is manufactured.

The selected new ports follow pinned Cerberus b3e11ea334e95359907d4abf9194f0e7fedc6c6a, frontend/model/translation.lem:94–114 (pointer TestEq uses ConstantNull) and1001 (void call result uses BTy_unit). The real call, parameter-object allocation/conversion and cleanup remain intact. Floating control tests, CHERI and unsupported call domains remain unsupported.

`context.c` is the exact span join, `typed-ail.sexp` the actual Lean frontend output, `program.sexp` the actual four-definition Lean elaboration output and `runtime.sexp` the unchanged pinned public runtime projection. Reproduce using `lake env lean -DwarningAsError=true --run tools/corpus/CjsonInsertInputs.lean`. This is not an upstream compiler/exporter run, frontend-adequacy theorem or corpus semantic proof.

Local finite Core and machine observations cover a three-node list with disjoint new and unrelated objects, interior index1 and append index3, exact four/three pointer updates. Core observations check original caller bytes, pointer provenance, allocation/lifetime/permission records and stdout; machine observations check actual pointer words, byte/mapping preservation, ABI and private stack frame. The native observations use the existing loaded ELF. These are finite observations of a bounded obligation, not full-input coverage, termination/refinement proofs or arbitrary-continuation equivalence. The unproved `CjsonInsert.Context.Task.compilesTo` quantifies over arbitrary admissible aligned heap bases and384 payload bytes, with the same two declared insertion positions. Its nested-call source observation explicitly retains the private-allocation/bookkeeping adequacy gap and does not weaken earlier complete-record contexts. All caller allocation metadata, lifetime, byte/provenance, parameter objects and stdout remain observed; fresh actual private objects must be dead. The exact three/four typed post-stores are demanded postconditions, never entry premises. The target demands exact pointer words, low32 return correspondence, all unrelated bytes/mappings and a128-byte private stack frame. Source safety, joint entries and first returns remain obligations, without universal termination/divergence or general-input coverage.

Targeted validation commands:

```sh
lake build --wfail Silmaril.Elf.Corpus.CjsonInsert.Context.Defs Silmaril.Elf.Corpus.CjsonInsert.Thms Silmaril.Elf.Corpus.CjsonInsert.Source.Projection.Thms
lake env lean -DwarningAsError=true tests/cerberus/CjsonInsertObservation.lean
lake env lean -DwarningAsError=true --run tests/cerberus/CjsonInsertContext.lean
lake env lean -DwarningAsError=true --run tests/cerberus/CjsonInsertMachine.lean
python3 -I tools/corpus/check_cjson_insert_native.py
```
