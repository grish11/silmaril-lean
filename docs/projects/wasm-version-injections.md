# Native Wasm version injections

Import [`Silmaril.Wasm.Profiles.Injections.Thms`](../../Silmaril/Wasm/Profiles/Injections/Thms.lean).
The arrows use `Module W` and `Function W` for the **native** profile syntax,
not feature-filtered Core syntax. They are explicit values, not instances or
coercions: callers choose the route and whether they need binary agreement.

```text
Wasm1 ──→ Lime ──→ Wasm2 ──⇀ Wasm3 ──→ FX (loadable module)
  └──────────────────────────→ ↑
          Lime ────────────────┘
```

- `wasm1ToLime`, `limeToWasm2`, `wasm1ToWasm2`, and the direct 1.0/Lime
  arrows into Core are total syntax embeddings. `wasm2ToWasm3` is a
  `PartialInjection`; `run` returns `Option`, and `onDomain` is an ordinary
  embedding. Invalid raw numeric conversion triples can both produce `none`;
  that is not equality of the inputs. `id_comp`, `comp_id`, and `comp_assoc`
  compose the existing maps without any change of representation.
- `wasm1_via_lime`, `lime_core_via_wasm2`, `wasm1_core_via_wasm2`, and
  `wasm1_fx_via_wasm2` are exact AST equalities. Where the target is partial,
  the composite is literally `some` of the direct image, not a behavioral
  equivalence. Function syntax maps include the analogous V1-to-Core triangle.
- `wasm2ToWasm3Binary` is a **separate** embedding for the legacy binary
  element forms. `wasm2_binary_via_ast` factors it as ordinary translation then
  element retyping; a legacy function-index initializer uses `(ref null func)`
  in the ordinary image and `(ref func)` in the binary image. Existing
  [binary agreement](../../Silmaril/Wasm/SpecTec/BinaryAgree/Thms.lean) is the
  place to look for encoding/decoding and binary instantiation receipts; this
  syntax layer neither supplies a V2 codec nor claims bytes are identical.
- `wasm3ToFX` is identity on the loadable module AST. `wasm3ToFXUnbound`
  selects empty host-code bindings and `wasm3ToFXInstruction` injects only
  Core instructions. `FuncFX` is runtime code, not a Core function declaration;
  packaging native FX functions would need an instance and function arities.
  There is no claimed inverse for arbitrary FX code or host bindings.

## Typed boundary

V1 and Lime have native validity (the profile API uses a `Unit` interface
index). `checkedWasm1ToLime` and the direct Core images preserve validity.
`validWasm1ToWasm2` requires imported-only global reads in active segment
offsets. `validLimeToWasm2` also excludes extended-const operators in constant
expressions. These are not restrictions on the raw arrows. In particular,
[`exists_valid_noExtendedConst_not_toV2_valid`](../../Silmaril/Wasm/Versions/Thms.lean)
uses a defined immutable global in a valid Lime offset to refute dropping the
offset condition. `checkedWasm1_via_wasm2` proves exact agreement with the
direct Core image whenever the intermediate module really checks.

`checkedWasm2ToWasm3Embedding` embeds **all natively checked V2 modules** at
each fixed import/export interface, mapping the interface using
`V2.ExternType.toCore`. The domain proof covers nested bodies, global
initializers, element initializers/offsets and data offsets. V2 typing implies
the immediate check used by translation, including the extra scalar
conversion guard in the repository's V2 judgment. This does not repair or
prove totality for an unmodified SpecTec derivation lacking that guard.
`checkedWasm2ToWasm3_erasure` identifies the exact raw image, and
`checkedWasm2ToWasm3_lift` gives an intrinsic Core witness at the translated
interface. It does not choose a canonical witness or claim an isomorphism of
typing trees. `wasm2Function_defined` proves total translation at a valid V2
function judgment; Core function typing in isolation additionally needs a
related context (as in the existing module-typing transport).

## SpecTec and behavior receipts

The [snapshot manifest](../../specs/spectec/manifest.json) pins three standard
scripts. The [version comparison](../../specs/spectec/e7a9df7c/README.md) is a
later audit, not a new blanket simulation pin. V1 and V2 use native Lean
syntax and judgments, including documented corrections and restrictions;
Wasm3 is Silmaril's Core implementation and its actual judgments. Lime1 is
the repository's language with a V1-like binary, not a fourth SpecTec script.
FX is the repository's extension of Core execution, not a standard snapshot.
[`Versions.Soundness.Thms`](../../Silmaril/Wasm/Versions/Soundness/Thms.lean)
exports native V2 preservation/progress and two typed-stuck counterexamples
for the literal SpecTec conversion rules without Silmaril's extra premises.

| Route | Existing checked receipt | Important limit |
| --- | --- | --- |
| V1 → Lime; V1/Lime → V2 | [`Versions.Thms`](../../Silmaril/Wasm/Versions/Thms.lean): lockstep for V1 → Lime, and forward `Step.toV2`, `Steps.toV2`, `Diverges.toV2` at `Profile.spec`; [`V10Lime1Back.obs_eq`](../../Silmaril/Wasm/Models/V10Lime1Back/Thms.lean) for the reverse observations. | Reverse V1 observations need `Store1` and the model domain; `converse_false` refutes the unrestricted converse. The V2 route needs related hosts and states. |
| Lime → Core | [`Lime1Core.Thms`](../../Silmaril/Wasm/Models/Lime1Core/Thms.lean): `lime1_core_beh` gives forward observations; `Versions.Thms` exports the step/run/divergence transport. | Neither the raw arrow nor the feature test alone gives backwards simulation. |
| V2 → Core | `Versions.Thms`: `Step.toCore` gives **one or more** Core steps along `Sim`; `Steps.toCore`, `Diverges.toCore`, `Sim.result`, and `Instantiate.toCore`/`InstantiateDiverges.toCore` give finite, infinite, result, and instantiation transport. | Related stores/hosts and relevant bounds matter. [`V2Core.Thms`](../../Silmaril/Wasm/Models/V2Core/Thms.lean) gives observation inclusion and a restricted deterministic equality; `v20_core_valid_iff` needs `ConstReadsImports` on the source and `ValidIn v20` on the target. `v20_core_valid_false` rules out unqualified reflection. [`V2CoreSpecImg.instObs_spec_eq_once`](../../Silmaril/Wasm/Models/V2CoreSpecImg/Thms.lean) is a scoped instantiation observation theorem; the [single-allocation result](../../Silmaril/Wasm/Versions/Once/Thms.lean) is not unqualified standard instantiation equality. |
| Core → FX | [`Models.FX.Thms`](../../Silmaril/Wasm/Models/FX/Thms.lean): `stepFX_conservative`, `stepsFX_conservative`, `divergesFX_conservative`, `behavioursFX_conservative`; [`FXVModel.fxEmb'`](../../Silmaril/Wasm/Models/FXVModel/Thms.lean) is a model embedding. | The single-step theorem assumes `NoFX` on the store and uses a blocked host; the run/behavior equalities use `noFX` bindings. Neither interprets nonempty FX bindings as Core. |

The [SpecTec institution chain](../../Silmaril/Wasm/SpecTec/Institution/Chain2030/Thms.lean)
preserves progress in its stated domain. The
[one-step bridge](../../Silmaril/Wasm/SpecTec/Institution/Chain2030One/Thms.lean)
proves `sat_iff_v2_model1` on `PairDom1`, not all V2 states;
`progress_not_equal` explains why even progress cannot simply be replaced by
equality. Current receipts do not give a general arbitrary-host contextual
equivalence, a backwards semantics for every profile, or UB reflection.
For [`HasOpSem`](../../Silmaril/Semantics/Operational/Policy/Defs.lean), select a
policy separately, then relate `initial`, `step`, `observe` and `ub` with its
assumptions. Nothing here selects the policy, and a syntax equation does not
prove that simulation.

Regression: `make check CHECK_TARGETS=+Silmaril.Wasm.Profiles.Injections.Thms` checks
the native exported `add` module through the typed chain, the raw conversion
failure, the two element types, no-FX bindings and the theorem axioms.
