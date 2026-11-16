module

public import Silmaril.Wasm.Institution.Core3Graph.Defs

/-!
# The component logic graph over Core 3.0: theorems

Instances of the `CompGraph` results at `core3Sem P`:

* `pathModelExpansive`: every path of `fullGraph₃` is model-expansive, so heterogeneous
  borrowing applies along it;
* `valid_wrap_iff`: a sentence about numeric Core 3.0 instances is valid iff its translation
  about their wrapping components is valid in the component logic;
* `valid_flatten_iff`: the same along flattening of nested components.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.Core3Graph

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Logic.Institution
open CategoryTheory Silmaril.Wasm.Institution Silmaril.Wasm.Institution.CompGraph Silmaril.Wasm.Institution.Components
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference ObsSemantics Silmaril.Wasm.Institution.Games

theorem pathModelExpansive {H : Type} (P : Profile) (host : HostSemantics H)
    (Env : Module → Store H → List ExternAddr → Prop) {a b : (fullGraph₃ P host Env).Idx}
    (p : Quiver.Path a b) : (fullGraph₃ P host Env).PathModelExpansive p :=
  fullGraph₂_pathModelExpansive (core3Sem P) P host Env p

theorem valid_wrap_iff (P : Profile) {K : Sig compIfaces.I}
    (s : Sen (moduleSem (core3Sem P)) K) :
    (moduleSem (core3Sem P)).Valid s ↔
      (compSem (core3Sem P)).Valid ((wrapTr (core3Sem P) (wrapAdequate (core3Sem P))).sen s) :=
  CompGraph.valid_wrap_iff (core3Sem P) s

theorem valid_flatten_iff (P : Profile) {K : Sig compIfaces.I}
    (s : Sen (compSem (core3Sem P)) K) :
    (compSem (core3Sem P)).Valid s ↔
      (linkedSem (core3Sem P)).Valid ((flattenTr (core3Sem P) pairLaws).sen s) :=
  CompGraph.valid_flatten_iff (core3Sem P) s

end Silmaril.Wasm.Institution.Core3Graph
