module

public import Silmaril.Proofs.Wasm.Component.Reference.HostMap

/-!
# Changing the host type of a Core 3.0 store: the public surface

Re-exports `Silmaril.Proofs.Wasm.Component.Reference.HostMap` for use outside the component
topic. `Store.mapH g`, `Config.mapH g` rename the code of host functions along `g : H → H'` and
keep everything else (function types and modules, memories, globals, tables, …):

* `Step.mapH`, `Steps.mapH`, `Diverges.mapH`: **host-free steps commute with renaming host code**
  (no host-free rule reads host code; every other rule reads function instances only through
  their types and wasm code, which the renaming keeps);
* `Store.mapH_funcs_getElem?` and the `Store.mapH_set…`/`mapH_add…` commutations with store
  updates;
* `invoke_mapH`: the invocation configuration of an export commutes with the renaming;
  `instantiateOnce?_mapH`: so does instantiation.

The definitions and proofs live in the proof module; this header adds no declarations.
-/
