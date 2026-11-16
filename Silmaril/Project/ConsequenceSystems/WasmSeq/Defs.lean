module

public import Silmaril.Project.Registry.Consequence.Defs
public import Silmaril.Wasi.Component.Consequence.Interp.Defs

/-!
# A partial interpretation of Wasm modules: the protocol track's `coreInterp`

`wasm.core.seq` registers `Silmaril.Wasi.Consequence.coreInterp`
(`Silmaril/Wasi/Component/Consequence/Interp`), a core `Interp` with configurations
`CoreConfig`: the numerics profile, the admissible hosts, the export `name(ptr: i32, len: i32) ->
i32` and the byte codec of sequents. It reads a module AST as a multiple-conclusion system
between byte lists (`coreSeq`). The ABI and the environment are fields of the configuration, so
they are given per system (`env := …`), not as constants of the definition.

Over a registered value of format `wasm` (the module its CID-pinned bytes decode to), a system
read through it is `artifactSystem X (coreInterp.orBot e)`; whether it is defined is the
separate certificate `silmaril.shapes.consequence.artifact_defined`. The protocol's own
byte-level interpretation `coreBytesInterp` (decoding with `Binary.Core.decode?`) is related to
this one by `coreBytesInterp_member` and `coreBytesInterp_empty`.
-/

silmaril consequence_interpretation wasm.core.seq := Silmaril.Wasi.Consequence.coreInterp
  (doc := "A core module as a multiple-conclusion system Γ ⊢ Δ between byte lists, through the export and codec of the configuration (coreSeq: CoreConfig = profile, hosts, export name, codec)")
