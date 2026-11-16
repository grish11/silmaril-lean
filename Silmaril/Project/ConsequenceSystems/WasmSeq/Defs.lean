module

public import Silmaril.Project.Registry.Consequence.Defs
public import Silmaril.Wasi.Component.Consequence.Interp.Defs
public import Silmaril.Project.ConsequenceSystems.WasmExport.Defs

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

/-- **The two readings of the export `check` agree** (project-side bridge): through the codec
`memberEnc`, `coreSeq … m "check" memberEnc Γ [c]` is `wasm.core.check_rel`'s `checkRel m Γ c`,
at `Profile.spec` and every Core host, for every module. -/
public theorem Silmaril.Project.ConsequenceSystems.WasmSeq.coreSeq_single_iff_checkRel
    (m : Silmaril.Wasm.Module) (Γ : List UInt8) (c : UInt8) :
    Silmaril.Wasi.Consequence.coreSeq Silmaril.Wasm.Numerics.Profile.spec
      Silmaril.Project.Languages.WasmExport.allHosts m "check" Silmaril.Wasi.Consequence.memberEnc Γ [c] ↔
      Silmaril.Project.ConsequenceSystems.WasmExport.checkRel m Γ c :=
  ⟨fun ⟨_, hw, h⟩ => by cases Option.some.inj hw; exact h, fun h => ⟨_, rfl, h⟩⟩

silmaril consequence_interpretation wasm.core.seq := Silmaril.Wasi.Consequence.coreInterp
  (doc := "A core module as a multiple-conclusion system Γ ⊢ Δ between byte lists, through the export and codec of the configuration (coreSeq: CoreConfig = profile, hosts, export name, codec)")
