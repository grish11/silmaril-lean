module

public import Silmaril.SSA.MLIR.WasmSSA.GC.Defs
import Silmaril.Proofs.SSA.MLIR.WasmSSA.GC.RoundTrip

public section

namespace Silmaril.MLIR.WasmSSA.GC

@[simp] theorem project_embed {params Γ : List IntType} {result : IntType}
    (block : WasmSSA.Block params result Γ) : project? (embed block) = some block :=
  Proofs.SSA.MLIR.WasmSSA.GC.project_embed block

/-- Projection succeeds exactly on embedded core blocks, with literal syntax
equality in both directions. -/
theorem project_eq_some_iff {params Γ : List IntType} {result : IntType}
    {block : Block params (.core result) (Γ.map ValType.core)}
    {core : WasmSSA.Block params result Γ} : project? block = some core ↔ embed core = block :=
  ⟨Proofs.SSA.MLIR.WasmSSA.GC.embed_of_project, fun h => h ▸ project_embed core⟩

theorem embed_injective {params Γ : List IntType} {result : IntType}
    {left right : WasmSSA.Block params result Γ} (h : embed left = embed right) : left = right :=
  Option.some.inj ((project_embed left).symm.trans ((congrArg project? h).trans (project_embed right)))

end Silmaril.MLIR.WasmSSA.GC
