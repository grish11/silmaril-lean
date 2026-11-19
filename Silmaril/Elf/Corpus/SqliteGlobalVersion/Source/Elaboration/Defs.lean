module
public import Silmaril.Elf.Corpus.SqliteGlobalVersion.Source.Defs
import Silmaril.Proofs.Elf.Corpus.SqliteGlobalVersion.Source
@[expose] public section
namespace Silmaril.Elf.Corpus.SqliteGlobalVersion.Source.Elaboration
theorem succeeds : (Source.inputs.run Source.ail).toOption.isSome = true :=
  Silmaril.Proofs.Elf.Corpus.SqliteGlobalVersion.succeeds
def core : Silmaril.Cerberus.Codec.FileBindings :=
  (Source.inputs.run Source.ail).toOption.get succeeds
/-- Actual no-argument pointer-returning procedure and its actual global
initializer. Failed shape/metadata lookup remains `none`. -/
def actual : Option (Silmaril.Cerberus.Sym × Silmaril.Cerberus.Ctype ×
    Silmaril.Cerberus.Core.Dynamics.EE × Silmaril.Cerberus.Core.Dynamics.EE) := do
  let (symbol, .procedure _ _ (.loaded .pointer) [] body) ←
      Silmaril.Project.Shapes.C.procedureNamed core "sqlite3_libversion" | none
  let (_, info) ← core.funInfo.find? (fun entry => entry.1.key == symbol.key)
  let .mk _ (.pointer _ (.mk _ (.basic (.integer .char)))) := info.2.2.1 | none
  unless info.2.2.2.1.isEmpty && !info.2.2.2.2.1 && !info.2.2.2.2.2 do none
  let [(global, .definition (_, type) initializer)] := core.globs | none
  let .mk _ (.array (.mk _ (.basic (.integer .char))) (some 7)) := type | none
  return (global, type, initializer, body)
end Silmaril.Elf.Corpus.SqliteGlobalVersion.Source.Elaboration
