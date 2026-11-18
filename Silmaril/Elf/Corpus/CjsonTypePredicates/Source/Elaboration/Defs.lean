module
public import Silmaril.Elf.Corpus.CjsonTypePredicates.Source.Defs
public import Silmaril.Elf.Corpus.CjsonTypePredicates.Defs
import Silmaril.Proofs.Elf.Corpus.CjsonTypePredicates.Source
@[expose] public section
namespace Silmaril.Elf.Corpus.CjsonTypePredicates.Source.Elaboration
theorem succeeds : (Source.inputs.run Source.ail).toOption.isSome = true :=
  Silmaril.Proofs.Elf.Corpus.CjsonTypePredicates.succeeds

/-- The actual successful elaboration result. No default body on failure. -/
def core : Silmaril.Cerberus.Codec.FileBindings :=
  (Source.inputs.run Source.ail).toOption.get
    succeeds
/-- A predicate body and its actual parameter type from the computed Core. -/
def function (p : Predicate) : Silmaril.Project.Shapes.C.CFn Source.signature where
  file := core.toFile
  params := Silmaril.Project.CompilesTo.paramsOf core p.name
  body := (Silmaril.Project.CompilesTo.procParts core p.name).2

/-- Layout of the actual elaborated struct and its actual `type` member. -/
def layoutSignature : Option (Int × Int × Option Int) := do
  let (tag, _) ← core.tagDefs.head?
  let layout ← (Silmaril.Cerberus.Mem.Concrete.typeLayout 64 core.toFile.tagDefs
    (.mk [] (.struct tag))).toOption
  pure (layout.size, layout.align,
    (layout.members.find? fun (name, _, _) => name.key == "type").map fun (_, _, offset) => offset)

end Silmaril.Elf.Corpus.CjsonTypePredicates.Source.Elaboration
