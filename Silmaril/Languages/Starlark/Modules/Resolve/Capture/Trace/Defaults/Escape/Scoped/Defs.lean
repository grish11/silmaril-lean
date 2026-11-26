module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped

open Functions

/-- Use the same wrapper shape with a compositional sequence before the
child's final read. The wrapper still has just one required parameter. -/
structure Spec where
  wrapper : Escape.Spec
  assignments : List (String × Lowering.Resolve.SourceExpr)

@[expose] def Spec.child (spec : Spec) : Defaults.Body.Definition :=
  ⟨spec.wrapper.childName, spec.wrapper.child.parameters,
    spec.assignments.foldr (fun (name, rhs) rest => .assign name rhs rest)
      (.ret (.scalar (.read spec.wrapper.returned)))⟩

@[expose] def Spec.enclosing (spec : Spec) : List String := [spec.wrapper.parameter, spec.wrapper.childName]

@[expose] def Spec.command (spec : Spec) : Command := spec.wrapper.commandWith spec.child.body.source

/-- The independently selected capture list contains exactly the
wrapper parameter. The child name and module captures stay outside
this bounded integration. -/
structure Plan (globals : List String) (spec : Spec) where
  body : Defaults.Body.Plan globals spec.child spec.enclosing
  captured : body.free = [⟨fileSlot spec.wrapper.parameter, fileSlot spec.wrapper.parameter⟩]

structure Admitted (globals : List String) (spec : Spec) : Prop where
  names : Escape.WrapperNames spec.wrapper
  plan : Nonempty (Plan globals spec)

@[expose] def capturesAt (spec : Spec) (address : Nat) : List Lists.Capture :=
  [⟨fileSlot spec.wrapper.parameter, address, true⟩]

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped
