module

public import Silmaril.Formats.Dasl.Resolve.Defs
public import Silmaril.Semantics.Naming.Dependency.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl

open Silmaril.Semantics.Naming

variable {Name : Type}

def Link.ofDependencyChild : Child Name → Link Name
  | .inl name => .obj name
  | .inr name => .blob name

def Store.dependency (store : Store Name) : Dependency Name (Shallow Name) ByteArray :=
  ⟨store, fun tree => {child | Link.ofDependencyChild child ∈ tree.directLinks}⟩

end Silmaril.Formats.Dasl
