module

public import Silmaril.Project.Registry.Institution.Defs
public import Silmaril.X86.BinInstitution.Defs
public import Silmaril.X86.Institution.Defs

/-!
# Logic graph: the institutions and rooms of `Silmaril.X86`

Registrations of the institution and room declarations of the `X86` tree (`docs/projects/logic-graph.md`): Lean checks each declaration's type; a family is registered as a family.
-/

silmaril institution x86.bin_institution.bundled := Silmaril.X86.BinInstitution.bundled
silmaril institution x86.institution.bundled := Silmaril.X86.Institution.bundled
silmaril room x86.bin_institution.room := Silmaril.X86.BinInstitution.room
silmaril room x86.institution.room := Silmaril.X86.Institution.room
