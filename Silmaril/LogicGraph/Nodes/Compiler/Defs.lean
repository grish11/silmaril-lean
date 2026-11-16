module

public import Silmaril.Compiler.Native.Correctness.AdditionInstitution.Defs
public import Silmaril.Compiler.Native.Correctness.ArithmeticInstitution.Defs
public import Silmaril.Compiler.Native.Optimize.AddressInstitution.Defs
public import Silmaril.Compiler.Native.Optimize.EffectsInstitution.Defs
public import Silmaril.Compiler.Native.Optimize.FiniteInstitution.Defs
public import Silmaril.Compiler.Native.Optimize.FloatingInstitution.Defs
public import Silmaril.Compiler.Native.Optimize.LambdaSSA.Institution.Defs
public import Silmaril.Compiler.Native.Optimize.SlotsInstitution.Defs
public import Silmaril.Project.Registry.Institution.Defs

/-!
# Logic graph: the institutions and rooms of `Silmaril.Compiler`

Registrations of the institution and room declarations of the `Compiler` tree (`docs/projects/logic-graph.md`): Lean checks each declaration's type; a family is registered as a family.
-/

silmaril institution compiler.native.correctness.addition_institution.source_institution := Silmaril.Compiler.Native.Correctness.AdditionInstitution.sourceInstitution
silmaril institution compiler.native.correctness.addition_institution.target_institution := Silmaril.Compiler.Native.Correctness.AdditionInstitution.targetInstitution
silmaril institution compiler.native.correctness.arithmetic_institution.source_institution := Silmaril.Compiler.Native.Correctness.ArithmeticInstitution.sourceInstitution
silmaril institution compiler.native.correctness.arithmetic_institution.target_institution := Silmaril.Compiler.Native.Correctness.ArithmeticInstitution.targetInstitution
silmaril institution compiler.native.optimize.address_institution.source_institution := Silmaril.Compiler.Native.Optimize.AddressInstitution.sourceInstitution
silmaril institution compiler.native.optimize.address_institution.target_institution := Silmaril.Compiler.Native.Optimize.AddressInstitution.targetInstitution
silmaril institution compiler.native.optimize.effects_institution.source_institution := Silmaril.Compiler.Native.Optimize.EffectsInstitution.sourceInstitution
silmaril institution compiler.native.optimize.effects_institution.target_institution := Silmaril.Compiler.Native.Optimize.EffectsInstitution.targetInstitution
silmaril institution compiler.native.optimize.finite_institution.institution := Silmaril.Compiler.Native.Optimize.FiniteInstitution.institution
silmaril institution compiler.native.optimize.floating_institution.source_institution := Silmaril.Compiler.Native.Optimize.FloatingInstitution.sourceInstitution
silmaril institution compiler.native.optimize.floating_institution.target_institution := Silmaril.Compiler.Native.Optimize.FloatingInstitution.targetInstitution
silmaril institution compiler.native.optimize.lambda_ssa.institution.institution := Silmaril.Compiler.Native.Optimize.LambdaSSA.Institution.institution
silmaril institution compiler.native.optimize.slots_institution.source_institution := Silmaril.Compiler.Native.Optimize.SlotsInstitution.sourceInstitution
silmaril institution compiler.native.optimize.slots_institution.target_institution := Silmaril.Compiler.Native.Optimize.SlotsInstitution.targetInstitution
