module

import Silmaril.SSA.Isotope.BrookesLetParIter.Thms
import Silmaril.Proofs.SSA.Isotope.BrookesLetParIter.Regression

open Silmaril.Isotope.BrookesLetParIter Silmaril.Isotope.BrookesLetParIter.Regression

#print axioms instLawfulTypeModelSCType
#print axioms instInstructionModelInstrSCTypeBoolM
#print axioms pure_instruction_iff
#print axioms Silmaril.Semantics.Brookes.Behavior.map_eq_mapResult
#print axioms Silmaril.Semantics.Brookes.Behavior.parallelPairing
#print axioms pairing
#print axioms abort_empty
#print axioms acquire_free
#print axioms acquire_held
#print axioms release_owner
#print axioms release_nonowner
#print axioms denote_readOnce
#print axioms denote_program
#print axioms program_completes
#print axioms sound
#print axioms interpret_sound
#print axioms swap_program
