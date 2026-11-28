module

import Silmaril.Proofs.Logic.BrookesSC.TreeSC.Regression

open Silmaril.Semantics.Brookes
open Silmaril.Logic.BrookesSC.TreeSC
open Silmaril.Proofs.Logic.BrookesSC.TreeSC.Regression

#print axioms Trace.mapStores
#print axioms Trace.mapStores_inverse
#print axioms Reduces.mapStores
#print axioms Behavior.transport
#print axioms Behavior.transport_accepts_iff
#print axioms Behavior.transport_atomic
#print axioms Behavior.transport_ret
#print axioms Behavior.transport_bind
#print axioms Behavior.transport_completes_iff
#print axioms world
#print axioms storeEquiv
#print axioms accessMode
#print axioms signature
#print axioms encode
#print axioms inequation
#print axioms encode_translate
#print axioms inequation_translate
#print axioms eval_encode
#print axioms eval_encode_reduct
#print axioms satisfies_iff
#print axioms satisfies_reduct
#print axioms eval_encode_completes_iff_sc
#print axioms translated_increment
#print axioms accepts_gapped_increment
#print axioms translated_inequation_fails
