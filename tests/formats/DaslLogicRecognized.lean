module

import Silmaril.ProofFormats.DaslSyntax.Language.Thms
import Silmaril.ProofFormats.DaslSyntax.PA.Defs

open Silmaril.Formats.Dasl
open Silmaril.ProofFormats.DaslSyntax
open Silmaril.Logic.Arithmetic (PAProof Valid)

example {Name : Type} (store : Store Name) :
    PA.theorems store = Recognized store (fun value =>
      value ∈ (PA.formula 0).language (fun sentence => Nonempty (PAProof [] sentence))) :=
  (PA.formula 0).namesWhere_eq_recognized store _

example {Name : Type} (store : Store Name) :
    PA.standardTruth store = Recognized store (fun value => value ∈ (PA.formula 0).language Valid) :=
  (PA.formula 0).namesWhere_eq_recognized store _

#print axioms Syntax.namesWhere_eq_recognized
