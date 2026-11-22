module

public import Silmaril.ProofFormats.DaslSyntax.FOL.Defs
public import Silmaril.ProofFormats.DaslSyntax.Thms
public import Silmaril.Logic.Consequence.FirstOrder.Derivation.Thms

public section

namespace Silmaril.ProofFormats.DaslSyntax.FOL

open Silmaril.Formats.Dasl
open Silmaril.Logic.Institution.Examples.UFOL
open Silmaril.Consequence.FirstOrder.ND (treeDerives_holds)

theorem theorems_subset_valid {Name : Type} {sig : Signature} [∀ arity, DecidableEq (sig.Op arity)]
    [∀ arity, DecidableEq (sig.Rel arity)] (store : Store Name) (labels : Labels sig) :
    theorems store labels ⊆ valid store labels :=
  (formula labels 0).namesWhere_mono store (fun _ proof model => treeDerives_holds proof model (by simp))

end Silmaril.ProofFormats.DaslSyntax.FOL
