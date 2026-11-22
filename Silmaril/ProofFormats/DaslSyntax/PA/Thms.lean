module

public import Silmaril.ProofFormats.DaslSyntax.PA.Defs
public import Silmaril.ProofFormats.DaslSyntax.Thms

public section

namespace Silmaril.ProofFormats.DaslSyntax.PA

open Silmaril.Formats.Dasl
open Silmaril.Logic.Arithmetic

theorem theorems_subset_standardTruth {Name : Type} (store : Store Name) : theorems store ⊆ standardTruth store :=
  (formula 0).namesWhere_mono store (fun _ ⟨proof⟩ environment => paSound proof environment (by simp [Satisfies]))

end Silmaril.ProofFormats.DaslSyntax.PA
