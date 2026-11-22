module

public import Silmaril.ProofFormats.DaslSyntax.HOL.Defs
public import Silmaril.ProofFormats.DaslSyntax.Thms

public section

namespace Silmaril.Proofs.ProofFormats.DaslSyntax.HOL

open Silmaril.Formats.Dasl
open Silmaril.Logic.HOLLight
open Silmaril.ProofFormats.DaslSyntax
open Silmaril.ProofFormats.DaslSyntax.HOL
open Silmaril.Semantics.Naming (Binding)

theorem system_iff_of_set {Name : Type} {store : Store Name} {resolved : Name → Hyps → Prop}
    (source : Consequence.System Hyps Tm) (bound : store.Binding) (functional : Binding resolved)
    {listRoot setRoot result : Name} {premises : List Tm} {term : Tm}
    (listHit : assumptions.names store listRoot premises) (setHit : resolved setRoot premises.toFinset)
    (resultHit : tm.names store result term) :
    system (assumptions.named store) (tm.named store) (fun items => source items.toFinset) listRoot result ↔
      system (.encoded resolved) (tm.named store) source setRoot result :=
  (system_of_match (context := assumptions.named store) (conclusion := tm.named store)
    (source := fun items => source items.toFinset) (assumptions.named_binding bound)
    (tm.named_binding bound) listHit resultHit).trans
    (system_of_match (context := .encoded resolved) (conclusion := tm.named store)
      (source := source) functional (tm.named_binding bound) setHit resultHit).symm

end Silmaril.Proofs.ProofFormats.DaslSyntax.HOL
