module

public import Silmaril.Logic.CommonLogic.FirstOrder.Expansion.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.CommonLogic.FirstOrderExpansion

open Silmaril.Logic.CommonLogic.FirstOrder
open Silmaril.Logic.CommonLogic
open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples

/-- Exact object expansion, not just an isomorphism of underlying carriers. -/
theorem decode_expand {S : Signature} (M : FOL.Structure (publicSignature S))
    (d : M.carrier ()) : decode (expand M d) = M := by
  rcases M with ⟨⟨carrier, op⟩, rel⟩
  have hc : (fun _ : Unit => carrier ()) = carrier := funext fun s => by cases s; rfl
  generalize hd : carrier () = D at hc
  clear hd
  cases hc
  dsimp only [decode, expand]
  congr 1
  · congr 1
    funext n w s o args
    cases s
    have hw : w = fun _ => () := funext fun i => Subsingleton.elim _ _
    cases hw
    simp
  · funext n w r args
    have hw : w = fun _ => () := funext fun i => Subsingleton.elim _ _
    cases hw
    simp


end Silmaril.Proofs.Logic.CommonLogic.FirstOrderExpansion
