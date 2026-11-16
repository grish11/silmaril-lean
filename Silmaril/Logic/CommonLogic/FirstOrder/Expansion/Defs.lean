module

public import Silmaril.Logic.CommonLogic.FirstOrder.Thms

@[expose] public section

namespace Silmaril.Logic.CommonLogic.FirstOrder

open Silmaril.Logic.CommonLogic
open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples

/-- Chosen filler values only complete the CL operations outside the translated fragment.
No natural or functorial choice of these fillers is asserted. -/
noncomputable def expand {S : Signature} (M : FOL.Structure (publicSignature S))
    (d : M.carrier ()) : Core.Model (clSignature S) where
  Reference := M.carrier () ⊕ Heads S
  Discourse := M.carrier ()
  nonempty := ⟨d⟩
  embed := Sum.inl
  injective := Sum.inl_injective
  discourse := Empty.elim
  nondiscourse := Sum.inr
  outside _ _ := by intro h; cases h
  sequence := Empty.elim
  function r xs := match r with
    | .inr (.inl ⟨n,o⟩) =>
        if h : xs.length = n then M.op (w := fun _ => ()) (s := ()) o
          (fun i => xs.get ⟨i.val, by simpa only [h] using i.isLt⟩) else d
    | _ => d
  relation r xs := match r with
    | .inr (.inr ⟨n,p⟩) =>
        if h : xs.length = n then M.rel (w := fun _ => ()) p
          (fun i => xs.get ⟨i.val, by simpa only [h] using i.isLt⟩) else False
    | _ => False


end Silmaril.Logic.CommonLogic.FirstOrder
