module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq.BuildA

/-!
# The right-to-left direction, by source

* `sessDivs_subset_union`: a diverging session call of the specification is one of the three
  sources (`sessDivsB`, `sessDivsA`, `sessDivsC`);
* `div_denD_of_sessDivs_of`: the right-to-left direction, from `div_denD_of_sessDivsB`,
  `div_denD_of_sessDivsA` and `Linked2.Task.ChatterBuild` for the third source.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val

/-- **The three sources of a diverging session call.** -/
theorem sessDivs_subset_union (P : Profile) (l : Linked2)
    (calls : List (Fin l.imp.exports.length × List IVal)) (j : Fin l.imp.exports.length)
    (vs : List IVal) :
    Linked2.sessDivs P l calls j vs ⊆
      Linked2.sessDivsB P l calls j vs ∪ Linked2.sessDivsA P l calls j vs ∪
        Linked2.sessDivsC P l calls j vs := by
  rintro _ ⟨Ie, Ii, u, π, hIe, hIi, hS, d, s, t, π₁, hj, hv, hOk, hp, hr, hB | hA | hC⟩
  · exact .inl (.inl ⟨Ie, Ii, u, π, hIe, hIi, hS, d, s, t, π₁, hj, hv, hOk, hp, hr, hB⟩)
  · exact .inl (.inr ⟨Ie, Ii, u, π, hIe, hIi, hS, d, s, t, π₁, hj, hv, hOk, hp, hr, hA⟩)
  · exact .inr ⟨Ie, Ii, u, π, hIe, hIi, hS, d, s, t, π₁, hj, hv, hOk, hp, hr, hC⟩

/-- **Right to left, given the chatter build.** -/
theorem div_denD_of_sessDivs_of (P : Profile) {l : Linked2} (hl : l.Adequate)
    (hC : Linked2.Task.ChatterBuild P l) {calls : List (Fin l.imp.exports.length × List IVal)}
    {outs : List (Option (List IVal))} (ht : SimpleI.TypedCalls l.imp calls)
    (hlen : calls.length = outs.length) {j : Fin l.imp.exports.length} {vs : List IVal}
    (hck : ValTy.checkList l.imp.exports[j].ty.params vs = true)
    (h : outs ∈ Linked2.sessDivs P l calls j vs) :
    Linked2.sessMoves l calls outs ++ [.inr (.ask (l.topQ j vs))] ∈
      (l.toComp.denD (impSemD P)).div := by
  rcases sessDivs_subset_union P l calls j vs h with (hB | hA) | hX
  · exact div_denD_of_sessDivsB P hl hB
  · exact div_denD_of_sessDivsA P hl hA
  · exact hC calls outs ht hlen j vs hck hX

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq
