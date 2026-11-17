module

public import Silmaril.Wasm.Acceptor.Bridge.Defs
public import Silmaril.Wasm.Component.Reference.ListLift.Thms
public import Silmaril.Wasm.Component.Reference.ListLift.Bump.Thms

@[expose] public section

/-!
# The acceptor kit: component soundness from Core soundness (proofs)

`CheckerExport.sound`: `acceptSound` gives the lowering and the nonzero core run,
`params_holds` with the kit's bump allocator gives a store of the invariant whose memory holds
the arguments, and the Core obligation gives `Goal`. A Silmaril addition.
-/

namespace Silmaril.Proofs.Wasm.Acceptor

open Silmaril.Wasm.Acceptor
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.ListLift
open Silmaril.Wasm.Numerics (Profile)

theorem CheckerExport.sound {c : ListComp} {α β : Type} (K : Kit c) (e : CheckerExport c α β)
    (hc : e.CoreSound K) (P : Profile) (prof : ProfileKind) (p : α) (q : β)
    (h : Outcome.returns (some [.bool true]) ∈ exportBehaviours prof (refHost P) () c.toRef []
      e.x.name ((e.enc p q).map LVal.toRef)) :
    e.Goal p q := by
  obtain ⟨s, fl, s', f', r, hL, hS, hr⟩ :=
    acceptSound c P prof K.I K.good K.inst e.x e.mem (e.enc p q) (e.typed p q) h
  obtain ⟨t, hI, -, -, hF⟩ := params_holds (K.bump P) hL K.init
  exact hc P p q s t fl s' f' r hI hF hS hr

end Silmaril.Proofs.Wasm.Acceptor
