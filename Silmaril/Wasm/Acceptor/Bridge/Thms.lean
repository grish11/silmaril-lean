module

public import Silmaril.Wasm.Acceptor.Bridge.Defs
public import Silmaril.Wasm.Component.Reference.Sound.Defs
import Silmaril.Proofs.Wasm.Acceptor.Bridge

/-!
# The acceptor kit: component soundness from Core soundness

For the reference Component Model at every numerics profile `P` and every component choice
profile `prof`. Proof in `Silmaril.Proofs.Wasm.Acceptor.Bridge`.

* **`CheckerExport.sound`**: for a component with a `Kit` and an export with its Core
  obligation (`CoreSound`), a behaviour of the reference machine that instantiates `c.toRef`,
  calls the export on the values of `p` and `q` and returns `true` gives `Goal p q`;
* **`CheckerExport.sound_accepts`**, **`CheckerExport.sound_lang`**: when `Goal p q` gives
  `chk p q = true` for a Lean checker `chk`, an accepting call puts `p` in `Accepts chk`, and in
  every language `L ⊇ Accepts chk`.

Only accepting behaviours are characterised: traps, divergence and `false` answers impose
nothing.
-/

@[expose] public section

namespace Silmaril.Wasm.Acceptor

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.ListLift (ListComp LVal)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Logic.SAT.Carrier (Accepts)

/-- **An accepting call of a checker export means `Goal`.** -/
theorem CheckerExport.sound {c : ListComp} {α β : Type} (K : Kit c) (e : CheckerExport c α β)
    (hc : e.CoreSound K) (P : Profile) (prof : ProfileKind) (p : α) (q : β)
    (h : Outcome.returns (some [.bool true]) ∈ exportBehaviours prof (refHost P) () c.toRef []
      e.x.name ((e.enc p q).map LVal.toRef)) :
    e.Goal p q :=
  Silmaril.Proofs.Wasm.Acceptor.CheckerExport.sound K e hc P prof p q h

/-- **An accepting call puts the problem in `Accepts chk`.** -/
theorem CheckerExport.sound_accepts {c : ListComp} {α β : Type} (K : Kit c)
    (e : CheckerExport c α β) (hc : e.CoreSound K) {chk : α → β → Bool}
    (hg : ∀ p q, e.Goal p q → chk p q = true) (P : Profile) (prof : ProfileKind) (p : α) (q : β)
    (h : Outcome.returns (some [.bool true]) ∈ exportBehaviours prof (refHost P) () c.toRef []
      e.x.name ((e.enc p q).map LVal.toRef)) :
    p ∈ Accepts chk :=
  ⟨q, hg p q (e.sound K hc P prof p q h)⟩

/-- **An accepting call puts the problem in every language of a sound Lean checker.** -/
theorem CheckerExport.sound_lang {c : ListComp} {α β : Type} (K : Kit c)
    (e : CheckerExport c α β) (hc : e.CoreSound K) {chk : α → β → Bool} {L : Set α}
    (hg : ∀ p q, e.Goal p q → chk p q = true) (hL : Accepts chk ⊆ L) (P : Profile)
    (prof : ProfileKind) (p : α) (q : β)
    (h : Outcome.returns (some [.bool true]) ∈ exportBehaviours prof (refHost P) () c.toRef []
      e.x.name ((e.enc p q).map LVal.toRef)) :
    p ∈ L :=
  hL (e.sound_accepts K hc hg P prof p q h)

end Silmaril.Wasm.Acceptor
