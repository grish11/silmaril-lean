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

* **`CheckerExport.rejects`**, **`CheckerExport.rejects_none`**: the contrapositive, for
  rejection. If `Goal p q` implies a property `R p q` (for instance that a decoder of the problem
  or of the certificate succeeds, `D p ≠ none`), then for arguments with `¬ R p q` **no
  behaviour of the reference machine returns `true`**.

Only accepting behaviours are characterised: traps, divergence and `false` answers impose
nothing. In particular "rejected" means "never answers `true`": that such a call answers `false`
(rather than trapping or diverging) is not claimed.
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

/-- **Arguments outside the goal are never accepted**: when `Goal p q` implies `R p q`, no
reference behaviour of a call on arguments with `¬ R p q` returns `true`. -/
theorem CheckerExport.rejects {c : ListComp} {α β : Type} (K : Kit c) (e : CheckerExport c α β)
    (hc : e.CoreSound K) {R : α → β → Prop} (hg : ∀ p q, e.Goal p q → R p q) (P : Profile)
    (prof : ProfileKind) {p : α} {q : β} (hn : ¬ R p q) :
    Outcome.returns (some [.bool true]) ∉ exportBehaviours prof (refHost P) () c.toRef []
      e.x.name ((e.enc p q).map LVal.toRef) :=
  fun h => hn (hg p q (e.sound K hc P prof p q h))

/-- **Undecodable arguments are never accepted**: when `Goal p q` implies that a decoder `D`
succeeds on `f p q` (the problem, the certificate, or both), no reference behaviour of a call
on arguments with `D (f p q) = none` returns `true`. -/
theorem CheckerExport.rejects_none {c : ListComp} {α β γ δ : Type} (K : Kit c)
    (e : CheckerExport c α β) (hc : e.CoreSound K) {f : α → β → γ} {D : γ → Option δ}
    (hg : ∀ p q, e.Goal p q → D (f p q) ≠ none) (P : Profile) (prof : ProfileKind) {p : α}
    {q : β} (hD : D (f p q) = none) :
    Outcome.returns (some [.bool true]) ∉ exportBehaviours prof (refHost P) () c.toRef []
      e.x.name ((e.enc p q).map LVal.toRef) :=
  e.rejects K hc (R := fun p q => D (f p q) ≠ none) hg P prof (not_not_intro hD)

end Silmaril.Wasm.Acceptor
