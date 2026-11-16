module

public import Silmaril.Wasm.Component.DWiring.Defs
public import Silmaril.Games.DivLTS.Thms
public import Silmaril.Games.DPair.Thms
public import Silmaril.Games.DivComp.Thms
import Silmaril.Proofs.Wasm.Component.DWiring.Narrow

/-!
# Divergence-observing wiring: theorems

**Consistency with the ordinary denotation.** Forgetting divergence and
infinite plays gives back the ordinary wiring operations and denotations, all
by definition:

* `toStrategy_atSizes : (DStrategy.atSizes n k σ).toStrategy = atSizes n k σ.toStrategy`;
* `toStrategy_ext`, `toStrategy_dcoreNode`;
* `toStrategy_denUD : (c.denUD C).toStrategy = c.denU C.forget` (with
  `toStrategy_denNodesD`, `toStrategy_node_denD`, by mutual induction);
* `toStrategy_denD : (c.denD C).toStrategy = c.den C.forget`;
* `toStrategy_linked_denUD`, `toStrategy_program_denUD`.

**Divergence and infinite plays of `atSizes`.** Composition hides the moves
at the inner interfaces, which can create divergence from infinite hidden
chatter (`Silmaril.Games.DivComp`). The two handlers of `atSizes` behave
differently:

* `narrowH k` (on top) answers every question by exactly one call. A one-call
  handler on top (`OneCall`) makes at most one hidden move per visible move,
  so it cannot chatter: the composite diverges exactly where the strategy below
  diverges, along the handler (`DStrategy.div_comp_ofHandler`), and every
  infinite interaction is an infinite play (`DStrategy.inf_comp_ofHandler`).
* `widenH n` (below) is *not* a relabelling: a call of an out-of-range function
  is answered `none` at once, without a visible move. So `σ` on top of it can
  chatter: calling out-of-range functions forever makes the composite diverge.
  This is the only source of chatter (`chatter_widenH`): a chattering
  interaction plays an infinite play of `σ` that is eventually made of trap
  events (`EventuallyTrap`).

Hence `div_atSizes`: a divergence of `atSizes n k σ` is a divergence of `σ`
along both handlers, or trap chatter of `σ` below `widenH n`, seen through
`narrowH k`. When no infinite play of `σ` is eventually trap chatter,
divergence of `atSizes n k σ` is exactly the image of `σ.div`
(`div_atSizes_of_noTrap`). Every infinite play of `atSizes n k σ` comes from an
infinite play of `σ` (`inf_atSizes_sub`), and the infinite plays are the
visible limits of the infinite interactions (`inf_atSizes`).

Proofs are in `Silmaril.Proofs.Wasm.Component.DWiring`.
-/

public section

namespace Silmaril.Wasm.Component

open Silmaril.Games
open Silmaril.Games.DStrategy (InfInteraction)

namespace DStrategy

/-- **Consistency of `atSizes`.** -/
@[simp] theorem toStrategy_atSizes (n k : Nat) (σ : DStrategy sigU sigU) :
    (atSizes n k σ).toStrategy = Component.atSizes n k σ.toStrategy := rfl

/-- **Consistency of `ext`.** -/
@[simp] theorem toStrategy_ext {X : Sig.{0}} (e : Nat) (D : DStrategy X sigU)
    (N : DStrategy sigU sigU) :
    (ext e D N).toStrategy = Component.ext e D.toStrategy N.toStrategy := rfl

end DStrategy

variable {M : Type} [CoreModule M]

/-- Consistency of core instances. -/
@[simp] theorem toStrategy_dcoreNode (C : DCoreSem M) (e : Nat) (m : M) (args : List Impl) :
    (dcoreNode C e m args).toStrategy = coreNode C.forget e m args := rfl

mutual
/-- **Consistency of the component denotation over `sigU`.** -/
theorem toStrategy_denUD (C : DCoreSem M) : ∀ c : Comp M,
    (c.denUD C).toStrategy = c.denU C.forget
  | .mk I ns xs => by
    rw [Comp.denUD, Comp.denU]
    exact congrArg (fun S => S.comp (Strategy.ofHandler (exportsH (envAfter I.length ns) xs)))
      (toStrategy_denNodesD C I.length ns (DStrategy.ofHandler (maskH I.length)))

/-- Consistency of the extension by nodes. -/
theorem toStrategy_denNodesD (C : DCoreSem M) {X : Sig.{0}} :
    ∀ (e : Nat) (ns : List (Node M)) (D : DStrategy X sigU),
      (denNodesD C e ns D).toStrategy = denNodes C.forget e ns D.toStrategy
  | _, [], _ => by rw [denNodesD, denNodes]
  | e, n :: ns, D => by
    rw [denNodesD, denNodes, toStrategy_denNodesD C (e + n.width) ns,
      DStrategy.toStrategy_ext, toStrategy_node_denD C e n]

/-- Consistency of node denotations. -/
theorem toStrategy_node_denD (C : DCoreSem M) :
    ∀ (e : Nat) (n : Node M), (Node.denD C e n).toStrategy = Node.den C.forget e n
  | _, .core _ _ => by rw [Node.denD, Node.den]; rfl
  | e, .inst c args => by
    rw [Node.denD, Node.den, ← toStrategy_denUD C c]
    rfl
end

/-- **Consistency of the component denotation.** -/
theorem toStrategy_denD (C : DCoreSem M) (c : Comp M) :
    (c.denD C).toStrategy = c.den C.forget := by
  rw [Comp.denD, Comp.den, DStrategy.toStrategy_atSizes, toStrategy_denUD]

/-- Consistency of the extension by core instances. -/
theorem toStrategy_linked_go (C : DCoreSem M) {X : Sig.{0}} :
    ∀ (e : Nat) (ns : List (M × List Impl)) (D : DStrategy X sigU),
      (Linked.denUD.go C e ns D).toStrategy = Linked.denU.go C.forget e ns D.toStrategy
  | _, [], _ => rfl
  | e, n :: ns, D => by
    rw [Linked.denUD.go, Linked.denU.go, toStrategy_linked_go C _ ns]
    rfl

/-- Consistency of the flat component denotation. -/
theorem toStrategy_linked_denUD (C : DCoreSem M) (l : Linked M) :
    (l.denUD C).toStrategy = l.denU C.forget := by
  rw [Linked.denUD, Linked.denU]
  exact congrArg
    (fun S => S.comp (Strategy.ofHandler (exportsH (linkedEnv l.imports.length l.nodes) l.exports)))
    (toStrategy_linked_go C l.imports.length l.nodes (DStrategy.ofHandler (maskH l.imports.length)))

/-- Consistency of the program denotation. -/
theorem toStrategy_program_denUD (C : DCoreSem M) (p : Program M) :
    (p.denUD C).toStrategy = p.denU C.forget := by
  unfold Program.denUD Program.denU
  cases p.observe with
  | none => exact toStrategy_denUD C _
  | some obs => rw [← toStrategy_denUD]; rfl

/-! ## Handlers with at most one call -/

theorem oneCall_widenH (n : Nat) : OneCall (widenH n) :=
  Silmaril.Proofs.Wasm.Component.DWiring.oneCall_widenH n

theorem oneCall_narrowH (k : Nat) : OneCall (narrowH k) :=
  Silmaril.Proofs.Wasm.Component.DWiring.oneCall_narrowH k

theorem oneCall_splitH (e : Nat) : OneCall (splitH e) :=
  Silmaril.Proofs.Wasm.Component.DWiring.oneCall_splitH e

theorem oneCall_selectH (obs : List Nat) : OneCall (selectH obs) :=
  Silmaril.Proofs.Wasm.Component.DWiring.oneCall_selectH obs

namespace DStrategy

variable {X E F G : Sig.{0}}

/-- **No chatter below a one-call handler**: the composite diverges exactly
where the strategy below diverges. -/
theorem div_comp_ofHandler {h : Handler E F} (hh : OneCall h) (δ : DStrategy X E) :
    (δ.comp (DStrategy.ofHandler h)).div =
      {p | ∃ s t, Zip s t p ∧ s ∈ δ.div ∧ t ∈ Strategy.ofHandler h} :=
  Silmaril.Proofs.Wasm.Component.DWiring.comp_ofHandler_div hh δ

/-- Below a one-call handler, every infinite interaction is an infinite play. -/
theorem inf_comp_ofHandler {h : Handler E F} (hh : OneCall h) (δ : DStrategy X E) :
    (δ.comp (DStrategy.ofHandler h)).inf =
      {I | ∃ i : InfInteraction δ (DStrategy.ofHandler h), I = i.p.lim} :=
  Silmaril.Proofs.Wasm.Component.DWiring.comp_ofHandler_inf hh δ

/-- With a handler below, divergence is divergence of the strategy on top or
hidden chatter. -/
theorem div_ofHandler_comp (h : Handler E F) (σ : DStrategy F G) :
    ((DStrategy.ofHandler h).comp σ).div =
      {p | ∃ s t, Zip s t p ∧ s ∈ Strategy.ofHandler h ∧ t ∈ σ.div} ∪
      {p | ∃ i : InfInteraction (DStrategy.ofHandler h) σ, ∀ m, i.p m = p} :=
  Silmaril.Proofs.Wasm.Component.DWiring.ofHandler_comp_div h σ

/-- With a one-call handler below, an infinite interaction whose visible part
grows forever makes the strategy on top move forever, so it plays one of its
infinite plays. -/
theorem lim_t_of_oneCall {h : Handler E F} (hh : OneCall h) {σ : DStrategy F G}
    (i : InfInteraction (DStrategy.ofHandler h) σ) (hp : i.p.Unbounded) :
    i.t.Unbounded ∧ i.t.lim ∈ σ.inf :=
  have ht := Silmaril.Proofs.Wasm.Component.DWiring.unbounded_t hh i hp
  ⟨ht, i.lim_t ht⟩

end DStrategy

/-- **Chatter below `widenH` is trap chatter.** An infinite interaction of
`widenH n` with `σ` whose visible part stays `p` plays an infinite play of `σ`
which from some point on only calls out-of-range functions and receives `none`. -/
theorem chatter_widenH {G : Sig.{0}} {n : Nat} {σ : DStrategy sigU G}
    (i : InfInteraction (DStrategy.ofHandler (widenH n)) σ)
    {p : List (Move (sigN n) G)} (hp : ∀ m, i.p m = p) :
    i.t.lim ∈ σ.inf ∧ EventuallyTrap n i.t.lim :=
  Silmaril.Proofs.Wasm.Component.DWiring.chatter_widenH i hp

/-! ## `atSizes` -/

namespace DStrategy

variable {n k : Nat} {σ : DStrategy sigU sigU}

/-- **Divergence of `atSizes`**: `narrowH k` adds no chatter; below it, a
divergence of `σ` seen through `widenH n`, or chatter below `widenH n`. -/
theorem div_atSizes :
    (atSizes n k σ).div = {p | ∃ s t, Zip s t p ∧ t ∈ Strategy.ofHandler (narrowH k) ∧
      ((∃ u v, Zip u v s ∧ u ∈ Strategy.ofHandler (widenH n) ∧ v ∈ σ.div) ∨
        ∃ i : InfInteraction (DStrategy.ofHandler (widenH n)) σ, ∀ m, i.p m = s)} :=
  Silmaril.Proofs.Wasm.Component.DWiring.div_atSizes

/-- **Without trap chatter, `atSizes` diverges exactly where `σ` does**, along
the two handlers. -/
theorem div_atSizes_of_noTrap (hσ : ∀ I ∈ σ.inf, ¬ EventuallyTrap n I) :
    (atSizes n k σ).div = {p | ∃ s t u v, Zip u v s ∧ Zip s t p ∧
      u ∈ Strategy.ofHandler (widenH n) ∧ t ∈ Strategy.ofHandler (narrowH k) ∧
        v ∈ σ.div} :=
  Silmaril.Proofs.Wasm.Component.DWiring.div_atSizes_of_noTrap hσ

/-- **Infinite plays of `atSizes`**: the visible limits of all infinite
interactions with `narrowH k`. -/
theorem inf_atSizes :
    (atSizes n k σ).inf =
      {I | ∃ i : InfInteraction ((DStrategy.ofHandler (widenH n)).comp σ)
        (DStrategy.ofHandler (narrowH k)), I = i.p.lim} :=
  inf_comp_ofHandler (oneCall_narrowH k) _

/-- **Infinite plays of `atSizes` come from infinite plays of `σ`.** -/
theorem inf_atSizes_sub {I : Set (List (Move (sigN n) (sigN k)))}
    (hI : I ∈ (atSizes n k σ).inf) :
    ∃ i : InfInteraction ((DStrategy.ofHandler (widenH n)).comp σ)
        (DStrategy.ofHandler (narrowH k)),
      I = i.p.lim ∧ ∃ j : InfInteraction (DStrategy.ofHandler (widenH n)) σ,
        i.s.lim = j.p.lim ∧ j.t.Unbounded ∧ j.t.lim ∈ σ.inf :=
  Silmaril.Proofs.Wasm.Component.DWiring.inf_atSizes_sub hI

end DStrategy

end Silmaril.Wasm.Component
