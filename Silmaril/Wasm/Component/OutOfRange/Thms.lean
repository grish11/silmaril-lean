module

public import Silmaril.Wasm.Component.OutOfRange.Defs
public import Silmaril.Wasm.Component.DWiringChatter2.Thms
import Silmaril.Proofs.Wasm.Component.OutOfRange.Trap
import Silmaril.Proofs.Wasm.Component.OutOfRange.Spin
import Silmaril.Proofs.Wasm.Component.OutOfRange.Mask
import Silmaril.Proofs.Wasm.Component.OutOfRange.Ext

/-!
# Out-of-range chatter: when wiring creates divergence

`DStrategy.atSizes n k σ` puts `σ` above `widenH n`, which answers a call of an
out-of-range function (index `≥ n`) with the trap answer `none` at once, with
no visible move. `Silmaril.Wasm.Component.DWiringLaws.Thms` shows that the
divergences of `atSizes n k σ` are the divergences of `σ`, plus **trap
chatter** (`TrapChatter`): `σ` calling out-of-range functions forever and
receiving `none` each time (`div_atSizes_iff`).

**Trap chatter is not a trap.** A Wasm trap is an observable outcome: the
answer `none` reaches the caller. Trap chatter is the opposite: no answer
ever reaches the caller, and each hidden `none` is swallowed by `σ`, which
calls again. It is divergence created by the wiring: `σ` itself never
diverges.

## Classification

Wiring-induced divergence below `widenH n` occurs **exactly for strategies
that do not propagate traps**:

* **It occurs** (`wiring_divergence`): the spinner `spinS n` (call function
  `n` forever, whatever the answer) never diverges (`spinS_div`), does not
  propagate traps (`spinS_not_trapPropagating`), and `atSizes n k (spinS n)`
  diverges right after any question (`div_atSizes_spin`). Its infinite play is
  trap chatter (`trapChatter_spin`). So the divergence of `atSizes n k σ` is not
  in general the image of the divergence of `σ`.
* **It is excluded by trap propagation** (`div_atSizes_of_trapPropagating`):
  if, after every trap answer `none` from below, `σ` makes no further call
  below in that round (`TrapPropagating`, implied by the Wasm reading
  `TrapAborting`: the round answers with a trap), then no infinite play of
  `σ` is eventually trap events (`not_eventuallyTrap`), there is no trap chatter
  (`not_trapChatter`), and `atSizes n k σ` diverges exactly where `σ` does,
  along the two handlers. The infinite plays of `atSizes n k σ` are given
  exactly, for every `σ`, by `inf_atSizes_iff`.

The same holds below every **trap-silent** handler (`TrapSilent`: whatever it
answers without a call is `none`), such as `widenH n` and `maskH e`
(`trapSilent_widenH`, `trapSilent_maskH`): a trap-propagating strategy has no
silent chatter there (`not_silentChatter`,
`div_ofHandler_comp_of_trapSilent`). It fails for handlers that answer silently
with a value: `implsH` with a `.const (some v)` target is not trap-silent
(`not_trapSilent_implsH_const`). Calling such a constant forever is ordinary
divergence of the caller's own loop, not trap chatter, and trap propagation
does not (and should not) exclude it.

## The component denotation, layer by layer

`Comp.denD C (.mk I ns xs)` is `atSizes` of `denUD`, which is `exportsH` above
the environment built from `maskH I.length` by the nodes (`ext`).

* **The outer `widenH` layer adds no divergence, unconditionally**
  (`div_denD_eq`). `maskH I.length` already answers every out-of-range import
  call with `none` itself, so a component calls its imports in range only
  (`denUD_lowerIn`), and then it has no trap events below except answers, which
  cannot follow one another. The out-of-range chatter of a component therefore
  sits one layer down, at `maskH`.
* **The `exportsH` layer adds no divergence** (`div_denUD`, one-call handler on
  top).
* **The `maskH` layer adds no divergence when the first node propagates traps**
  (`div_ext_ofHandler_of_trapSilent`, `div_ext_maskH`): its chatter with the
  node above would be the node calling an out-of-range function forever,
  answered `none` (`not_extChatter_ofHandler`).
* **Later nodes** (`div_ext_eq_routed`): divergence of the environment,
  divergence of the node, and inter-node chatter `ExtChatter`, in which the
  environment answers the node's calls forever. When the node propagates
  traps, none of those answers but possibly the last is a trap, so this is
  genuine mutual recursion between instances, not out-of-range chatter.

Hence, for a component whose node strategies propagate traps, every
divergence is a node's own divergence or inter-node chatter of non-trap
answers; the wiring (`widenH`, `maskH`, `narrowH`, `exportsH`, `splitH`) adds
none. For a single node this is `div_denD_single`.

Proofs are in `Silmaril.Proofs.Wasm.Component.OutOfRange`.
-/

public section

namespace Silmaril.Wasm.Component

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.OutOfRange (LowerIn)

variable {O : Type} {G : Sig.{0}} {n k : Nat}

/-! ## Trap propagation -/

/-- The Wasm reading of trap propagation implies the round-ending one. -/
theorem TrapAborting.trapPropagating {P : Type} {σ : DStrategy (sigO O) (sigO P)}
    (h : TrapAborting σ) : TrapPropagating σ := fun s m y hy =>
  let ⟨_, hq⟩ := h s m y hy; ⟨_, hq⟩

/-- **No trap tail.** A trap-propagating strategy has no infinite play that,
after one of its members, only moves below and only receives the answer
`none`. -/
theorem TrapPropagating.no_trap_tail {σ : DStrategy (sigO O) G} (hσ : TrapPropagating σ)
    {I : Set (List (Move (sigO O) G))} (hI : I ∈ σ.inf) {t₀ : List (Move (sigO O) G)}
    (ht₀ : t₀ ∈ I)
    (htr : ∀ w x, t₀ ++ w ++ [x] ∈ I →
      ∃ e : Ev (sigO O), x = .inl e ∧ ∀ m r, e = .ans m r → r = none) : False :=
  Silmaril.Proofs.Wasm.Component.OutOfRange.no_trap_tail hσ hI ht₀ htr

/-- **A trap-propagating strategy has no eventually-trap infinite play.** -/
theorem TrapPropagating.not_eventuallyTrap {σ : DStrategy sigU G} (hσ : TrapPropagating σ)
    {I : Set (List (Move sigU G))} (hI : I ∈ σ.inf) : ¬ EventuallyTrap n I :=
  Silmaril.Proofs.Wasm.Component.OutOfRange.not_eventuallyTrap hσ hI

/-- **A trap-propagating strategy has no trap chatter.** -/
theorem TrapPropagating.not_trapChatter {σ : DStrategy sigU G} (hσ : TrapPropagating σ)
    {s : List (Move (sigN n) G)} : ¬ TrapChatter n σ s :=
  Silmaril.Proofs.Wasm.Component.OutOfRange.not_trapChatter hσ

namespace DStrategy

/-- **Exclusion: with trap propagation, `atSizes` diverges exactly where `σ`
does**, along the two handlers. -/
theorem div_atSizes_of_trapPropagating {σ : DStrategy sigU sigU} (hσ : TrapPropagating σ) :
    (atSizes n k σ).div = {p | ∃ s t u v, Zip u v s ∧ Zip s t p ∧
      u ∈ Strategy.ofHandler (widenH n) ∧ t ∈ Strategy.ofHandler (narrowH k) ∧
        v ∈ σ.div} :=
  div_atSizes_of_noTrap fun _ hI => hσ.not_eventuallyTrap hI

end DStrategy

/-! ## The counterexample -/

/-- The spinner never diverges on its own. -/
theorem spinS_div (j : Nat) : (spinS j).div = ∅ :=
  Silmaril.Proofs.Wasm.Component.OutOfRange.spinS_div j

/-- The spinner does not propagate traps. -/
theorem spinS_not_trapPropagating (j : Nat) : ¬ TrapPropagating (spinS j) :=
  Silmaril.Proofs.Wasm.Component.OutOfRange.spin_not_trapPropagating j

/-- **The spinner's infinite play on a question is trap chatter** below
`widenH n` for `n ≤ j`. -/
theorem trapChatter_spin {j : Nat} (hj : n ≤ j) (Q : Nat × Payload) :
    TrapChatter n (spinS j) [.inr (.ask Q)] :=
  Silmaril.Proofs.Wasm.Component.OutOfRange.trapChatter_spin j Q hj

/-- **Wiring-induced divergence**: `atSizes n k (spinS j)` diverges right after
any question when `n ≤ j`, although `spinS j` never diverges. -/
theorem div_atSizes_spin {j : Nat} (hj : n ≤ j) (q : (sigN k).Op) :
    [.inr (.ask q)] ∈ (DStrategy.atSizes n k (spinS j)).div :=
  Silmaril.Proofs.Wasm.Component.OutOfRange.div_atSizes_spin j hj q

/-- **Classification, first half: wiring creates divergence.** There is a
strategy that never diverges and does not propagate traps, whose
`atSizes n k` diverges after any question; this divergence is not the image of
any divergence of the strategy. -/
theorem wiring_divergence (q : (sigN k).Op) :
    ∃ σ : DStrategy sigU sigU, σ.div = ∅ ∧ ¬ TrapPropagating σ ∧
      [.inr (.ask q)] ∈ (DStrategy.atSizes n k σ).div ∧
      [.inr (.ask q)] ∉ {p | ∃ s t u v, Zip u v s ∧ Zip s t p ∧
        u ∈ Strategy.ofHandler (widenH n) ∧ t ∈ Strategy.ofHandler (narrowH k) ∧
          v ∈ σ.div} :=
  ⟨spinS n, spinS_div n, spinS_not_trapPropagating n, div_atSizes_spin le_rfl q,
    fun ⟨_, _, _, _, _, _, _, _, hv⟩ => by rw [spinS_div] at hv; exact hv⟩

/-- **Classification, second half: trap propagation excludes it.** -/
theorem no_wiring_divergence {σ : DStrategy sigU sigU} (hσ : TrapPropagating σ) :
    (DStrategy.atSizes n k σ).div = {p | ∃ s t u v, Zip u v s ∧ Zip s t p ∧
      u ∈ Strategy.ofHandler (widenH n) ∧ t ∈ Strategy.ofHandler (narrowH k) ∧
        v ∈ σ.div} :=
  DStrategy.div_atSizes_of_trapPropagating hσ

/-! ## Trap-silent handlers -/

theorem trapSilent_widenH (n : Nat) : TrapSilent (widenH n) := by
  intro q r h
  simp only [widenH] at h; split at h <;> cases h; rfl

theorem trapSilent_maskH (e : Nat) : TrapSilent (maskH e) := by
  intro q r h
  simp only [maskH, Target.prog] at h; split at h <;> cases h; rfl

/-- `implsH` is not trap-silent: a constant target answers with a value at once. -/
theorem not_trapSilent_implsH_const (e : Nat) (v : Payload) :
    ¬ TrapSilent (implsH e [⟨[], .const (some v)⟩]) := fun h =>
  Option.some_ne_none v (h (0, v) (some v) rfl)

/-- **No silent chatter below a trap-silent handler.** -/
theorem TrapPropagating.not_silentChatter {E : Sig.{0}} {h : Handler E (sigO O)}
    (hh : TrapSilent h) {σ : DStrategy (sigO O) G} (hσ : TrapPropagating σ)
    {s : List (Move E G)} : ¬ SilentChatter h σ s :=
  Silmaril.Proofs.Wasm.Component.OutOfRange.not_silentChatter hh hσ

namespace DStrategy

/-- **Below a trap-silent handler, a trap-propagating strategy diverges only
where it diverges itself.** -/
theorem div_ofHandler_comp_of_trapSilent {E : Sig.{0}} {h : Handler E (sigO O)}
    (hh : TrapSilent h) {σ : DStrategy (sigO O) G} (hσ : TrapPropagating σ) :
    ((DStrategy.ofHandler h).comp σ).div =
      {p | ∃ u v, Zip u v p ∧ u ∈ Strategy.ofHandler h ∧ v ∈ σ.div} := by
  rw [div_ofHandler_comp_iff]
  ext p
  exact or_iff_left (hσ.not_silentChatter hh)

/-! ## `ext` above a trap-silent handler -/

/-- **A trap-silent handler and a trap-propagating node do not chatter.** -/
theorem not_extChatter_ofHandler {X : Sig.{0}} {h : Handler X sigU} (hh : TrapSilent h)
    {N : DStrategy sigU sigU} (hN : TrapPropagating N) {e : Nat}
    {I : Set (List (Move X sigU))} (hI : I ∈ (DStrategy.ofHandler h).inf)
    {L : Set (List (Move sigU sigU))} (hL : L ∈ N.inf) {p : List (Move X sigU)} :
    ¬ ExtChatter e I L p :=
  Silmaril.Proofs.Wasm.Component.OutOfRange.not_extChatter_ofHandler hh hN hI hL

/-- **A node above a trap-silent handler**: if the node propagates traps, the
extension diverges exactly where the node does, through the pairing and
`splitH e`. -/
theorem div_ext_ofHandler_of_trapSilent {X : Sig.{0}} {h : Handler X sigU} (hh : TrapSilent h)
    (e : Nat) {N : DStrategy sigU sigU} (hN : TrapPropagating N) :
    (ext e (DStrategy.ofHandler h) N).div = {p | ∃ s t, Zip s t p ∧
      s ∈ Strategy.ofHandler h ∧ ∃ a b, Zip a b t ∧
        (a ∈ (Strategy.id sigU).pair N.toStrategy ∧ (Split.halves false a).2 ∈ N.div) ∧
          b ∈ Strategy.ofHandler (splitH e)} := by
  rw [div_ext_eq_routed]
  ext p
  constructor
  · rintro (⟨s, t, hz, ⟨hs, -⟩ | ⟨hs, hr⟩⟩ | ⟨I, hI, L, hL, hc⟩)
    · rw [Silmaril.Games.DStrategy.ofHandler_div] at hs; exact hs.elim
    · exact ⟨s, t, hz, hs, hr⟩
    · exact (not_extChatter_ofHandler hh hN hI hL hc).elim
  · rintro ⟨s, t, hz, hs, hr⟩
    exact .inl ⟨s, t, hz, .inr ⟨hs, hr⟩⟩

/-- **The `maskH` layer** adds no divergence above a trap-propagating node. -/
theorem div_ext_maskH (e : Nat) {N : DStrategy sigU sigU} (hN : TrapPropagating N) :
    (ext e (DStrategy.ofHandler (maskH e)) N).div = {p | ∃ s t, Zip s t p ∧
      s ∈ Strategy.ofHandler (maskH e) ∧ ∃ a b, Zip a b t ∧
        (a ∈ (Strategy.id sigU).pair N.toStrategy ∧ (Split.halves false a).2 ∈ N.div) ∧
          b ∈ Strategy.ofHandler (splitH e)} :=
  div_ext_ofHandler_of_trapSilent (trapSilent_maskH e) e hN

end DStrategy

/-! ## The component denotation -/

variable {M : Type} [CoreModule M]

/-- **A component calls its imports in range only**: `maskH` answers the other
calls itself. -/
theorem denUD_lowerIn (C : DCoreSem M) (c : Comp M) :
    ∀ s ∈ (c.denUD C).toStrategy, ∀ m : Nat × Payload, .inl (.ask m) ∈ s →
      m.1 < c.imports.length :=
  Silmaril.Proofs.Wasm.Component.OutOfRange.denUD_lowerIn C c

/-- A component has no eventually-trap infinite play below its imports. -/
theorem denUD_not_eventuallyTrap (C : DCoreSem M) (c : Comp M)
    {I : Set (List (Move sigU sigU))} (hI : I ∈ (c.denUD C).inf) :
    ¬ EventuallyTrap c.imports.length I :=
  Silmaril.Proofs.Wasm.Component.OutOfRange.not_eventuallyTrap_of_lowerIn
    (denUD_lowerIn C c) hI

/-- **The outer layer of a component adds no divergence, unconditionally.** -/
theorem div_denD_eq (C : DCoreSem M) (c : Comp M) :
    (c.denD C).div = {p | ∃ s t u v, Zip u v s ∧ Zip s t p ∧
      u ∈ Strategy.ofHandler (widenH c.imports.length) ∧
        t ∈ Strategy.ofHandler (narrowH c.exports.length) ∧ v ∈ (c.denUD C).div} :=
  DStrategy.div_atSizes_of_noTrap fun _ hI => denUD_not_eventuallyTrap C c hI

/-- **A component with one node**: when the node propagates traps, the
component diverges exactly where the node does, seen through the wiring
(`splitH` and the pairing, `maskH`, `exportsH`, `widenH`, `narrowH`). -/
theorem div_denD_single (C : DCoreSem M) (I : Iface) (nd : Node M) (xs : List Export)
    (hN : TrapPropagating (Node.denD C I.length nd)) :
    ((Comp.mk I [nd] xs).denD C).div = {p | ∃ s t u v, Zip u v s ∧ Zip s t p ∧
      u ∈ Strategy.ofHandler (widenH I.length) ∧
        t ∈ Strategy.ofHandler (narrowH xs.length) ∧ ∃ d x, Zip d x v ∧
          (∃ a b, Zip a b d ∧ a ∈ Strategy.ofHandler (maskH I.length) ∧
            ∃ c g, Zip c g b ∧
              (c ∈ (Strategy.id sigU).pair (Node.denD C I.length nd).toStrategy ∧
                (Split.halves false c).2 ∈ (Node.denD C I.length nd).div) ∧
              g ∈ Strategy.ofHandler (splitH I.length)) ∧
          x ∈ Strategy.ofHandler (exportsH (envAfter I.length [nd]) xs)} := by
  rw [div_denD_eq, div_denUD, denNodesD_cons, denNodesD_nil, DStrategy.div_ext_maskH _ hN]
  rfl

end Silmaril.Wasm.Component
