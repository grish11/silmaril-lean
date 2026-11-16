module

public import Silmaril.Games.Div.Defs
import Silmaril.Proofs.Games.DPull.Path

/-!
# Pulling strategies back along a move map

A move map `f : Move E F → Move E' F'` reads plays of `E ↠ F` as plays of `E' ↠ F'`. When it
is compatible with the legality automata through a position map `pf` (`PullData f pf`), every
strategy for `E' ↠ F'` pulls back to one for `E ↠ F`:

* `Strategy.pull f pf hf σ`: the plays `p` with `p.map f ∈ σ`. This preimage is already a
  strategy (prefix closed, legal and receptive), so no `Strategy.generate` is needed; it is equal
  to `Strategy.generate {p | p.map f ∈ σ}` (`Strategy.pull_eq_generate`);
* `DStrategy.pull f pf hf σ`: the same finite plays; divergences `{p | p.map f ∈ σ.div}`;
  infinite plays `{J | IsInfPlay J ∧ List.map f '' J ∈ σ.inf}`.

`PullData f pf` asks for exactly what the strategy fields need, and nothing about injectivity:

* `idle`: `pf` keeps the initial position;
* `step`: a step goes to a step (so images of legal plays are legal, and Opponent moves after a
  play can be forwarded to `σ`);
* `lift`: a move whose image can be played from an image position can be played there (so a play
  whose image is legal is legal);
* `run`: only running positions go to running positions (so divergences end running, and
  Opponent moves go to Opponent moves).

The laws (`Silmaril.Games.DPull.Thms`) are the membership characterisations, functoriality
(`pull_id`, `pull_comp`) and monotonicity.

`StratSession.relabel` is not an instance: it maps along the non-injective `relMove`, and its
plays, divergences and infinite plays are *images* (a pushforward), not preimages.
-/

@[expose] public section

namespace Silmaril.Games

open Silmaril.Proofs.Games.DPull (path_map legal_lift run_lift isO_map)

universe u

variable {E F E' F' : Sig.{u}}

/-- **Compatibility of a move map with the legality automata**, through the position map `pf`;
see the module documentation. -/
structure PullData (f : Move E F → Move E' F') (pf : Pos E F → Pos E' F') : Prop where
  /-- The initial position is kept. -/
  idle : pf .idle = .idle
  /-- Steps go to steps. -/
  step : ∀ {x o y}, Step x o y → Step (pf x) (f o) (pf y)
  /-- A step from an image position along an image move lifts. -/
  lift : ∀ {x o y'}, Step (pf x) (f o) y' → ∃ y, Step x o y
  /-- Only running positions go to running positions. -/
  run : ∀ {x q'}, pf x = .run q' → ∃ q, x = .run q

/-- **The strategy pulled back along `f`**: the plays whose image is a play of `σ`. -/
def Strategy.pull (f : Move E F → Move E' F') (pf : Pos E F → Pos E' F') (hf : PullData f pf)
    (σ : Strategy E' F') : Strategy E F where
  plays := {p | p.map f ∈ σ}
  nil_mem := σ.nil_mem
  legal h := by exact legal_lift hf.step hf.lift hf.idle (σ.legal h)
  of_prefix h hst := σ.of_prefix h (hst.map f)
  receptive h hx hxy ho := by
    have hx' := path_map hf.step hx
    rw [hf.idle] at hx'
    simpa using σ.receptive h hx' (hf.step hxy) (isO_map hf.step hf.run hxy ho)

/-- **The divergence-observing strategy pulled back along `f`**: the finite plays, divergences
and infinite plays whose images are those of `σ`. -/
def DStrategy.pull (f : Move E F → Move E' F') (pf : Pos E F → Pos E' F') (hf : PullData f pf)
    (σ : DStrategy E' F') : DStrategy E F where
  toStrategy := σ.toStrategy.pull f pf hf
  div := {p | p.map f ∈ σ.div}
  inf := {J | IsInfPlay J ∧ List.map f '' J ∈ σ.inf}
  div_mem h := σ.div_mem h
  div_run h := by exact run_lift hf.step hf.lift hf.idle hf.run (σ.div_run h)
  inf_isInf h := h.1
  inf_sub h _ hp := σ.inf_sub h.2 ⟨_, hp, rfl⟩

end Silmaril.Games
