module

public import Silmaril.Games.DPull.Defs
import Silmaril.Proofs.Games.DPull.Path

/-!
# Pulling strategies back along a move map: laws (proofs)

The pull along a move map is the generated strategy of the preimage (`pull_eq_generate`), is
functorial (`pull_id`, `pull_comp`, for strategies and divergence-observing strategies) and
monotone. Used by `Silmaril.Games.DPull.Thms`.
-/

public section

namespace Silmaril.Proofs.Games.DPull

open Silmaril.Games

universe u

variable {E F E' F' E'' F'' : Sig.{u}}

theorem pull_eq_generate {f : Move E F → Move E' F'} {pf : Pos E F → Pos E' F'}
    (hf : PullData f pf) (σ : Strategy E' F') :
    σ.pull f pf hf = Strategy.generate {p | p.map f ∈ σ} :=
  le_antisymm (fun _ h => Strategy.subset_generate h ((σ.pull f pf hf).legal h))
    (Strategy.generate_le fun _ h _ => h)

theorem pullData_comp {g : Move E' F' → Move E'' F''} {pg : Pos E' F' → Pos E'' F''}
    {f : Move E F → Move E' F'} {pf : Pos E F → Pos E' F'}
    (hg : PullData g pg) (hf : PullData f pf) : PullData (g ∘ f) (pg ∘ pf) where
  idle := by simp [hf.idle, hg.idle]
  step h := hg.step (hf.step h)
  lift h := by
    obtain ⟨y', hy'⟩ := hg.lift h
    exact hf.lift hy'
  run h := by
    obtain ⟨q', hq'⟩ := hg.run h
    exact hf.run hq'

theorem strategy_pull_id (σ : Strategy E F) :
    σ.pull id id ⟨rfl, id, fun h => ⟨_, h⟩, fun h => ⟨_, h⟩⟩ = σ :=
  Strategy.ext fun p => by
    change p.map id ∈ σ ↔ p ∈ σ
    rw [List.map_id]

theorem pull_id (σ : DStrategy E F) :
    σ.pull id id ⟨rfl, id, fun h => ⟨_, h⟩, fun h => ⟨_, h⟩⟩ = σ := by
  refine DStrategy.ext (strategy_pull_id _) ?_ ?_
  · ext p
    change p.map id ∈ σ.div ↔ p ∈ σ.div
    rw [List.map_id]
  · ext J
    change IsInfPlay J ∧ List.map id '' J ∈ σ.inf ↔ J ∈ σ.inf
    rw [List.map_id_fun, Set.image_id]
    exact ⟨fun h => h.2, fun h => ⟨σ.inf_isInf h, h⟩⟩

theorem strategy_pull_comp {g : Move E' F' → Move E'' F''} {pg : Pos E' F' → Pos E'' F''}
    {f : Move E F → Move E' F'} {pf : Pos E F → Pos E' F'}
    (hg : PullData g pg) (hf : PullData f pf) (h : PullData (g ∘ f) (pg ∘ pf))
    (σ : Strategy E'' F'') : σ.pull (g ∘ f) (pg ∘ pf) h = (σ.pull g pg hg).pull f pf hf :=
  Strategy.ext fun p => by
    change p.map (g ∘ f) ∈ σ ↔ (p.map f).map g ∈ σ
    rw [List.map_map]

theorem pull_comp {g : Move E' F' → Move E'' F''} {pg : Pos E' F' → Pos E'' F''}
    {f : Move E F → Move E' F'} {pf : Pos E F → Pos E' F'}
    (hg : PullData g pg) (hf : PullData f pf) (h : PullData (g ∘ f) (pg ∘ pf))
    (σ : DStrategy E'' F'') : σ.pull (g ∘ f) (pg ∘ pf) h = (σ.pull g pg hg).pull f pf hf := by
  refine DStrategy.ext (strategy_pull_comp hg hf h _) ?_ ?_
  · ext p
    change p.map (g ∘ f) ∈ σ.div ↔ (p.map f).map g ∈ σ.div
    rw [List.map_map]
  · ext J
    change IsInfPlay J ∧ List.map (g ∘ f) '' J ∈ σ.inf ↔
      IsInfPlay J ∧ IsInfPlay (List.map f '' J) ∧ List.map g '' (List.map f '' J) ∈ σ.inf
    have hc : (fun l => List.map g (List.map f l)) = List.map (g ∘ f) :=
      funext fun _ => List.map_map
    rw [Set.image_image, hc]
    exact ⟨fun ⟨hJ, h⟩ => ⟨hJ, isInfPlay_image f hJ, h⟩, fun ⟨hJ, _, h⟩ => ⟨hJ, h⟩⟩

end Silmaril.Proofs.Games.DPull
