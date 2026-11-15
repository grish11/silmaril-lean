module

public import Silmaril.Wasm.Cfg.Maximal.Defs
public import Silmaril.Wasm.Cfg.BlockTree.Thms

@[expose] public section

namespace Silmaril.Wasm.Cfg.Proofs.Maximal

open Silmaril.Wasm Silmaril.Wasm.Cfg

theorem mem_maxFlow (body : Expr) (b : BlockId) (t : Target) :
    (b, t) ∈ maxFlow body ↔ EdgeAE body b t ∧ internal body b t = false := by
  unfold maxFlow EdgeAE
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨⟨b', s'⟩, hm, hx⟩
    rw [List.mem_map] at hx
    obtain ⟨t', ht', he⟩ := hx
    rw [List.mem_filter] at ht'
    cases he
    exact ⟨⟨s', (mem_blocks body b' s').1 hm, ht'.1⟩, by simpa using ht'.2⟩
  · rintro ⟨⟨s, hs, ht⟩, hi⟩
    refine ⟨(b, s), (mem_blocks body b s).2 hs, ?_⟩
    rw [List.mem_map]
    exact ⟨t, List.mem_filter.2 ⟨ht, by simpa using hi⟩, rfl⟩

theorem mem_maxHandler (body : Expr) (b : BlockId) (t : Target) :
    (b, t) ∈ maxHandler body ↔ HandlerEdge body b t := by
  unfold maxHandler HandlerEdge
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨⟨b', s'⟩, hm, hx⟩
    rw [List.mem_map] at hx
    obtain ⟨t', ht', he⟩ := hx
    cases he
    exact ⟨s', (mem_blocks body b' s').1 hm, ht'⟩
  · rintro ⟨s, hs, ht⟩
    exact ⟨(b, s), (mem_blocks body b s).2 hs, List.mem_map.2 ⟨t, ht, rfl⟩⟩

theorem internal_iff (body : Expr) (b : BlockId) (t : Target) :
    internal body b t = true ↔ ∃ c, t = .block c ∧ canMerge body b c = true := by
  cases t <;> simp [internal]

end Silmaril.Wasm.Cfg.Proofs.Maximal
