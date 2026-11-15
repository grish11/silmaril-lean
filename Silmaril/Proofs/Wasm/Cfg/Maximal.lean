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

theorem nodupB_sound : ∀ {l : List BlockId}, nodupB l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    simp only [nodupB, Bool.and_eq_true] at h
    exact List.nodup_cons.2 ⟨by simpa [List.contains_iff_mem] using h.1, nodupB_sound h.2⟩

theorem groupsOk_sound {body : Expr} {gs : List (List BlockId)} (h : groupsOk body gs = true) :
    (∀ b, b ∈ gs.flatten ↔ b ∈ (blocks body).map (·.1)) ∧ gs.flatten.Nodup ∧
      ∀ g ∈ gs, groupOk body g = true := by
  unfold groupsOk at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨hn, hc⟩, hs⟩, hg⟩ := h
  refine ⟨fun b => ⟨fun hb => ?_, fun hb => ?_⟩, nodupB_sound hn, hg⟩
  · simpa [List.contains_iff_mem] using hs b hb
  · simpa [List.contains_iff_mem] using hc b hb

theorem groupOk_spec {body : Expr} {g : List BlockId} (h : groupOk body g = true) :
    (∀ p ∈ g.zip g.tail, canMerge body p.1 p.2 = true) ∧
    (∃ hd, g.head? = some hd ∧ ∀ p ∈ blocks body, canMerge body p.1 hd = false) ∧
    (∃ l, g.getLast? = some l ∧ ∀ p ∈ blocks body, canMerge body l p.1 = false) := by
  unfold groupOk chainOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hc, hh⟩, hl⟩ := h
  refine ⟨List.all_eq_true.1 hc, ?_, ?_⟩
  · revert hh
    cases g.head? with
    | none => intro hh; simp at hh
    | some x =>
      intro hh
      change isHead body x = true at hh
      unfold isHead at hh
      exact ⟨x, rfl, fun p hp => by simpa using List.all_eq_true.1 hh p hp⟩
  · revert hl
    cases g.getLast? with
    | none => intro hl; simp at hl
    | some x =>
      intro hl
      change isLast body x = true at hl
      unfold isLast at hl
      exact ⟨x, rfl, fun p hp => by simpa using List.all_eq_true.1 hl p hp⟩

end Silmaril.Wasm.Cfg.Proofs.Maximal
