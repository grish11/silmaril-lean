module

public import Silmaril.Crypto.Blake3.Tree.Defs
import Init.Data.Option.Lemmas
import Init.Data.List.TakeDrop

public section

namespace Silmaril.Proofs.Crypto.Blake3

open Silmaril.Crypto.Blake3

theorem geometry_size (first size : Nat) : (geometry first size).size = size := by
  induction size using Nat.strongRecOn generalizing first with
  | ind size ih =>
    rw [geometry]
    split
    · rfl
    · rename_i large
      have pos : 0 < splitBytes size := Nat.mul_pos (by decide) (Nat.pow_pos (by decide))
      have power := Nat.log2_self_le (n := (size - 1) / 1024) (by omega)
      have mul := Nat.mul_le_mul_left 1024 power
      have lt : splitBytes size < size := by unfold splitBytes; omega
      simp only [Shape.size, ih _ lt, ih _ (by omega : size - splitBytes size < size)]
      omega

theorem geometry_valid (first size : Nat) (bound : validSize (first + size)) : (geometry first size).Valid := by
  induction size using Nat.strongRecOn generalizing first with
  | ind size ih =>
    rw [geometry]
    unfold validSize at bound
    split
    · exact ⟨by assumption, by unfold validSize; omega⟩
    · rename_i large
      have pos : 0 < splitBytes size := Nat.mul_pos (by decide) (Nat.pow_pos (by decide))
      have power := Nat.log2_self_le (n := (size - 1) / 1024) (by omega)
      have mul := Nat.mul_le_mul_left 1024 power
      have lt : splitBytes size < size := by unfold splitBytes; omega
      exact ⟨ih _ lt _ (by unfold validSize; omega), ih _ (by omega) _ (by unfold validSize; omega)⟩

theorem chain_graph {run : Input → Option CV} {root first : Bool} {chunk more : Nat}
    {cv output : CV} {bytes : Bytes} :
    chain? run root chunk more first cv bytes = some output ↔
      Chain (Compression.graph run) root chunk more first cv bytes output := by
  induction more generalizing first cv bytes with
  | zero =>
    constructor
    · intro evaluated
      unfold chain? at evaluated
      split at evaluated
      · exact .last (by assumption) evaluated
      · contradiction
    · rintro ⟨small, hit⟩
      simpa [chain?, small, Compression.graph] using hit
  | succ more ih =>
    constructor
    · intro evaluated
      unfold chain? at evaluated
      split at evaluated
      · obtain ⟨mid, hit, tail⟩ := Option.bind_eq_some_iff.mp evaluated
        exact .step (by assumption) hit (ih.mp tail)
      · contradiction
    · intro trace
      cases trace with
      | step large hit tail =>
        rw [chain?, ite_eq_left large]
        exact Option.bind_eq_some_iff.mpr ⟨_, hit, ih.mpr tail⟩

theorem eval_graph {run : Input → Option CV} {root : Bool} {shape : Shape} {opening : Opening} {output : CV} :
    eval? run root shape opening = some output ↔ Trace (Compression.graph run) root shape opening output := by
  induction opening generalizing root shape output with
  | «opaque» cv =>
    cases root <;> simp only [eval?, Bool.false_eq_true, ↓reduceIte, Option.some.injEq]
    · exact ⟨fun eq => eq ▸ Trace.opaque shape cv, fun trace => by cases trace; rfl⟩
    · exact ⟨fun hit => by contradiction, fun trace => by cases trace⟩
  | leaf bytes =>
    cases shape with
    | leaf chunk size =>
      constructor
      · intro hit
        simp only [eval?] at hit
        split at hit
        · exact .leaf (by assumption) (chain_graph.mp hit)
        · contradiction
      · intro trace
        cases trace with
        | leaf ok chain => simpa only [eval?, ite_eq_left ok] using chain_graph.mpr chain
    | fork => exact ⟨fun hit => by contradiction, fun trace => by cases trace⟩
  | fork lhs rhs leftIH rightIH =>
    cases shape with
    | leaf => exact ⟨fun hit => by contradiction, fun trace => by cases trace⟩
    | fork left right =>
      simp only [eval?, Option.bind_eq_bind, Option.bind_eq_some_iff]
      constructor
      · rintro ⟨_, leftHit, _, rightHit, hit⟩
        exact .fork (leftIH.mp leftHit) (rightIH.mp rightHit) hit
      · intro trace
        cases trace with
        | fork ltrace rtrace hit => exact ⟨_, leftIH.mpr ltrace, _, rightIH.mpr rtrace, hit⟩

private theorem chain_mono {left right : Compression} (sub : ∀ ⦃input output⦄, left input output → right input output)
    {root first : Bool} {chunk more : Nat} {cv output : CV} {bytes : Bytes}
    (trace : Chain left root chunk more first cv bytes output) : Chain right root chunk more first cv bytes output := by
  induction trace with
  | last bound hit => exact .last bound (sub hit)
  | step bound hit _ ih => exact .step bound (sub hit) ih

private theorem trace_mono {left right : Compression} (sub : ∀ ⦃input output⦄, left input output → right input output)
    {root : Bool} {shape : Shape} {opening : Opening} {output : CV}
    (trace : Trace left root shape opening output) : Trace right root shape opening output := by
  induction trace with
  | «opaque» => exact .opaque ..
  | leaf ok chain => exact .leaf ok (chain_mono sub chain)
  | fork _ _ hit leftIH rightIH => exact .fork leftIH rightIH (sub hit)

theorem eval_sound {rel : Compression} {run : Input → Option CV} {root : Bool}
    {shape : Shape} {opening : Opening} {output : CV} (consistent : Compression.Consistent rel run)
    (hit : eval? run root shape opening = some output) : Trace rel root shape opening output :=
  trace_mono consistent (eval_graph.mp hit)

theorem root_graph {run : Input → Option CV} {size : Nat} {opening : Opening} {digest : Bytes} :
    root? run size opening = some digest ↔ Root (Compression.graph run) size digest opening := by
  by_cases ok : validSize size <;> simp [root?, Root, ok, eval_graph]

theorem root_sound {rel : Compression} {run : Input → Option CV} {size : Nat} {opening : Opening}
    {digest : Bytes} (consistent : Compression.Consistent rel run)
    (hit : root? run size opening = some digest) : Root rel size digest opening :=
  let ⟨ok, output, trace, eq⟩ := root_graph.mp hit
  ⟨ok, output, eval_sound consistent (eval_graph.mpr trace), eq⟩

private theorem chain_total {run : Input → Option CV} (total : ∀ input, ∃ cv, run input = some cv)
    (root first : Bool) (chunk more : Nat) (cv : CV) (bytes : Bytes)
    (count : more = (bytes.length - 1) / 64) : ∃ output, chain? run root chunk more first cv bytes = some output := by
  induction more generalizing first cv bytes with
  | zero =>
    have small : bytes.length ≤ 64 := by omega
    simpa only [chain?, ite_eq_left small] using total (chunkInput root first true chunk cv bytes)
  | succ more ih =>
    have large : 64 < bytes.length := by omega
    obtain ⟨mid, hit⟩ := total (chunkInput false first false chunk cv (bytes.take 64))
    obtain ⟨output, tail⟩ := ih false mid (bytes.drop 64) (by simp only [List.length_drop]; omega)
    exact ⟨output, by simp [chain?, large, hit, tail]⟩

private theorem disclose_total {run : Input → Option CV} (total : ∀ input, ∃ cv, run input = some cv)
    (root : Bool) (shape : Shape) (bytes : Bytes) (ok : shape.Valid) (len : bytes.length = shape.size) :
    ∃ output, eval? run root shape (disclose shape bytes) = some output := by
  induction shape generalizing root bytes with
  | leaf chunk size =>
    have guard : leafOK chunk size bytes := ⟨len, ok⟩
    simpa only [disclose, eval?, ite_eq_left guard] using
      chain_total total root true chunk ((size - 1) / 64) iv bytes (by rw [len]; rfl)
  | fork left right leftIH rightIH =>
    change left.Valid ∧ right.Valid at ok
    change bytes.length = left.size + right.size at len
    obtain ⟨lcv, lhit⟩ := leftIH false (bytes.take left.size) ok.1 (by simp; omega)
    obtain ⟨rcv, rhit⟩ := rightIH false (bytes.drop left.size) ok.2 (by simp; omega)
    obtain ⟨output, hit⟩ := total (parentInput root lcv rcv)
    exact ⟨output, by simp [disclose, eval?, lhit, rhit, hit]⟩

theorem hash_total {run : Input → Option CV} (total : ∀ input, ∃ cv, run input = some cv)
    {bytes : Bytes} (valid : validSize bytes.length) : ∃ digest, hash? run bytes = some digest := by
  obtain ⟨output, hit⟩ := disclose_total total true (geometry 0 bytes.length) bytes
    (geometry_valid 0 _ (by simpa using valid)) (geometry_size 0 _).symm
  exact ⟨digestBytes output, by simp [hash?, root?, valid, hit]⟩

end Silmaril.Proofs.Crypto.Blake3
