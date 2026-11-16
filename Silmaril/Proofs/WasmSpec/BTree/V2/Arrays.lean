module

public import Silmaril.Proofs.WasmSpec.BTree.V2.Specs

/-!
# The B-tree library, version 2: `ba_insert` and `ba_copy` by tactics

Symbolic execution with the rules of `Silmaril.Wasm.Logic.Words`.

* `ba_copy(src, dst, n)`: the loop copies word `i` of the source to cell `i` of the
  destination; invariant: the first `i` cells hold the first `i` source words and only the
  destination array changed (`CInv`), variant `n + 1 - i`; then the length is stored.
* `ba_insert(x, j, v)`: the loop shifts cell `i - 1` to cell `i` from `i = |α|` down to `j + 1`;
  invariant: cells `[0, i)` hold `α.take i` and cells `(i, |α|]` hold `α.drop i` (`IInv`),
  variant `i`; then `v` is stored at cell `j` and the length incremented.

Every-run total correctness at every profile and host relation.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.WasmSpec.BTree.V2

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.Words
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Arrays -/

/-- A segment of one more word: its first word, then the rest. -/
theorem words_succ (B : ByteArray) (p k : Nat) : words B p (k + 1) = wd B p :: words B (p + 4) k := by
  have h := words_append (B := B) p 1 k
  rw [Nat.add_comm] at h
  rw [h]
  simp [words]

/-- A segment of one more word: the first words, then the last. -/
theorem words_snoc (B : ByteArray) (p k : Nat) :
    words B p (k + 1) = words B p k ++ [wd B (p + 4 * k)] := by
  rw [words_append]
  simp [words]

/-! ## `ba_copy` -/

/-- The loop of `ba_copy`. -/
abbrev copyLoop : List Instr := [lget 3, lget 2, igeu, brIf 1,
  lget 1, lget 3, c32 4, imul, iadd,
  lget 0, lget 3, c32 4, imul, iadd, iload,
  .intStore .i32 none ⟨0⟩ ⟨2, 4⟩,
  lget 3, c32 1, iadd, lset 3, br 0]

theorem baCopyFunc_body : baCopyFunc.body = [while_ copyLoop, lget 1, lget 2, istore] := rfl

theorem forCall_baCopy (mi : ModuleInst) (src dst n : BitVec 32) :
    Frame.forCall mi [.i32 src, .i32 dst, .i32 n] baCopyFunc.locals = fr mi [src, dst, n, 0] :=
  rfl

/-- The layout of `ba_copy`'s arguments. -/
def CopyCtx (B : ByteArray) (src dst n : BitVec 32) (cap : Nat) : Prop :=
  n.toNat ≤ cap ∧ src.toNat + 4 * n.toNat ≤ B.size ∧ src.toNat + 4 * n.toNat ≤ int32Max ∧
    dst.toNat + 4 + 4 * cap ≤ B.size ∧ dst.toNat + 4 + 4 * cap ≤ int32Max ∧
    (src.toNat + 4 * n.toNat ≤ dst.toNat ∨ dst.toNat + 4 + 4 * cap ≤ src.toNat)

/-- **The invariant of `ba_copy`'s loop**: memory `0` holds `B'`, equal to `B` outside the
destination array, whose first `i` cells hold the first `i` source words. -/
def CInv (s₀ : Store H) (mi : ModuleInst) (ma : Nat) (mt : MemoryType) (B : ByteArray)
    (src dst n : BitVec 32) (cap : Nat) (s : Store H) (f : Frame) : Prop :=
  ∃ (B' : ByteArray) (i : BitVec 32), s = s₀.setMem ma ⟨mt, B'⟩ ∧ f = fr mi [src, dst, n, i] ∧
    i.toNat ≤ n.toNat ∧ SameOutside B B' dst.toNat (4 + 4 * cap) ∧
    words B' (dst.toNat + 4) i.toNat = words B src.toNat i.toNat

/-- The variant `n + 1 - i`. -/
def CV (n : BitVec 32) (_ : Store H) (f : Frame) : Nat := n.toNat + 1 - loc f 3

theorem CV_fr {mi : ModuleInst} {src dst n i : BitVec 32} {s : Store H} :
    CV n s (fr mi [src, dst, n, i]) = n.toNat + 1 - i.toNat := by
  simp only [CV, loc_fr (L := [src, dst, n, i]) (k := 3) (by simp), List.getD_cons_succ,
    List.getD_cons_zero]

/-- **One copy**: cell `i` of the destination gets source word `i`. -/
theorem copy_step {B B' : ByteArray} {src dst n i : BitVec 32} {cap : Nat}
    (hc : CopyCtx B src dst n cap) (hso : SameOutside B B' dst.toNat (4 + 4 * cap))
    (hw : words B' (dst.toNat + 4) i.toNat = words B src.toNat i.toNat)
    (hi : i.toNat < n.toNat) :
    SameOutside B (wr B' (dst.toNat + 4 * i.toNat + 4) (wd B' (src.toNat + 4 * i.toNat)))
        dst.toNat (4 + 4 * cap) ∧
      words (wr B' (dst.toNat + 4 * i.toNat + 4) (wd B' (src.toNat + 4 * i.toNat)))
        (dst.toNat + 4) (i.toNat + 1) = words B src.toNat (i.toNat + 1) := by
  obtain ⟨hn, hs1, -, hd1, -, hdis⟩ := hc
  have hsz : B'.size = B.size := hso.1
  have hb : dst.toNat + 4 * i.toNat + 4 + 4 ≤ B'.size := by omega
  have hv : wd B' (src.toNat + 4 * i.toNat) = wd B (src.toNat + 4 * i.toNat) :=
    hso.wd_eq (by omega)
  have hlast : wd (wr B' (dst.toNat + 4 * i.toNat + 4) (wd B' (src.toNat + 4 * i.toNat)))
      (dst.toNat + 4 + 4 * i.toNat) = wd B (src.toNat + 4 * i.toNat) := by
    rw [show dst.toNat + 4 + 4 * i.toNat = dst.toNat + 4 * i.toNat + 4 by omega, wd_wr_same _ hb, hv]
  refine ⟨hso.trans (sameOutside_wr _ hb (by omega) (by omega)), ?_⟩
  rw [words_snoc, words_snoc, words_wr_out _ hb (by omega), hw, hlast]

/-- The copy and the increment of `i`, for `i < n`. -/
theorem copy_cont {s₀ : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType}
    {B B' : ByteArray} {src dst n i : BitVec 32} {cap : Nat} (hm₀ : MemAt s₀ mi ma mt B)
    (hc : CopyCtx B src dst n cap) {rest : List Admin} {Q : Post H}
    (hso : SameOutside B B' dst.toNat (4 + 4 * cap))
    (hw : words B' (dst.toNat + 4) i.toNat = words B src.toNat i.toNat)
    (hlt : i.toNat < n.toNat) :
    TWP P host (s₀.setMem ma ⟨mt, B'⟩) (fr mi [src, dst, n, i]) (vals [] ++ expression
      [lget 1, lget 3, c32 4, imul, iadd, lget 0, lget 3, c32 4, imul, iadd, iload,
        .intStore .i32 none ⟨0⟩ ⟨2, 4⟩, lget 3, c32 1, iadd, lset 3, br 0])
      (whilePostT P host (CInv s₀ mi ma mt B src dst n cap) (CV n) (n.toNat + 1 - i.toNat)
        rest Q) := by
  have hm : MemAt (s₀.setMem ma ⟨mt, B'⟩) mi ma mt B' := hm₀.setMem B'
  obtain ⟨hn, hs1, hs2, hd1, hd2, hdis⟩ := hc
  have hsz : B'.size = B.size := hso.1
  have hd2' : dst.toNat + 4 + 4 * cap ≤ 2 ^ 31 - 1 := hd2
  have hs2' : src.toNat + 4 * n.toNat ≤ 2 ^ 31 - 1 := hs2
  have hdi : (dst + i * 4#32).toNat = dst.toNat + 4 * i.toNat :=
    addr_toNat (n := cap) (by omega) (by omega)
  have hsi : (src + i * 4#32).toNat = src.toNat + 4 * i.toNat :=
    addr_toNat (n := n.toNat) (by omega) (by omega)
  have e4 : ((4 : Fin (2 ^ 64)) : Nat) = 4 := rfl
  have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
  obtain ⟨h1, h2⟩ := copy_step ⟨hn, hs1, hs2, hd1, hd2, hdis⟩ hso hw hlt
  have hv : CV n s₀ (fr mi [src, dst, n, i + 1#32]) < n.toNat + 1 - i.toNat := by
    rw [CV_fr]; omega
  wbegin
  wrun
  rw [setMem_setMem, hdi, hsi, e4]
  exact t_br (whilePostT_cont ⟨_, i + 1#32, rfl, rfl, by omega, h1, by rw [hi1]; exact h2⟩ hv)

/-- **One iteration of `ba_copy`'s loop.** -/
theorem copy_iter {s₀ : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType}
    {B : ByteArray} {src dst n : BitVec 32} {cap : Nat} (hm₀ : MemAt s₀ mi ma mt B)
    (hc : CopyCtx B src dst n cap) {rest : List Admin} {Q : Post H} {s : Store H} {f : Frame}
    (hI : CInv s₀ mi ma mt B src dst n cap s f)
    (hexit : ∀ B', SameOutside B B' dst.toNat (4 + 4 * cap) →
      words B' (dst.toNat + 4) n.toNat = words B src.toNat n.toNat →
      TWP P host (s₀.setMem ma ⟨mt, B'⟩) (fr mi [src, dst, n, n]) (vals [] ++ rest) Q) :
    TWP P host s f (vals [] ++ expression copyLoop)
      (whilePostT P host (CInv s₀ mi ma mt B src dst n cap) (CV n) (CV n s f) rest Q) := by
  obtain ⟨B', i, hs, hf, hin, hso, hw⟩ := hI
  have hm : MemAt (s₀.setMem ma ⟨mt, B'⟩) mi ma mt B' := hm₀.setMem B'
  rw [hs, hf, CV_fr]
  wbegin
  wrun
  refine t_brIf (fun h => ?_) (fun h => ?_)
  · have hge : n.toNat ≤ i.toNat := by simpa using h
    have hi : i = n := BitVec.eq_of_toNat_eq (by omega)
    exact whilePostT_exit (hi ▸ hexit B' hso (hi ▸ hw))
  · exact copy_cont hm₀ hc hso hw (by simpa using h)

/-- After the loop: store the length. -/
theorem copy_after {s₀ : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType}
    {B B' : ByteArray} {src dst n : BitVec 32} (hm₀ : MemAt s₀ mi ma mt B)
    (hc : CopyCtx B src dst n n.toNat) {Q : Post H}
    (hso : SameOutside B B' dst.toNat (4 + 4 * n.toNat))
    (hw : words B' (dst.toNat + 4) n.toNat = words B src.toNat n.toNat)
    (hQ : ∀ B'', SameOutside B B'' dst.toNat (4 + 4 * n.toNat) → wd B'' dst.toNat = n →
      words B'' (dst.toNat + 4) n.toNat = words B src.toNat n.toNat → ∀ F,
      Q (s₀.setMem ma ⟨mt, B''⟩) F (.normal [])) :
    TWP P host (s₀.setMem ma ⟨mt, B'⟩) (fr mi [src, dst, n, n])
      (vals [] ++ expression [lget 1, lget 2, istore]) Q := by
  have hm : MemAt (s₀.setMem ma ⟨mt, B'⟩) mi ma mt B' := hm₀.setMem B'
  have hsz : B'.size = B.size := hso.1
  have hb : dst.toNat + 4 ≤ B'.size := by have := hc.2.2.2.1; omega
  have hso' : SameOutside B (wr B' dst.toNat n) dst.toNat (4 + 4 * n.toNat) :=
    hso.trans (sameOutside_wr _ hb (le_refl _) (by omega))
  have hw' : words (wr B' dst.toNat n) (dst.toNat + 4) n.toNat = words B src.toNat n.toNat := by
    rw [words_wr_out _ hb (by omega), hw]
  wbegin
  wrun
  rw [setMem_setMem]
  exact w_end (m := .total) (rs := []) (hQ _ hso' (wd_wr_same _ hb) hw' _)

/-- **The body of `ba_copy`.** -/
theorem copy_body {s₀ : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType}
    {B : ByteArray} {src dst n : BitVec 32} (hm₀ : MemAt s₀ mi ma mt B)
    (hc : CopyCtx B src dst n n.toNat) {Q : Post H}
    (hQ : ∀ B'', SameOutside B B'' dst.toNat (4 + 4 * n.toNat) → wd B'' dst.toNat = n →
      words B'' (dst.toNat + 4) n.toNat = words B src.toNat n.toNat → ∀ F,
      Q (s₀.setMem ma ⟨mt, B''⟩) F (.normal [])) :
    TWP P host s₀ (fr mi [src, dst, n, 0]) (vals [] ++ expression
      [while_ copyLoop, lget 1, lget 2, istore]) Q := by
  have hI : CInv s₀ mi ma mt B src dst n n.toNat s₀ (fr mi [src, dst, n, 0]) :=
    ⟨B, 0, hm₀.setMem_self.symm, rfl, by simp, SameOutside.refl _ _ _, by simp [words]⟩
  wbegin
  exact t_while (Inv := CInv s₀ mi ma mt B src dst n n.toNat) (V := CV n) hI
    (fun _ _ hI => copy_iter hm₀ hc hI fun B' hso hw => copy_after hm₀ hc hso hw hQ)

/-- Three `i32` arguments determine their values. -/
theorem args3_inj {a b c a' b' c' : BitVec 32}
    (h : [Val.i32 a, .i32 b, .i32 c] = [.i32 a', .i32 b', .i32 c']) : a = a' ∧ b = b' ∧ c = c' := by
  simp only [List.cons.injEq, and_true] at h
  exact ⟨i32_inj h.1.symm, i32_inj h.2.1.symm, i32_inj h.2.2.symm⟩

/-- A bounded array from its length cell and its words. -/
theorem BA.mk' {B : ByteArray} {x n : Nat} {α : List (BitVec 32)}
    (hl : wd B x = BitVec.ofNat 32 α.length) (hw : words B (x + 4) α.length = α)
    (hn : α.length ≤ n) (hmax : x + 4 + 4 * n ≤ int32Max) (hb : x + 4 + 4 * n ≤ B.size) :
    BA B x n α := ⟨hl, hw, hn, hmax, hb⟩

/-- The postcondition of `ba_copy`, for every capacity the caller may name. -/
theorem copy_post {a : Nat} {fi : FuncInst H} {s : Store H} {src dst n : BitVec 32} {ma : Nat}
    {mt : MemoryType} {B B'' : ByteArray} (hm : MemAt s fi.module ma mt B)
    (hso : SameOutside B B'' dst.toNat (4 + 4 * n.toNat)) (hl : wd B'' dst.toNat = n)
    (hw : words B'' (dst.toNat + 4) n.toNat = words B src.toNat n.toNat) :
    (baCopySpec a fi).post s [.i32 src, .i32 dst, .i32 n] (s.setMem ma ⟨mt, B''⟩) (.normal []) := by
  intro src' dst' n' ma' mt' B' cap hargs hm' hn _ _ hd1 hd2 _
  obtain ⟨rfl, rfl, rfl⟩ := args3_inj hargs
  obtain ⟨rfl, rfl, rfl⟩ := hm'.unique hm
  have hlen : (words B src.toNat n.toNat).length = n.toNat := length_words _ _
  have hl' : wd B'' dst.toNat = BitVec.ofNat 32 (words B src.toNat n.toNat).length := by
    rw [hlen, hl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine ⟨rfl, B'', rfl, BA.mk' hl' (by rw [hlen, hw]) (by omega) hd2 (by rw [hso.1]; exact hd1),
    hso.mono (le_refl _) (by omega)⟩

/-- **`ba_copy` meets `baCopySpec`.** -/
theorem baCopy_valid {a : Nat} {fi : FuncInst H} (hcode : fi.code = .wasm baCopyFunc)
    (har : HasArity fi 3 0) : TFSpecAt P host a (baCopySpec a fi) := by
  obtain ⟨ps, rs, he, hps, hrs⟩ := har
  refine TFSpecAt.of_body (fun _ _ h => h.1) hcode he ?_ ?_
  · rintro s args ⟨-, src, dst, n, ma, mt, B, cap, hargs, -⟩
    simp [hargs, hps]
  · rintro s args ⟨-, src, dst, n, ma, mt, B, cap, hargs, hm, hn, hs1, hs2, hd1, hd2, hdis⟩ f vs₀
    have hc : CopyCtx B src dst n n.toNat :=
      ⟨le_refl _, hs1, hs2, by omega, by have : int32Max = 2 ^ 31 - 1 := rfl; omega, by omega⟩
    rw [hargs, forCall_baCopy, baCopyFunc_body]
    exact copy_body hm hc fun B'' hso hl hw F =>
      bodyPostT_normal (by simp [hrs]) (copy_post hm hso hl hw)

/-! ## `ba_insert` -/

/-- Inserting at index `i` is the prefix, the element and the suffix. -/
theorem insertIdx_eq_take_drop {α : Type} (a : α) :
    ∀ (l : List α) (i : Nat), i ≤ l.length → l.insertIdx i a = l.take i ++ a :: l.drop i
  | l, 0, _ => by simp [List.insertIdx_zero]
  | [], _ + 1, h => by simp at h
  | b :: l, i + 1, h => by
    rw [List.insertIdx_succ_cons, insertIdx_eq_take_drop a l i (by simpa using h)]
    simp

/-- The loop of `ba_insert`. -/
abbrev insLoop : List Instr := [lget 3, lget 1, .intRelOp .i32 (.le .unsigned), brIf 1,
  lget 0, lget 3, c32 4, imul, iadd,
  lget 0, lget 3, c32 4, imul, iadd, iload,
  .intStore .i32 none ⟨0⟩ ⟨2, 4⟩,
  lget 3, c32 1, isub, lset 3, br 0]

/-- The code of `ba_insert` after its loop. -/
abbrev insAfter : List Instr := [lget 0, lget 1, c32 4, imul, iadd, lget 2,
  .intStore .i32 none ⟨0⟩ ⟨2, 4⟩, lget 0, lget 0, iload, c32 1, iadd, istore]

theorem baInsertFunc_body : baInsertFunc.body =
    [lget 0, iload, lset 3, while_ insLoop] ++ insAfter := rfl

theorem forCall_baInsert (mi : ModuleInst) (x j v : BitVec 32) :
    Frame.forCall mi [.i32 x, .i32 j, .i32 v] baInsertFunc.locals = fr mi [x, j, v, 0] :=
  rfl

/-- The facts of `ba_insert`'s loop, for the array `α` at `x` in `B` and the hole at `i`:
`B'` equals `B` outside the cells `[0, |α|]`, cells `[0, i)` hold `α.take i` and cells
`(i, |α|]` hold `α.drop i`. -/
def IFacts (B B' : ByteArray) (x : Nat) (α : List (BitVec 32)) (i : Nat) : Prop :=
  SameOutside B B' (x + 4) (4 * (α.length + 1)) ∧ words B' (x + 4) i = α.take i ∧
    words B' (x + 4 + 4 * (i + 1)) (α.length - i) = α.drop i

/-- **The invariant of `ba_insert`'s loop.** -/
def IInv (s₀ : Store H) (mi : ModuleInst) (ma : Nat) (mt : MemoryType) (B : ByteArray)
    (x j v : BitVec 32) (α : List (BitVec 32)) (s : Store H) (f : Frame) : Prop :=
  ∃ (B' : ByteArray) (i : BitVec 32), s = s₀.setMem ma ⟨mt, B'⟩ ∧ f = fr mi [x, j, v, i] ∧
    j.toNat ≤ i.toNat ∧ i.toNat ≤ α.length ∧ IFacts B B' x.toNat α i.toNat

/-- The variant `i`. -/
def IV (_ : Store H) (f : Frame) : Nat := loc f 3

theorem IV_fr {mi : ModuleInst} {x j v i : BitVec 32} {s : Store H} :
    IV s (fr mi [x, j, v, i]) = i.toNat := by
  simp only [IV, loc_fr (L := [x, j, v, i]) (k := 3) (by simp), List.getD_cons_succ,
    List.getD_cons_zero]

/-- The cell below the hole `k + 1` holds `α[k]`, and the cells below it `α.take k`. -/
theorem below_hole {B' : ByteArray} {x k : Nat} {α : List (BitVec 32)} (hk : k < α.length)
    (hw : words B' (x + 4) (k + 1) = α.take (k + 1)) :
    words B' (x + 4) k = α.take k ∧ wd B' (x + 4 * (k + 1)) = α[k] := by
  rw [words_snoc, List.take_succ_eq_append_getElem hk] at hw
  obtain ⟨h1, h2⟩ := List.append_inj' hw rfl
  refine ⟨h1, ?_⟩
  rw [show x + 4 * (k + 1) = x + 4 + 4 * k by omega]
  simpa using h2

/-- **One shift**: cell `k + 1` gets cell `k`, the hole moves to `k`. -/
theorem shift_step {B B' : ByteArray} {x k : Nat} {α : List (BitVec 32)} (hk : k < α.length)
    (hb : x + 4 + 4 * (α.length + 1) ≤ B.size) (hf : IFacts B B' x α (k + 1)) :
    IFacts B (wr B' (x + 4 * (k + 1) + 4) (wd B' (x + 4 * (k + 1)))) x α k := by
  obtain ⟨hso, hw1, hw2⟩ := hf
  obtain ⟨hpre, hcell⟩ := below_hole hk hw1
  have hb' : x + 4 * (k + 1) + 4 + 4 ≤ B'.size := by rw [hso.1]; omega
  have hm : α.length - k = (α.length - (k + 1)) + 1 := by omega
  refine ⟨hso.trans (sameOutside_wr _ hb' (by omega) (by omega)), ?_, ?_⟩
  · rw [words_wr_out _ hb' (by omega), hpre]
  · rw [hm, words_succ, show x + 4 + 4 * (k + 1) = x + 4 * (k + 1) + 4 by omega,
      wd_wr_same _ hb', words_wr_out _ hb' (by omega), hcell,
      show x + 4 * (k + 1) + 4 + 4 = x + 4 + 4 * (k + 1 + 1) by omega, hw2,
      List.drop_eq_getElem_cons hk]

/-- The shift and the decrement of `i`, for `j < i`. -/
theorem ins_cont {s₀ : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType}
    {B B' : ByteArray} {x j v i : BitVec 32} {n : Nat} {α : List (BitVec 32)}
    (hm₀ : MemAt s₀ mi ma mt B) (hO : BA B x.toNat n α) (hn : α.length < n) {rest : List Admin}
    {Q : Post H} (hji : j.toNat < i.toNat) (hil : i.toNat ≤ α.length)
    (hf : IFacts B B' x.toNat α i.toNat) :
    TWP P host (s₀.setMem ma ⟨mt, B'⟩) (fr mi [x, j, v, i]) (vals [] ++ expression
      [lget 0, lget 3, c32 4, imul, iadd, lget 0, lget 3, c32 4, imul, iadd, iload,
        .intStore .i32 none ⟨0⟩ ⟨2, 4⟩, lget 3, c32 1, isub, lset 3, br 0])
      (whilePostT P host (IInv s₀ mi ma mt B x j v α) IV i.toNat rest Q) := by
  have hm : MemAt (s₀.setMem ma ⟨mt, B'⟩) mi ma mt B' := hm₀.setMem B'
  obtain ⟨-, -, -, hmax, hb⟩ := hO
  have hmax' : x.toNat + 4 + 4 * n ≤ 2 ^ 31 - 1 := hmax
  have hsz : B'.size = B.size := hf.1.1
  have hxi : (x + i * 4#32).toNat = x.toNat + 4 * i.toNat :=
    addr_toNat (n := n) (by omega) (by omega)
  have e4 : ((4 : Fin (2 ^ 64)) : Nat) = 4 := rfl
  have hi1 : (i - 1#32).toNat = i.toNat - 1 := by bv_omega
  have hk : i.toNat = (i.toNat - 1) + 1 := by omega
  have hf' : IFacts B (wr B' (x.toNat + 4 * i.toNat + 4) (wd B' (x.toNat + 4 * i.toNat)))
      x.toNat α (i - 1#32).toNat := by
    rw [hi1]
    rw [hk] at hf ⊢
    exact shift_step (by omega) (by omega) hf
  have hv : IV s₀ (fr mi [x, j, v, i - 1#32]) < i.toNat := by rw [IV_fr]; omega
  wbegin
  wrun
  rw [setMem_setMem, hxi, e4]
  exact t_br (whilePostT_cont ⟨_, i - 1#32, rfl, rfl, by omega, by omega, hf'⟩ hv)

/-- The facts after `ba_insert`, for the memory `B₂`. -/
def InsDone (B B₂ : ByteArray) (x j v : BitVec 32) (α : List (BitVec 32)) : Prop :=
  SameOutside B B₂ x.toNat (4 + 4 * (α.length + 1)) ∧
    wd B₂ x.toNat = BitVec.ofNat 32 (α.length + 1) ∧
    words B₂ (x.toNat + 4) (α.length + 1) = α.insertIdx j.toNat v

/-- The words after storing `v` in the hole `j`. -/
theorem ins_place {B B' : ByteArray} {x j : Nat} {v : BitVec 32} {α : List (BitVec 32)}
    (hj : j ≤ α.length) (hb : x + 4 + 4 * (α.length + 1) ≤ B.size) (hf : IFacts B B' x α j) :
    words (wr B' (x + 4 * j + 4) v) (x + 4) (α.length + 1) = α.insertIdx j v := by
  obtain ⟨hso, hw1, hw2⟩ := hf
  have hb' : x + 4 * j + 4 + 4 ≤ B'.size := by rw [hso.1]; omega
  have hm : α.length + 1 = j + ((α.length - j) + 1) := by omega
  rw [hm, words_append, words_succ, show x + 4 + 4 * j = x + 4 * j + 4 by omega, wd_wr_same _ hb',
    words_wr_out _ hb' (by omega), words_wr_out _ hb' (by omega),
    show x + 4 * j + 4 + 4 = x + 4 + 4 * (j + 1) by omega, hw1, hw2,
    insertIdx_eq_take_drop v α j hj]

/-- The facts after `ba_insert`'s two stores. -/
theorem ins_done {B B' : ByteArray} {x j v : BitVec 32} {n : Nat} {α : List (BitVec 32)}
    (hO : BA B x.toNat n α) (hn : α.length < n) (hj : j.toNat ≤ α.length)
    (hf : IFacts B B' x.toNat α j.toNat) :
    let B₁ := wr B' (x.toNat + 4 * j.toNat + 4) v
    InsDone B (wr B₁ x.toNat (wd B₁ x.toNat + 1#32)) x j v α := by
  intro B₁
  obtain ⟨hl, -, -, -, hb⟩ := hO
  have hso := hf.1
  have hb' : x.toNat + 4 * j.toNat + 4 + 4 ≤ B'.size := by rw [hso.1]; omega
  have hb₁ : x.toNat + 4 ≤ B₁.size := by rw [size_wr _ hb', hso.1]; omega
  have hl₁ : wd B₁ x.toNat = BitVec.ofNat 32 α.length := by
    rw [wd_wr_ne _ hb' (by omega), hso.wd_eq (by omega), hl]
  have hso₁ : SameOutside B B₁ x.toNat (4 + 4 * (α.length + 1)) :=
    (hso.mono (by omega) (by omega)).trans (sameOutside_wr _ hb' (by omega) (by omega))
  refine ⟨hso₁.trans (sameOutside_wr _ hb₁ (le_refl _) (by omega)), ?_, ?_⟩
  · rw [wd_wr_same _ hb₁, hl₁]
    exact BitVec.eq_of_toNat_eq (by simp)
  · rw [words_wr_out _ hb₁ (by omega)]
    exact ins_place hj (by omega) hf

/-- After the loop: store `v` in the hole and increment the length. -/
theorem ins_after {s₀ : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType}
    {B B' : ByteArray} {x j v : BitVec 32} {n : Nat} {α : List (BitVec 32)}
    (hm₀ : MemAt s₀ mi ma mt B) (hO : BA B x.toNat n α) (hn : α.length < n)
    (hj : j.toNat ≤ α.length) (hf : IFacts B B' x.toNat α j.toNat) {Q : Post H}
    (hQ : ∀ B₂, InsDone B B₂ x j v α → ∀ F, Q (s₀.setMem ma ⟨mt, B₂⟩) F (.normal [])) :
    TWP P host (s₀.setMem ma ⟨mt, B'⟩) (fr mi [x, j, v, j]) (vals [] ++ expression insAfter) Q := by
  have hm : MemAt (s₀.setMem ma ⟨mt, B'⟩) mi ma mt B' := hm₀.setMem B'
  have hmax : x.toNat + 4 + 4 * n ≤ 2 ^ 31 - 1 := hO.2.2.2.1
  have hb : x.toNat + 4 + 4 * n ≤ B.size := hO.2.2.2.2
  have hsz : B'.size = B.size := hf.1.1
  have hxj : (x + j * 4#32).toNat = x.toNat + 4 * j.toNat :=
    addr_toNat (n := n) (by omega) (by omega)
  have e4 : ((4 : Fin (2 ^ 64)) : Nat) = 4 := rfl
  have hd := ins_done (v := v) hO hn hj hf
  wbegin
  wrun
  rw [hxj, e4] at *
  rw [setMem_setMem, setMem_setMem]
  exact w_end (m := .total) (rs := []) (hQ _ hd _)

/-- **One iteration of `ba_insert`'s loop.** -/
theorem ins_iter {s₀ : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType}
    {B : ByteArray} {x j v : BitVec 32} {n : Nat} {α : List (BitVec 32)}
    (hm₀ : MemAt s₀ mi ma mt B) (hO : BA B x.toNat n α) (hn : α.length < n) {rest : List Admin}
    {Q : Post H} {s : Store H} {f : Frame} (hI : IInv s₀ mi ma mt B x j v α s f)
    (hexit : ∀ B', IFacts B B' x.toNat α j.toNat →
      TWP P host (s₀.setMem ma ⟨mt, B'⟩) (fr mi [x, j, v, j]) (vals [] ++ rest) Q) :
    TWP P host s f (vals [] ++ expression insLoop)
      (whilePostT P host (IInv s₀ mi ma mt B x j v α) IV (IV s f) rest Q) := by
  obtain ⟨B', i, hs, hf, hji, hil, hfacts⟩ := hI
  have hm : MemAt (s₀.setMem ma ⟨mt, B'⟩) mi ma mt B' := hm₀.setMem B'
  rw [hs, hf, IV_fr]
  wbegin
  wrun
  refine t_brIf (fun h => ?_) (fun h => ?_)
  · have hle : i.toNat ≤ j.toNat := by simpa using h
    have hi : i = j := BitVec.eq_of_toNat_eq (by omega)
    exact whilePostT_exit (hi ▸ hexit B' (hi ▸ hfacts))
  · exact ins_cont hm₀ hO hn (by simpa using h) hil hfacts

/-- **The body of `ba_insert`.** -/
theorem ins_body {s₀ : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType}
    {B : ByteArray} {x j v : BitVec 32} {n : Nat} {α : List (BitVec 32)}
    (hm₀ : MemAt s₀ mi ma mt B) (hO : BA B x.toNat n α) (hn : α.length < n)
    (hj : j.toNat ≤ α.length) {Q : Post H}
    (hQ : ∀ B₂, InsDone B B₂ x j v α → ∀ F, Q (s₀.setMem ma ⟨mt, B₂⟩) F (.normal [])) :
    TWP P host s₀ (fr mi [x, j, v, 0]) (vals [] ++ expression
      ([lget 0, iload, lset 3, while_ insLoop] ++ insAfter)) Q := by
  have hmax : x.toNat + 4 + 4 * n ≤ 2 ^ 31 - 1 := hO.2.2.2.1
  have hb : x.toNat + 4 + 4 * n ≤ B.size := hO.2.2.2.2
  have hlen : (wd B x.toNat).toNat = α.length := hO.len
  have hI : IInv s₀ mi ma mt B x j v α s₀ (fr mi [x, j, v, wd B x.toNat]) :=
    ⟨B, wd B x.toNat, hm₀.setMem_self.symm, rfl, by omega, by omega, SameOutside.refl _ _ _,
      by rw [hlen, hO.2.1, List.take_length], by rw [hlen]; simp [words]⟩
  wbegin
  wrun
  exact t_while (Inv := IInv s₀ mi ma mt B x j v α) (V := IV) hI
    (fun _ _ hI => ins_iter hm₀ hO hn hI fun B' hf => ins_after hm₀ hO hn hj hf hQ)

/-- The postcondition of `ba_insert`, for every capacity the caller may name. -/
theorem ins_post {a : Nat} {fi : FuncInst H} {s : Store H} {x j v : BitVec 32} {ma : Nat}
    {mt : MemoryType} {B B₂ : ByteArray} {n : Nat} {α : List (BitVec 32)}
    (hm : MemAt s fi.module ma mt B) (hO : BA B x.toNat n α) (hj : j.toNat ≤ α.length)
    (hd : InsDone B B₂ x j v α) :
    (baInsertSpec a fi).post s [.i32 x, .i32 j, .i32 v] (s.setMem ma ⟨mt, B₂⟩) (.normal []) := by
  intro x' j' v' ma' mt' B' n' α' hargs hm' hO' _ hn'
  obtain ⟨rfl, rfl, rfl⟩ := args3_inj hargs
  obtain ⟨rfl, rfl, rfl⟩ := hm'.unique hm
  obtain rfl : α' = α := hO.unique hO'
  obtain ⟨hso, hl, hw⟩ := hd
  have hlen : (α'.insertIdx j.toNat v).length = α'.length + 1 :=
    List.length_insertIdx_of_le_length hj v
  refine ⟨rfl, B₂, rfl, BA.mk' (by rw [hlen, hl]) (by rw [hlen, hw]) (by omega) hO'.2.2.2.1
    (by rw [hso.1]; exact hO'.2.2.2.2), hso.mono (le_refl _) (by omega)⟩

/-- **`ba_insert` meets `baInsertSpec`.** -/
theorem baInsert_valid {a : Nat} {fi : FuncInst H} (hcode : fi.code = .wasm baInsertFunc)
    (har : HasArity fi 3 0) : TFSpecAt P host a (baInsertSpec a fi) := by
  obtain ⟨ps, rs, he, hps, hrs⟩ := har
  refine TFSpecAt.of_body (fun _ _ h => h.1) hcode he ?_ ?_
  · rintro s args ⟨-, x, j, v, ma, mt, B, n, α, hargs, -⟩
    simp [hargs, hps]
  · rintro s args ⟨-, x, j, v, ma, mt, B, n, α, hargs, hm, hO, hj, hn⟩ f vs₀
    rw [hargs, forCall_baInsert, baInsertFunc_body]
    exact ins_body hm hO hn hj fun B₂ hd F =>
      bodyPostT_normal (by simp [hrs]) (ins_post hm hO hj hd)

end Silmaril.WasmSpec.BTree.V2
