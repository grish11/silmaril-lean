module

public import Silmaril.Proofs.WasmSpec.BTree.V2.Specs

/-!
# The B-tree library, version 2: `alloc_node` by tactics

`alloc_node` pops the last page of the free list at `8` when it is non-empty, and otherwise
grows memory `0` by one page (`t_grow`, the every-run rule for `memory.grow` over the `i32`
view, covering both outcomes), returning `-1` when growth fails or the new page is beyond
`32767`. Facts about grown memories (`grown`: zero bytes appended) are proved here too.
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

/-- The bytes `B` grown by `n` pages of zeros. -/
def grown (B : ByteArray) (n : Nat) : ByteArray :=
  B ++ ByteArray.mk (Array.replicate (n * 65536) 0)

/-- `MemAt` after replacing the memory, of any type. -/
theorem MemAt.setMemT {s : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType}
    {B : ByteArray} (h : MemAt s mi ma mt B) (mt' : MemoryType) (B' : ByteArray) :
    MemAt (s.setMem ma ⟨mt', B'⟩) mi ma mt' B' := by
  have hlt : ma < s.mems.length := by
    by_contra hc
    have h2 := h.2
    rw [List.getElem?_eq_none (by omega)] at h2
    cases h2
  exact ⟨h.1, by simp [Store.setMem, hlt]⟩

/-- A successful growth appends zero pages, keeps the address type and stays within the
address type's page bound. -/
theorem grow?_bytes {mi mi' : MemInst} {n : Nat} (hg : mi.grow? n = some mi') :
    mi' = ⟨mi'.type, grown mi.bytes n⟩ ∧ mi'.type.address = mi.type.address ∧
      mi.bytes.size / 65536 + n ≤ 2 ^ (mi.type.address.width - 16) := by
  simp only [MemInst.grow?] at hg
  split at hg
  · rename_i h
    cases hg
    exact ⟨rfl, rfl, h.1⟩
  · cases hg

/-- **`memory.grow`** over the `i32` view, for total correctness: on success the memory is
`grown B n` (of a type with the same address type, the new page count within its bound) and
the result the old size in pages; on failure `-1`. -/
theorem t_grow {s : Store H} {mi : ModuleInst} {L : List (BitVec 32)} {ma : Nat}
    {mt : MemoryType} {B : ByteArray} {n : BitVec 32} {rs : List Val} {rest : List Admin}
    {Q : Post H} (hm : MemAt s mi ma mt B)
    (hsucc : ∀ mt' : MemoryType, mt'.address = mt.address →
      B.size / 65536 + n.toNat ≤ 2 ^ (mt.address.width - 16) →
      MemAt (s.setMem ma ⟨mt', grown B n.toNat⟩) mi ma mt' (grown B n.toNat) →
      TWP P host (s.setMem ma ⟨mt', grown B n.toNat⟩) (fr mi L)
        (vals (Val.i32 (BitVec.ofNat 32 (B.size / 65536)) :: rs).reverse ++ rest) Q)
    (hfail : TWP P host s (fr mi L) (vals (Val.i32 (BitVec.allOnes 32) :: rs).reverse ++ rest) Q) :
    TWP P host s (fr mi L) (vals (Val.i32 n :: rs).reverse ++
      .plain (.memoryGrow ⟨0⟩) :: rest) Q := by
  rw [vals_rev_push]
  refine Wp.memoryGrow (m := .total) (a := .i32) (n := n) (us := rs.reverse) hm.mem?
    (fun mi' hg _ => ?_) (fun _ => ?_)
  · obtain ⟨he, ha, hb⟩ := grow?_bytes hg
    have h := hsucc mi'.type ha hb (MemAt.setMemT hm _ _)
    rw [vals_rev_push] at h
    rw [he]
    exact h
  · have h := hfail
    rw [vals_rev_push] at h
    exact h

/-- The bytes of a grown memory. -/
theorem grown_toList (B : ByteArray) (n : Nat) :
    (grown B n).data.toList = B.data.toList ++ List.replicate (n * 65536) 0 := by
  simp [grown]
/-- The size of a grown memory. -/
theorem size_grown (B : ByteArray) (n : Nat) : (grown B n).size = B.size + n * 65536 := by
  rw [grown, ByteArray.size_append]
  show B.size + (Array.replicate (n * 65536) (0 : UInt8)).size = _
  rw [Array.size_replicate]
/-- A grown memory has the old bytes. -/
theorem grown_get (B : ByteArray) (n : Nat) {i : Nat} (hi : i < B.size) :
    (grown B n).data.toList[i]? = B.data.toList[i]? := by
  rw [grown_toList, List.getElem?_append_left (by simpa using hi)]
/-- Words with the same bytes, both in bounds, are equal. -/
theorem wd_of_bytes {B B' : ByteArray} {a : Nat} (hb : a + 4 ≤ B.size) (hb' : a + 4 ≤ B'.size)
    (h : ∀ i, a ≤ i → i < a + 4 → B'.data.toList[i]? = B.data.toList[i]?) : wd B' a = wd B a := by
  have hr : Silmaril.Wasm.Logic.Core.bytesAt B' ⟨a, 4⟩ = Silmaril.Wasm.Logic.Core.bytesAt B ⟨a, 4⟩ := by
    apply List.ext_getElem?
    intro i
    rw [Silmaril.Wasm.Logic.Core.getElem?_bytesAt, Silmaril.Wasm.Logic.Core.getElem?_bytesAt]
    dsimp only
    split
    · exact h _ (by omega) (by omega)
    · rfl
  rw [wd, wd, Silmaril.Wasm.Logic.Core.load_eq hb, Silmaril.Wasm.Logic.Core.load_eq hb', hr]

/-- A grown memory has the old words. -/
theorem wd_grown {B : ByteArray} (n : Nat) {a : Nat} (ha : a + 4 ≤ B.size) :
    wd (grown B n) a = wd B a :=
  wd_of_bytes ha (by rw [size_grown]; omega) fun i _ hi => grown_get B n (by omega)

/-- A grown memory has the old arrays. -/
theorem words_grown {B : ByteArray} (n : Nat) {p m : Nat} (h : p + 4 * m ≤ B.size) :
    words (grown B n) p m = words B p m := by
  unfold words
  refine List.map_congr_left fun k hk => ?_
  have hk' : k < m := List.mem_range.1 hk
  exact wd_grown n (by omega)

/-- A bounded array stays in a grown memory. -/
theorem BA.grown {B : ByteArray} {x c : Nat} {α : List (BitVec 32)} (h : BA B x c α) (n : Nat) :
    BA (grown B n) x c α := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hle : α.length ≤ c := h3
  refine ⟨by rw [wd_grown n (by omega), h1], by rw [words_grown n (by omega), h2], h3, h4, ?_⟩
  rw [size_grown]
  omega

/-- An ordered array without duplicates stays in a grown memory. -/
theorem OBAnd.grown {B : ByteArray} {x c : Nat} {α : List (BitVec 32)} (h : OBAnd B x c α)
    (n : Nat) : OBAnd (grown B n) x c α :=
  ⟨⟨h.1.1.grown n, h.1.2⟩, h.2⟩

/-- A valid page stays valid in a grown memory. -/
theorem PageOK.grown {B : ByteArray} {p : Nat} (h : PageOK B p) (n : Nat) :
    PageOK (grown B n) p := by
  refine ⟨h.1, h.2.1, ?_⟩
  rw [size_grown]
  have := h.2.2
  omega

/-- A grown memory of whole pages is of whole pages. -/
theorem grown_mod {B : ByteArray} (h : B.size % page = 0) (n : Nat) :
    (grown B n).size % page = 0 := by
  rw [size_grown]
  simp only [page] at h ⊢
  omega

/-! ## The outcomes of `alloc_node` -/

/-- Failure with the memory unchanged. -/
theorem allocPost_fail {B : ByteArray} {φ : List (BitVec 32)} (hsz : B.size % page = 0)
    (hφ : OBAnd B 8 16381 φ) (hpg : ∀ q ∈ φ, PageOK B q.toNat) : AllocPost B φ (-1) B φ :=
  ⟨hsz, le_refl _, hφ, List.Sublist.refl _, fun _ _ _ => rfl, hpg, .inl rfl⟩

/-- Failure after a growth (the new page is beyond `32767`). -/
theorem allocPost_big {B : ByteArray} {φ : List (BitVec 32)} (hsz : B.size % page = 0)
    (hφ : OBAnd B 8 16381 φ) (hpg : ∀ q ∈ φ, PageOK B q.toNat) :
    AllocPost B φ (-1) (grown B 1) φ := by
  refine ⟨grown_mod hsz 1, by rw [size_grown]; omega, hφ.grown 1, List.Sublist.refl _,
    fun i hi _ => grown_get B 1 hi, fun q hq => (hpg q hq).grown 1, .inl rfl⟩

/-- A free page lies below the memory's page count. -/
theorem PageOK.lt_pages {B : ByteArray} {q : Nat} (h : PageOK B q) : q < B.size / 65536 := by
  have := h.2.2
  simp only [page] at this
  omega

/-- A fresh page from a growth. -/
theorem allocPost_fresh {B : ByteArray} {φ : List (BitVec 32)} (hsz : B.size % page = 0)
    (hφ : OBAnd B 8 16381 φ) (hpg : ∀ q ∈ φ, PageOK B q.toNat)
    (hbig : B.size / 65536 < 32768) :
    AllocPost B φ (BitVec.ofNat 32 (B.size / 65536)) (grown B 1) φ := by
  have h8 : 8 + 4 + 4 * 16381 ≤ B.size := hφ.1.1.2.2.2.2
  have hp : (BitVec.ofNat 32 (B.size / 65536)).toNat = B.size / 65536 := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hsz' : B.size % 65536 = 0 := hsz
  have hok : PageOK (grown B 1) (BitVec.ofNat 32 (B.size / 65536)).toNat := by
    refine ⟨by rw [hp]; omega, by rw [hp]; exact hbig, ?_⟩
    rw [hp, size_grown]
    show 65536 * _ ≤ _
    omega
  have hnot : BitVec.ofNat 32 (B.size / 65536) ∉ φ := fun h => by
    have := (hpg _ h).lt_pages
    omega
  exact ⟨grown_mod hsz 1, by rw [size_grown]; omega, hφ.grown 1, List.Sublist.refl _,
    fun i hi _ => grown_get B 1 hi, fun q hq => (hpg q hq).grown 1,
    .inr ⟨hok, hnot, .inr (by rw [hp]; show _ ≤ 65536 * _; omega)⟩⟩

/-- PageOK depends only on the memory's size. -/
theorem PageOK.of_size {B B' : ByteArray} {p : Nat} (h : PageOK B p) (hs : B.size ≤ B'.size) :
    PageOK B' p :=
  ⟨h.1, h.2.1, le_trans h.2.2 hs⟩

/-- The last element of a list without duplicates is not among the others. -/
theorem last_not_mem_take {φ : List (BitVec 32)} (hn : φ.Nodup) (h1 : 1 ≤ φ.length) :
    φ.getD (φ.length - 1) 0 ∉ φ.take (φ.length - 1) := by
  intro hm
  have hsplit : φ.take (φ.length - 1) ++ φ.drop (φ.length - 1) = φ := List.take_append_drop _ _
  have hd : φ.getD (φ.length - 1) 0 ∈ φ.drop (φ.length - 1) := by
    rw [getD_of_lt _ (by omega)]
    exact List.mem_iff_getElem.2 ⟨0, by simp; omega, by simp⟩
  rw [← hsplit] at hn
  exact List.disjoint_of_nodup_append hn hm hd

/-- The free list after popping its last page. -/
theorem OBAnd.pop {B : ByteArray} {φ : List (BitVec 32)} (hφ : OBAnd B 8 16381 φ)
    (h1 : 1 ≤ φ.length) :
    OBAnd (wr B 8 (BitVec.ofNat 32 φ.length - 1#32)) 8 16381 (φ.take (φ.length - 1)) := by
  obtain ⟨⟨⟨h8, hw, hcap, hmax, hb⟩, hs⟩, hn⟩ := hφ
  have hb8 : 8 + 4 ≤ B.size := by omega
  have hso : SameOutside B (wr B 8 (BitVec.ofNat 32 φ.length - 1#32)) 8 4 :=
    sameOutside_wr _ hb8 (le_refl _) (le_refl _)
  have htl : (φ.take (φ.length - 1)).length = φ.length - 1 := by simp
  have hv : BitVec.ofNat 32 φ.length - 1#32 = BitVec.ofNat 32 (φ.length - 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have hwd : words B 12 (φ.length - 1) = φ.take (φ.length - 1) := by
    rw [← hw, show φ.length = (φ.length - 1) + 1 by omega, words_append, List.take_left']
    · simp
    · simp
  refine ⟨⟨⟨by rw [wd_wr_same _ hb8, hv, htl], ?_, by omega, hmax, by rw [hso.1]; exact hb⟩,
    hs.sublist (List.take_sublist _ _)⟩, hn.sublist (List.take_sublist _ _)⟩
  rw [htl, hso.words_eq (by omega)]
  exact hwd

/-- Popping the last free page. -/
theorem allocPost_pop {B : ByteArray} {φ : List (BitVec 32)} (hsz : B.size % page = 0)
    (hφ : OBAnd B 8 16381 φ) (hpg : ∀ q ∈ φ, PageOK B q.toNat) (h1 : 1 ≤ φ.length) :
    AllocPost B φ (φ.getD (φ.length - 1) 0) (wr B 8 (BitVec.ofNat 32 φ.length - 1#32))
      (φ.take (φ.length - 1)) := by
  have hb8 : 8 + 4 ≤ B.size := by have := hφ.1.1.2.2.2.2; omega
  have hso : SameOutside B (wr B 8 (BitVec.ofNat 32 φ.length - 1#32)) 8 4 :=
    sameOutside_wr _ hb8 (le_refl _) (le_refl _)
  have hs : (wr B 8 (BitVec.ofNat 32 φ.length - 1#32)).size = B.size := hso.1
  have hmem : φ.getD (φ.length - 1) 0 ∈ φ := by
    rw [getD_of_lt _ (by omega)]
    exact List.getElem_mem _
  refine ⟨by rw [hs]; exact hsz, by rw [hs], hφ.pop h1, List.take_sublist _ _,
    fun i _ hi => hso.2 i (by omega), fun q hq => (hpg q (List.mem_of_mem_take hq)).of_size
      (by rw [hs]), .inr ⟨(hpg _ hmem).of_size (by rw [hs]), last_not_mem_take hφ.2 h1,
      .inl hmem⟩⟩

/-! ## The body -/

/-- The pop arm of `alloc_node`. -/
abbrev popArm : List Instr := [lget 0, c32 1, isub, lset 0, c32 8, lget 0, istore, lget 0, c32 4,
  imul, .intLoad .i32 none ⟨0⟩ ⟨2, 12⟩, .return_]

theorem allocFunc_body : allocFunc.body = [c32 8, iload, lset 0, lget 0, .if_ .empty popArm [],
    c32 1, .memoryGrow ⟨0⟩, lset 1, lget 1, c32 32768, igeu,
    .if_ .empty [c32 4294967295, .return_] [], lget 1] := rfl

theorem forCall_alloc (mi : ModuleInst) :
    Frame.forCall mi [] allocFunc.locals = fr mi [0, 0] := rfl

/-- The address of the last free page's cell. -/
theorem last_addr {n : Nat} (h1 : 1 ≤ n) (h2 : n ≤ 16381) :
    ((BitVec.ofNat 32 n - 1#32) * 4#32).toNat = 4 * (n - 1) := by
  have : (BitVec.ofNat 32 n - 1#32).toNat = n - 1 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  rw [BitVec.toNat_mul, this]
  have e : (4#32).toNat = 4 := rfl
  rw [e]
  omega

/-- **The pop arm**: store the decremented length, return the last free page. -/
theorem alloc_pop {s : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType} {B : ByteArray}
    {φ : List (BitVec 32)} {rest : List Admin} {Q : Post H} (hm : MemAt s mi ma mt B)
    (hφ : OBAnd B 8 16381 φ) (h1 : 1 ≤ φ.length)
    (hQ : ∀ F, Q (s.setMem ma ⟨mt, wr B 8 (BitVec.ofNat 32 φ.length - 1#32)⟩) F
      (.ret [.i32 (φ.getD (φ.length - 1) 0)])) :
    TWP P host s (fr mi [BitVec.ofNat 32 φ.length, 0]) (vals [] ++ expression popArm)
      (armPostT P host [] rest Q) := by
  have hcap : φ.length ≤ 16381 := hφ.1.1.2.2.1
  have hsz : 8 + 4 + 4 * 16381 ≤ B.size := hφ.1.1.2.2.2.2
  have hidx := last_addr h1 hcap
  have hg : φ.getD (φ.length - 1) 0 = wd B (8 + 4 + 4 * (φ.length - 1)) := by
    have h := getD_words (B := B) (p := 8 + 4) (n := φ.length) (k := φ.length - 1) (by omega)
    rwa [hφ.1.1.2.1] at h
  have hv : wd B (4 * (φ.length - 1) + 12) = φ.getD (φ.length - 1) 0 := by
    rw [hg]
    congr 1
    omega
  have e8 : (8#32).toNat = 8 := rfl
  have e12 : ((12 : Fin (2 ^ 64)) : Nat) = 12 := rfl
  wbegin
  wrun
  rw [e8, hidx, e12, wd_wr_ne _ (by omega) (by omega), hv]
  exact t_ret (armPostT_ret (hQ _))

/-- The growth part of `alloc_node`. -/
abbrev growPart : List Instr := [c32 1, .memoryGrow ⟨0⟩, lset 1, lget 1, c32 32768, igeu,
  .if_ .empty [c32 4294967295, .return_] [], lget 1]

/-- What the body's postcondition must accept: for every outcome allowed by `AllocPost`,
returned by `return` or by falling through. -/
def AllocQ (s : Store H) (ma : Nat) (B : ByteArray) (φ : List (BitVec 32)) (Q : Post H) : Prop :=
  ∀ (r : BitVec 32) (mt' : MemoryType) (B' : ByteArray) (φ' : List (BitVec 32)),
    mt'.address = .i32 → AllocPost B φ r B' φ' →
    (∀ F, Q (s.setMem ma ⟨mt', B'⟩) F (.ret [.i32 r])) ∧
      ∀ F, Q (s.setMem ma ⟨mt', B'⟩) F (.normal [.i32 r])

theorem minus_one : (BitVec.ofNat 32 4294967295 : BitVec 32) = -1 := by decide

/-- Return `-1`. -/
theorem alloc_minus_one {s : Store H} {f : Frame} {rest : List Admin} {Q : Post H}
    (hQ : ∀ F, Q s F (.ret [.i32 (-1)])) :
    TWP P host s f (vals [] ++ expression [c32 4294967295, .return_])
      (armPostT P host [] rest Q) := by
  wbegin
  wrun
  rw [minus_one]
  exact t_ret (armPostT_ret (hQ _))

/-- After a successful growth: the new page, unless it is beyond `32767`. -/
theorem alloc_grown {s : Store H} {mi : ModuleInst} {ma : Nat} {mt' : MemoryType}
    {B : ByteArray} {φ : List (BitVec 32)} {Q : Post H} {n : BitVec 32}
    (h32 : mt'.address = .i32) (hb : B.size / 65536 + 1 ≤ 2 ^ 16)
    (hsz : B.size % page = 0) (hφ : OBAnd B 8 16381 φ) (hpg : ∀ q ∈ φ, PageOK B q.toNat)
    (hQ : AllocQ s ma B φ Q) :
    TWP P host (s.setMem ma ⟨mt', grown B 1⟩) (fr mi [n, 0])
      (vals [Val.i32 (BitVec.ofNat 32 (B.size / 65536))].reverse ++
        expression (growPart.drop 2)) Q := by
  have hp : (BitVec.ofNat 32 (B.size / 65536)).toNat = B.size / 65536 := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  wbegin
  wrun
  refine t_if (fun hc => ?_) (fun hc => ?_)
  · exact alloc_minus_one ((hQ _ _ _ _ h32 (allocPost_big hsz hφ hpg)).1)
  · have hlt : B.size / 65536 < 32768 := by
      have : ¬ 32768 ≤ (BitVec.ofNat 32 (B.size / 65536)).toNat := by simpa using hc
      omega
    refine t_armEnd ?_
    wrun
    exact w_end (m := .total) (rs := [_]) ((hQ _ _ _ _ h32 (allocPost_fresh hsz hφ hpg hlt)).2 _)

/-- **The growth part**: grow by a page; `-1` on failure. -/
theorem alloc_grow {s : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType}
    {B : ByteArray} {φ : List (BitVec 32)} {Q : Post H} {n : BitVec 32}
    (hm : MemAt s mi ma mt B) (h32 : mt.address = .i32) (hsz : B.size % page = 0)
    (hφ : OBAnd B 8 16381 φ) (hpg : ∀ q ∈ φ, PageOK B q.toNat) (hQ : AllocQ s ma B φ Q) :
    TWP P host s (fr mi [n, 0]) (vals [] ++ expression growPart) Q := by
  have hQf : ∀ F, Q s F (.ret [.i32 (-1)]) := fun F => by
    have h := (hQ _ _ _ _ h32 (allocPost_fail hsz hφ hpg)).1 F
    rwa [hm.setMem_self] at h
  wbegin
  wrun
  refine t_grow hm (fun mt' ha hb _ => alloc_grown (ha.trans h32) (by rw [h32] at hb; exact hb)
    hsz hφ hpg hQ) ?_
  wrun
  refine t_if (fun _ => alloc_minus_one hQf) (fun hc => ?_)
  exact absurd hc (by decide)

/-- **The body of `alloc_node`**: pop the last free page if there is one, else grow. -/
theorem alloc_body {s : Store H} {mi : ModuleInst} {ma : Nat} {mt : MemoryType}
    {B : ByteArray} {φ : List (BitVec 32)} {Q : Post H}
    (hm : MemAt s mi ma mt B) (h32 : mt.address = .i32) (hsz : B.size % page = 0)
    (hφ : OBAnd B 8 16381 φ) (hpg : ∀ q ∈ φ, PageOK B q.toNat) (hQ : AllocQ s ma B φ Q) :
    TWP P host s (fr mi [0, 0]) (vals [] ++ expression
      ([c32 8, iload, lset 0, lget 0, .if_ .empty popArm []] ++ growPart)) Q := by
  have h8 : 8 + 4 + 4 * 16381 ≤ B.size := hφ.1.1.2.2.2.2
  have hcap : φ.length ≤ 16381 := hφ.1.1.2.2.1
  have hw8 : wd B 8 = BitVec.ofNat 32 φ.length := hφ.1.1.1
  have e8 : (8#32).toNat = 8 := rfl
  wbegin
  wrun
  rw [e8, hw8]
  refine t_if (fun hc => ?_) (fun _ => t_armEnd (alloc_grow hm h32 hsz hφ hpg hQ))
  have h1 : 1 ≤ φ.length := by
    rcases Nat.eq_zero_or_pos φ.length with h | h
    · exact absurd (by rw [h]; rfl) hc
    · exact h
  exact alloc_pop hm hφ h1 ((hQ _ _ _ _ h32 (allocPost_pop hsz hφ hpg h1)).1)

/-- **`alloc_node()`**: with the free pages `φ` at `8` (valid pages) and a memory of whole
pages and address type `i32`, return a page for a node or `-1` (`AllocPost`); only memory `0`
changes. (The address type matters: on a 64-bit memory of `2 ^ 32` pages or more the page
number `memory.grow` returns would wrap.) -/
def allocSpecI32 (a : Nat) (fi : FuncInst H) : FSpec H where
  pre s args := s.funcs[a]? = some fi ∧ ∃ (ma : Nat) (mt : MemoryType) (B : ByteArray)
    (φ : List (BitVec 32)), args = [] ∧ MemAt s fi.module ma mt B ∧ mt.address = .i32 ∧
    B.size % page = 0 ∧ OBAnd B 8 16381 φ ∧ ∀ q ∈ φ, PageOK B q.toNat
  post s args s' o := ∀ (ma : Nat) (mt : MemoryType) (B : ByteArray) (φ : List (BitVec 32)),
    args = [] → MemAt s fi.module ma mt B → mt.address = .i32 → B.size % page = 0 →
    OBAnd B 8 16381 φ → (∀ q ∈ φ, PageOK B q.toNat) → ∃ (r : BitVec 32) (mt' : MemoryType)
      (B' : ByteArray) (φ' : List (BitVec 32)), o = .normal [.i32 r] ∧
      s' = s.setMem ma ⟨mt', B'⟩ ∧ mt'.address = .i32 ∧ AllocPost B φ r B' φ'

/-- The postcondition of `alloc_node` for an outcome allowed by `AllocPost`. -/
theorem alloc_post {a : Nat} {fi : FuncInst H} {s : Store H} {ma : Nat} {mt mt' : MemoryType}
    {B B' : ByteArray} {φ φ' : List (BitVec 32)} {r : BitVec 32}
    (hm : MemAt s fi.module ma mt B) (hφ : OBAnd B 8 16381 φ) (h32 : mt'.address = .i32)
    (hp : AllocPost B φ r B' φ') :
    (allocSpecI32 a fi).post s [] (s.setMem ma ⟨mt', B'⟩) (.normal [.i32 r]) := by
  intro ma₂ mt₂ B₂ φ₂ _ hm₂ _ _ hφ₂ _
  obtain ⟨rfl, rfl, rfl⟩ := hm₂.unique hm
  have hφe : φ₂ = φ := hφ.1.1.unique hφ₂.1.1
  rw [hφe]
  exact ⟨r, mt', B', φ', rfl, rfl, h32, hp⟩

/-- **`alloc_node` meets `allocSpecI32`.** -/
theorem alloc_valid {a : Nat} {fi : FuncInst H} (hcode : fi.code = .wasm allocFunc)
    (har : HasArity fi 0 1) : TFSpecAt P host a (allocSpecI32 a fi) := by
  obtain ⟨ps, rs, he, hps, hrs⟩ := har
  refine TFSpecAt.of_body (fun _ _ h => h.1) hcode he ?_ ?_
  · rintro s args ⟨-, ma, mt, B, φ, hargs, -⟩
    simp [hargs, hps]
  · rintro s args ⟨-, ma, mt, B, φ, hargs, hm, h32, hsz, hφ, hpg⟩ f vs₀
    rw [hargs, forCall_alloc, allocFunc_body, hrs]
    exact alloc_body hm h32 hsz hφ hpg fun r mt' B' φ' ha hp =>
      ⟨fun _ => bodyPostT_ret (alloc_post hm hφ ha hp),
        fun _ => bodyPostT_normal rfl (alloc_post hm hφ ha hp)⟩

end Silmaril.WasmSpec.BTree.V2
