module

public import Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Ring.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.Take
public import Silmaril.Wasm.Logic.Instr.Thms
public import Silmaril.Wasm.Logic.Memory.Thms
public import Silmaril.Wasm.Verify.Kernel.Defs

/-!
# `chunkRingN cap` meets its chunk specification, for every capacity

Every proof here is generic in the capacity `cap` (`RingCap cap` bounds its slots by memory32).

* `ring_shape`: the instance has shape `MShape`: the shape without the body comparison
  (`ring_shapeNB`, `MShape.of_okNB`) and the instantiated code (`ring_code4`, `ring_code5`) are
  kernel evaluations with `cap` free (`kernel_rfl`); so are `ring_mems4`, `ring_mems5` (both
  exported functions see memory `0`), `ring_gval0`, `ring_gval1`, `ring_memlen`, `ring_size`,
  `chunkRingN_instance`. `RI cap` is the instance, irreducible so that elaboration never
  unfolds the instantiation (`RI_eq`); `ringInv_init`: the instantiated store represents the
  empty buffer; `ringInv_uniq`: a store represents at most one buffer;
* rules for the memory instructions of the example (`X.load64`, `X.store64R`), for `rem_u` by a
  non-zero constant (`remu_ok`, `X.remuC`), `sub`; slot arithmetic with `cap` symbolic
  (`capW_toNat`, `slot_addr`, `slot_ne`: distinct `i, j < cap` have disjoint slots, `slot_shift`,
  `st_next`);
* `chunkRingN_sat` (and `chunkRingN_satI`, at `Verify.instOf (chunkRingN cap)`): in every
  environment `ρ` and every profile, assuming the writer answers agree with `ρ` (no writer
  sentinel), the instance meets `chunkSSpec ringPix ppol ρ takeR (ringInv cap)`: `feed(x)` stores
  `x` in the slot after the buffered values and moves the represented buffer from `g` to
  `g ++ [x]` (or traps with `cap` values buffered); `finish(n)` with `n = 0` or `n` above the
  count returns `(0, h)`, `h` denoting `()`, keeping the buffer; otherwise its loop (invariant
  `RingLoop`: the accumulated handle denotes the list of the buffered values `i … n - 1`) builds
  the list of the first `n` buffered values, and the call returns `(n, h)` and drops them from
  the buffer by advancing the start slot. Traps keep the buffer (a store out of the page traps).

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.Ring

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics
  Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.GameLink
  Silmaril.Formats Silmaril.Formats.Api Silmaril.Accept.Handle Silmaril.Accept.Parse
  Silmaril.Accept.Mixed Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Writers Silmaril.Wasm.Game.HandleAccept.Writers.Builders
  Silmaril.Wasm.Game.HandleAccept.Parsing Silmaril.Wasm.Game.HandleAccept.Mixed.Stream
  Silmaril.Wasm.Game.HandleAccept.Mixed.Stream.Stack Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk
  Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Take
  Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Ring
  Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers
  Silmaril.Proofs.Wasm.Game.HandleAccept.Parsing.Checkers
  Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.TwoWords
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream.Stack
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.Take
open Silmaril.Wasm.Logic.Strategy (ISpec)
open Silmaril.Wasm.Logic.Core (Outcome Post Region)

/-! ## The instance

The shape (`MShape`) compares the instantiated bodies with `ringFeedBody cap`, `ringFinBody cap`
instruction by instruction, which needs the bits of `capW cap`. The rest of the shape, the
instantiated code, the globals and the memory are kernel evaluations with `cap` free
(`kernel_rfl`): neither the validator nor the instantiation reads the value of an `i32.const`. -/

section Shape

variable (cap : Nat)

/-- The instance, irreducible: elaboration never evaluates the instantiation. -/
@[irreducible] def RI : ScalarInstance := Verify.instOf (chunkRingN cap)

theorem RI_eq : RI cap = Verify.instOf (chunkRingN cap) := by
  unfold RI; rfl

/-- The exported functions. -/
abbrev ringFnsWith (preludeCode : List Instr) : List (List ValType × List Instr × List (Option Val)) :=
  [([], ringFeedWith cap preludeCode, []),
    ([.i32, .i32], ringFinBody cap, [some (.i32 0), some (.i32 0)])]

abbrev ringFns := ringFnsWith cap []

/-- `fnOkM` without the body comparison. -/
def fnOkMNB (np nr : Nat) (mf : List Nat) (locals : List ValType) (D : List (Option Val))
    (fi : FuncInst Nat) : Bool :=
  (match fi.code with
    | .wasm c => c.locals == locals
    | _ => false) &&
  (match fi.type.expand? with
    | some (.func ps rs) => ps.length == np && rs.length == nr
    | _ => false) &&
  fi.module.funcs == mf &&
  locals.map (fun t => defaultVal? ((Validation.liftVal t).substAll
    (fi.module.types.map .dt))) == D

/-- `mshapeOk` without the body comparison. -/
def mshapeOkNB (I : ScalarInstance) (fts efts : List FnType)
    (fns : List (List ValType × List Instr × List (Option Val))) (mg : List Nat) : Bool :=
  I.imports == fts && I.exports == efts &&
  I.addrs == (List.range efts.length).map (fts.length + ·) && fns.length == efts.length &&
  (List.range fts.length).all (fun k => match I.store.funcs[k]?, fts[k]? with
    | some fk, some ft => stubOkN k ft.params.length fk
    | _, _ => false) &&
  (List.range efts.length).all (fun j => match I.store.funcs[fts.length + j]?, efts[j]?, fns[j]? with
    | some fi, some eft, some (locals, _, D) =>
      fnOkMNB eft.params.length eft.results.length (List.range (fts.length + efts.length)) locals
        D fi && fi.module.globals == mg
    | _, _, _ => false)

omit cap in
theorem MShape.of_okNB {I : ScalarInstance} {fts efts : List FnType}
    {fns : List (List ValType × List Instr × List (Option Val))} {mg : List Nat}
    (h : mshapeOkNB I fts efts fns mg = true)
    (hb : ∀ j (hj : j < fns.length), ∃ fi c, I.store.funcs[fts.length + j]? = some fi ∧
      fi.code = .wasm c ∧ c.body = (fns[j]'hj).2.1) :
    MShape I fts efts fns mg := by
  unfold mshapeOkNB at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hi, he⟩, ha⟩, hl⟩, hst⟩, hf⟩ := h
  refine ⟨hi, he, ha, hl, fun k hk => ?_, fun j hj => ?_⟩
  · have hk' := List.all_eq_true.1 hst k (List.mem_range.2 hk)
    rw [List.getElem?_eq_getElem hk] at hk'
    split at hk'
    · rename_i fk ft hfk hft
      obtain rfl := Option.some.inj hft
      obtain ⟨ps, rs, h⟩ := stubOkN_spec hk'
      exact ⟨fk, ps, rs, hfk, h⟩
    · cases hk'
  · have hj' := List.all_eq_true.1 hf j (List.mem_range.2 hj)
    have hjf : j < fns.length := by rw [hl]; exact hj
    obtain ⟨fi', c', hfi', hc', hb'⟩ := hb j hjf
    rw [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hjf] at hj'
    split at hj'
    · rename_i fi eft locals body D hfi heft hfns
      obtain rfl := Option.some.inj heft
      have hfns' := Option.some.inj hfns
      rw [hfi] at hfi'
      obtain rfl := Option.some.inj hfi'
      simp only [Bool.and_eq_true, beq_iff_eq] at hj'
      obtain ⟨hok, hg⟩ := hj'
      unfold fnOkMNB at hok
      simp only [Bool.and_eq_true, beq_iff_eq] at hok
      obtain ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩ := hok
      simp only [hc', beq_iff_eq] at h₁
      split at h₂
      · rename_i ps rs hexp
        simp only [Bool.and_eq_true, beq_iff_eq] at h₂
        refine ⟨fi, c', ps, rs, hfi, hc', ?_, hb', Validation.Expand.iff.2 hexp, h₂.1, h₂.2, h₃, hg, ?_⟩
        · rw [hfns']; exact h₁
        · rw [hfns']; exact h₄
      · cases h₂
    · cases hj'

/-- **The shape without the bodies, for every capacity** (kernel evaluation with `cap` free). -/
theorem ring_shapeNB : mshapeOkNB (Verify.instOf (chunkRingN cap)) twoFTs chunkFTs (ringFns cap) [0, 1] = true := by
  kernel_rfl

/-- **The instantiated code of `feed`**, for every capacity. -/
theorem ring_code4 : ((Verify.instOf (chunkRingN cap)).store.funcs[4]?).map FuncInst.code =
    some (.wasm ⟨⟨4⟩, [], ringFeedBody cap⟩) := by
  kernel_rfl

/-- **The instantiated code of `finish`**, for every capacity. -/
theorem ring_code5 : ((Verify.instOf (chunkRingN cap)).store.funcs[5]?).map FuncInst.code =
    some (.wasm ⟨⟨5⟩, [.i32, .i32], ringFinBody cap⟩) := by
  kernel_rfl

private theorem ring_shape_of {I : ScalarInstance} {preludeCode : List Instr}
    (shape : mshapeOkNB I twoFTs chunkFTs (ringFnsWith cap preludeCode) [0, 1] = true)
    (feed : (I.store.funcs[4]?).map FuncInst.code =
      some (.wasm ⟨⟨4⟩, [], ringFeedWith cap preludeCode⟩))
    (finish : (I.store.funcs[5]?).map FuncInst.code =
      some (.wasm ⟨⟨5⟩, [.i32, .i32], ringFinBody cap⟩)) :
    MShape I twoFTs chunkFTs (ringFnsWith cap preludeCode) [0, 1] := by
  refine MShape.of_okNB shape fun j hj => ?_
  match j, hj with
  | 0, _ =>
    rw [show twoFTs.length + 0 = 4 from rfl]
    generalize I.store.funcs[4]? = o at feed ⊢
    rcases o with _ | fi
    · cases feed
    · exact ⟨fi, _, rfl, Option.some.inj feed, rfl⟩
  | 1, _ =>
    rw [show twoFTs.length + 1 = 5 from rfl]
    generalize I.store.funcs[5]? = o at finish ⊢
    rcases o with _ | fi
    · cases finish
    · exact ⟨fi, _, rfl, Option.some.inj finish, rfl⟩

theorem ring_shape : MShape (RI cap) twoFTs chunkFTs (ringFns cap) [0, 1] := by
  rw [RI_eq]
  exact ring_shape_of cap (ring_shapeNB cap) (ring_code4 cap) (ring_code5 cap)

theorem ring_mems4 : (((RI cap).store.funcs[4]?).map (·.module.mems)) = some [0] := by
  rw [RI_eq]
  kernel_rfl

theorem ring_mems5 : (((RI cap).store.funcs[5]?).map (·.module.mems)) = some [0] := by
  rw [RI_eq]
  kernel_rfl

theorem ring_gval0 : gval (Verify.instOf (chunkRingN cap)).store 0 = some (.i32 0) := by
  kernel_rfl

theorem ring_gval1 : gval (Verify.instOf (chunkRingN cap)).store 1 = some (.i32 0) := by
  kernel_rfl

theorem ring_memlen : (Verify.instOf (chunkRingN cap)).store.mems.length = 1 := by
  kernel_rfl

theorem ring_size : ((Verify.instOf (chunkRingN cap)).store.mems[0]?).map (·.bytes.size) = some 65536 := by
  kernel_rfl

theorem chunkRingN_instance : (Verify.instance? (chunkRingN cap)).isSome = true := by
  kernel_rfl

@[irreducible] def RIG : ScalarInstance := Verify.instOf (chunkRingGrowing cap)

theorem RIG_eq : RIG cap = Verify.instOf (chunkRingGrowing cap) := by
  unfold RIG; rfl

theorem growing_shape : MShape (RIG cap) twoFTs chunkFTs (ringFnsWith cap (reserveBody cap)) [0, 1] := by
  rw [RIG_eq]
  exact ring_shape_of cap (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

theorem growing_mems4 : (((RIG cap).store.funcs[4]?).map (·.module.mems)) = some [0] := by
  rw [RIG_eq]
  kernel_rfl

theorem growing_mems5 : (((RIG cap).store.funcs[5]?).map (·.module.mems)) = some [0] := by
  rw [RIG_eq]
  kernel_rfl

theorem chunkRingGrowing_instance : (Verify.instance? (chunkRingGrowing cap)).isSome = true := by
  kernel_rfl

end Shape

private theorem ringInvFor_init {I : ScalarInstance} {cap : Nat} (hc : RingCap cap)
    (first : gval I.store 0 = some (.i32 0)) (count : gval I.store 1 = some (.i32 0))
    (length : I.store.mems.length = 1)
    (width : (I.store.mems[0]?).map (·.type.address) = some .i32) : ringInvFor I cap [] I.store := by
  refine ⟨rfl, 0, 0, first, count, hc.1, rfl, Nat.zero_le _, length, ?_, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  intro mi found
  rw [found] at width
  exact Option.some.inj width

theorem ringInv_init {cap : Nat} (hc : RingCap cap) :
    ringInv cap [] (Verify.instOf (chunkRingN cap)).store := by
  exact ringInvFor_init hc (ring_gval0 cap) (ring_gval1 cap) (ring_memlen cap) (by kernel_rfl)

theorem growingRingInv_init {cap : Nat} (hc : RingCap cap) :
    growingRingInv cap [] (Verify.instOf (chunkRingGrowing cap)).store := by
  exact ringInvFor_init hc (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

theorem ringInv_uniq {I : ScalarInstance} {cap : Nat} {g g' : List (BitVec 64)} {s : Store Nat}
    (h : ringInvFor I cap g s) (h' : ringInvFor I cap g' s) : g = g' := by
  obtain ⟨-, st, cnt, h0, h1, -, hc, -, -, -, hl⟩ := h
  obtain ⟨-, st', cnt', h0', h1', -, hc', -, -, -, hl'⟩ := h'
  rw [h0] at h0'
  rw [h1] at h1'
  cases h0'
  cases h1'
  have hlen : g.length = g'.length := hc.symm.trans hc'
  refine List.ext_getElem hlen fun i hi hi' => ?_
  obtain ⟨mi, hmi, hld⟩ := hl i hi
  obtain ⟨mi', hmi', hld'⟩ := hl' i hi'
  rw [hmi] at hmi'
  cases hmi'
  rw [hld] at hld'
  exact Option.some.inj hld'

/-! ## Slots -/

section Slots

variable {cap : Nat}

theorem capW_toNat (hc : cap ≤ 536870912) : (capW cap).toNat = cap := by
  simp only [capW, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

theorem capW_ne (hc : RingCap cap) : capW cap ≠ 0 := fun h => by
  have := capW_toNat hc.2
  rw [h] at this
  have := hc.1
  simp at *
  omega

theorem remu_ok {x y : BitVec 32} (h : y ≠ 0) :
    intBinOp .i32 (.rem .unsigned) x y = .ok (x % y) := by
  simp only [intBinOp]
  split
  · exact absurd ‹_› h
  · rfl

theorem slot_addr (hc : RingCap cap) {st k : BitVec 32} (hs : st.toNat < cap)
    (hk : k.toNat < cap) : ((st + k) % capW cap * 8).toNat = slot cap st.toNat k.toNat := by
  obtain ⟨h0, h1⟩ := hc
  have h8 : (8 : BitVec 32).toNat = 8 := rfl
  rw [BitVec.toNat_mul, BitVec.toNat_umod, BitVec.toNat_add, capW_toNat h1, h8]
  simp only [Nat.reducePow]
  rw [Nat.mod_eq_of_lt (a := st.toNat + k.toNat) (by omega)]
  have hm := Nat.mod_lt (st.toNat + k.toNat) h0
  unfold slot
  generalize (st.toNat + k.toNat) % cap = r at hm ⊢
  omega

theorem slot_ne {st i j : Nat} (hi : i < cap) (hj : j < cap) (hij : i ≠ j) :
    Region.Disjoint ⟨slot cap st i, 8⟩ ⟨slot cap st j, 8⟩ := by
  have hne : (st + i) % cap ≠ (st + j) % cap := by
    intro h
    have := Nat.ModEq.add_left_cancel' st h
    unfold Nat.ModEq at this
    rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
    exact hij this
  simp only [Region.Disjoint, Region.stop, slot]
  generalize (st + i) % cap = a at hne ⊢
  generalize (st + j) % cap = b at hne ⊢
  omega

theorem slot_shift (st n j : Nat) : slot cap ((st + n) % cap) j = slot cap st (n + j) := by
  simp only [slot]
  rw [Nat.mod_add_mod, Nat.add_assoc]

theorem st_next (hc : RingCap cap) {st n : BitVec 32} (hs : st.toNat < cap)
    (hn : n.toNat ≤ cap) :
    ((st + n) % capW cap).toNat = (st.toNat + n.toNat) % cap ∧
      (st.toNat + n.toNat) % cap < cap := by
  obtain ⟨h0, h1⟩ := hc
  refine ⟨?_, Nat.mod_lt _ h0⟩
  rw [BitVec.toNat_umod, BitVec.toNat_add, capW_toNat h1]
  simp only [Nat.reducePow]
  rw [Nat.mod_eq_of_lt (a := st.toNat + n.toNat) (by omega)]

theorem cnt_sub {c n : BitVec 32} (h : n.toNat ≤ c.toNat) : (c - n).toNat = c.toNat - n.toNat := by
  rw [BitVec.toNat_sub]
  omega

theorem cnt_succ (hc : RingCap cap) {c : BitVec 32} (h : c.toNat < cap) :
    (c + 1).toNat = c.toNat + 1 := by
  have h1 : (1 : BitVec 32).toNat = 1 := rfl
  have := hc.2
  rw [BitVec.toNat_add, h1]
  omega

theorem i_pred {i : BitVec 32} (h : i ≠ 0) : (i + BitVec.allOnes 32).toNat = i.toNat - 1 ∧
    i.toNat - 1 < i.toNat := by
  have hz : i.toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq (by rw [h']; rfl))
  have ha : (BitVec.allOnes 32).toNat = 4294967295 := rfl
  have hl : i.toNat < 4294967296 := i.isLt
  rw [BitVec.toNat_add, ha]
  constructor <;> omega

end Slots

/-! ## Rules -/

section Rules

variable {P : Profile} {host : HostSemantics Nat} {s : Store Nat} {F : Frame} {us : List Val}
  {is : List Instr} {Q : Post Nat}

theorem X.remuC {x c : BitVec 32} (hc : c ≠ 0)
    (h : HWP P host s F (vals (us ++ [.i32 (x % c)]) ++ expression is) Q) :
    HWP P host s F (vals (us ++ [.i32 x]) ++
      expression (.intConst .i32 c :: .intBinOp .i32 (.rem .unsigned) :: is)) Q := by
  refine X.i32Const ?_
  rw [List.append_assoc]
  exact Wp.intBinOp (m := .part) (t := .i32) (x := x) (y := c) (z := (x % c : BitVec 32))
    (remu_ok hc) h

theorem X.mul8 {x : BitVec 32}
    (h : HWP P host s F (vals (us ++ [.i32 (x * 8)]) ++ expression is) Q) :
    HWP P host s F (vals (us ++ [.i32 x]) ++
      expression (.intConst .i32 8 :: .intBinOp .i32 .mul :: is)) Q := by
  refine X.i32Const ?_
  rw [List.append_assoc]
  exact Wp.intBinOp (m := .part) (t := .i32) (x := x) (y := 8) (z := (x * 8 : BitVec 32)) rfl h

theorem X.sub32 {x y : BitVec 32}
    (h : HWP P host s F (vals (us ++ [.i32 (x - y)]) ++ expression is) Q) :
    HWP P host s F (vals (us ++ [.i32 x] ++ [.i32 y]) ++ expression (.intBinOp .i32 .sub :: is))
      Q := by
  rw [List.append_assoc]
  exact Wp.intBinOp (m := .part) (t := .i32) (x := x) (y := y) (z := x - y) rfl h

theorem mem?_of {F : Frame} (hF : F.module.mems = [0]) {mi : MemInst}
    (hmi : s.mems[0]? = some mi) : s.mem? F ⟨0⟩ = some (0, mi) := by
  simp only [Store.mem?, hF]
  rw [show ([0] : List Nat)[(⟨0⟩ : MemIdx).toNat]? = some 0 from rfl]
  simp [hmi]

theorem store_none_lt {B : ByteArray} {a n : Nat} {w : BitVec (8 * n)}
    (h : Memory.store B a w = none) : B.size < a + n := by
  unfold Memory.store Memory.writeBytes at h
  split at h
  · cases h
  · rename_i hb
    rw [Memory.encodeLE_size] at hb
    omega

/-- A full-width `i64` load from memory `0` of a store with one memory. -/
theorem X.load64 {addr : BitVec 32} (hF : F.module.mems = [0]) (hl : s.mems.length = 1)
    (htrap : Q s F .trap)
    (h : ∀ mi c, s.mems[0]? = some mi →
      Memory.load mi.bytes addr.toNat 8 = some c →
      HWP P host s F (vals (us ++ [.i64 c]) ++ expression is) Q) :
    HWP P host s F (vals (us ++ [.i32 addr]) ++ expression (.intLoad .i64 none ⟨0⟩ ⟨0, 0⟩ :: is))
      Q := by
  obtain ⟨mi, hmi⟩ : ∃ mi, s.mems[0]? = some mi :=
    ⟨s.mems[0]'(by omega), List.getElem?_eq_getElem _⟩
  have hm := mem?_of hF hmi
  rcases hld : Memory.load mi.bytes (effAddr addr.toNat ⟨0, 0⟩) (IntType.i64.width / 8) with
    _ | c
  · refine Wp.intLoad_oob (m := .part) (a := .i32) (i := addr) (t := .i64) hm ?_ htrap
    unfold Memory.load Memory.readBytes at hld
    split at hld
    · cases hld
    · rename_i hb
      exact Nat.lt_of_not_le hb
  · refine Wp.intLoad (m := .part) (a := .i32) (i := addr) (t := .i64) hm hld ?_
    exact h mi c hmi hld

/-- A full-width `i64` store to memory `0` of a store with one memory. -/
theorem X.store64R {addr : BitVec 32} {v : BitVec 64} (hF : F.module.mems = [0])
    (hl : s.mems.length = 1) (htrap : Q s F .trap)
    (h : ∀ mi b, s.mems[0]? = some mi →
      Memory.store mi.bytes addr.toNat (count := 8) v = some b →
      HWP P host (s.setMem 0 { mi with bytes := b }) F (vals us ++ expression is) Q) :
    HWP P host s F (vals (us ++ [.i32 addr, .i64 v]) ++
      expression (.intStore .i64 none ⟨0⟩ ⟨0, 0⟩ :: is)) Q := by
  obtain ⟨mi, hmi⟩ : ∃ mi, s.mems[0]? = some mi :=
    ⟨s.mems[0]'(by omega), List.getElem?_eq_getElem _⟩
  have hm := mem?_of hF hmi
  rcases hst : Memory.store mi.bytes (effAddr addr.toNat ⟨0, 0⟩)
    (count := IntType.i64.width / 8) (v.setWidth _) with _ | b
  · exact Wp.intStore_oob (m := .part) (a := .i32) (i := addr) (t := .i64) (c := v)
      hm (store_none_lt hst) htrap
  · exact Wp.intStore (m := .part) (a := .i32) (i := addr) (t := .i64) (c := v) hm hst
      (h mi b hmi hst)

end Rules

theorem setMem_mems {s : Store Nat} {mi : MemInst} (hl : s.mems.length = 1) :
    (s.setMem 0 mi).mems[0]? = some mi ∧ (s.setMem 0 mi).mems.length = 1 ∧
      (s.setMem 0 mi).funcs = s.funcs ∧ (s.setMem 0 mi).globals = s.globals := by
  simp [Store.setMem, hl]

@[simp] theorem setGlobal_mems (s : Store Nat) (a : Nat) (v : Val) :
    (s.setGlobal a v).mems = s.mems := rfl

theorem gval_setMem {s : Store Nat} {mi : MemInst} (a : Nat) :
    gval (s.setMem 0 mi) a = gval s a := rfl

private theorem load_grown {before after : MemInst} {pages addr count : Nat}
    {value : BitVec (8 * count)} (grown : before.grow? pages = some after)
    (loaded : Memory.load before.bytes addr count = some value) :
    Memory.load after.bytes addr count = some value := by
  have bound : addr + count ≤ before.bytes.size := by
    by_contra outside
    simp [Memory.load, Memory.readBytes, outside] at loaded
  simp only [MemInst.grow?] at grown
  split at grown
  · obtain rfl := Option.some.inj grown
    unfold Memory.load Memory.readBytes at loaded ⊢
    rw [ite_eq_left bound] at loaded
    let extension : ByteArray := ⟨Array.replicate (pages * Memory.pageSize) 0⟩
    have expanded : addr + count ≤ (before.bytes ++ extension).size := by
      simp only [ByteArray.size_append]
      omega
    have sameBytes : (before.bytes ++ extension).extract addr (addr + count) =
        before.bytes.extract addr (addr + count) := by
      apply ByteArray.ext
      refine Array.ext_getElem? fun index => ?_
      simp only [ByteArray.data_extract, ByteArray.data_append, Array.getElem?_extract,
        Array.size_append, ByteArray.size_data, Nat.min_eq_left bound,
        Nat.min_eq_left (by simpa only [ByteArray.size_append] using expanded)]
      split
      · rw [Array.getElem?_append_left (by simp only [ByteArray.size_data]; omega)]
      · rfl
    change (if addr + count ≤ (before.bytes ++ extension).size then
      some ((before.bytes ++ extension).extract addr (addr + count)) else none).map
        (fun bytes => BitVec.ofNat (8 * count) (Memory.decodeLE bytes)) = some value
    rw [ite_eq_left expanded, sameBytes]
    exact loaded
  · cases grown

theorem ringRep_grow {cap pages : Nat} {g : List (BitVec 64)} {s : Store Nat}
    {st cnt : BitVec 32} {before after : MemInst} (rep : RingRep cap g s st cnt)
    (mem : s.mems[0]? = some before) (grown : before.grow? pages = some after) :
    RingRep cap g (s.setMem 0 after) st cnt := by
  obtain ⟨first, num, start, len, capBound, memLen, width, words⟩ := rep
  obtain ⟨nextMem, nextLen, _, _⟩ := setMem_mems (mi := after) memLen
  refine ⟨(gval_setMem 0).trans first, (gval_setMem 1).trans num, start, len, capBound,
    nextLen, ?_, fun index inside => ⟨after, nextMem, ?_⟩⟩
  · intro mi found
    rw [nextMem] at found
    obtain rfl := Option.some.inj found
    simp only [MemInst.grow?] at grown
    split at grown
    · obtain rfl := Option.some.inj grown
      exact width before mem
    · cases grown
  · obtain ⟨_, lookup, read⟩ := words index inside
    rw [mem] at lookup
    cases lookup
    exact load_grown grown read

theorem reserve_hwp {P : Profile} {host : HostSemantics Nat} {cap : Nat}
    {g : List (BitVec 64)} {s : Store Nat} {st cnt : BitVec 32} {f : Frame}
    {memory : MemInst} {tail : List Instr} {Q : Post Nat}
    (rep : RingRep cap g s st cnt) (lookup : s.mems[0]? = some memory)
    (addr : f.module.mems = [0]) (width : memory.type.address = .i32)
    (resume : ∀ current, current.funcs = s.funcs → RingRep cap g current st cnt →
      HWP P host current f (vals [] ++ expression tail) Q)
    (traps : ∀ current, current.funcs = s.funcs → RingRep cap g current st cnt → Q current f .trap) :
    HWP P host s f (vals [] ++ expression (reserveBody cap ++ tail)) Q := by
  have mem := mem?_of addr lookup
  refine Wp.memorySize (m := .part) (us := []) (x := ⟨0⟩)
    (rest := expression (.intConst .i32 (capW (reservePages cap)) ::
      .intRelOp .i32 (.lt .unsigned) ::
      .if_ .empty [.intConst .i32 (capW (reservePages cap - 1)), .memoryGrow ⟨0⟩,
        .intConst .i32 (BitVec.allOnes 32), .intRelOp .i32 .eq,
        .if_ .empty [.unreachable] []] [] :: tail)) mem ?_
  have read : addrVal memory.type.address (BitVec.ofNat _ memory.pages) = .i32 (capW memory.pages) := by
    obtain ⟨⟨_, _⟩, _⟩ := memory
    cases width
    rfl
  rw [read]
  refine X.i32Const (us := [] ++ [.i32 (capW memory.pages)]) ?_
  refine X.rel32 (us := []) ?_
  refine X.if_ (us := []) (fun _ => ?_) (fun _ => resume s rfl rep)
  refine X.i32Const (us := []) ?_
  refine Wp.memoryGrow (m := .part) (a := .i32) (us := []) (x := ⟨0⟩)
    (rest := expression [.intConst .i32 (BitVec.allOnes 32), .intRelOp .i32 .eq,
      .if_ .empty [.unreachable] []]) mem ?_ ?_
  · intro grown grows _
    have rep' := ringRep_grow rep lookup grows
    have funcs := (setMem_mems (mi := grown) rep.2.2.2.2.2.1).2.2.1
    refine X.i32Const (us := [] ++ [.i32 (capW memory.pages)]) ?_
    refine X.rel32 (us := []) ?_
    refine X.if_ (us := []) (fun _ => ?_) (fun _ => ?_)
    · exact Wp.unreachable (m := .part) (traps _ funcs rep')
    · exact X.blockEnd (us := []) (is := tail) (resume _ funcs rep')
  · intro _
    refine X.i32Const (us := [] ++ [.i32 (BitVec.allOnes 32)]) ?_
    refine X.rel32 (us := []) ?_
    refine X.if_ (us := []) (fun _ => ?_) (fun impossible => ?_)
    · exact Wp.unreachable (m := .part) (traps s rfl rep)
    · exact False.elim ((by decide : bool32 true ≠ 0) impossible)

theorem Traps.loop {Q : Post Nat} {s : Store Nat} {Inv : Store Nat → Frame → List Val → Prop}
    (h : Traps Q s) : Traps (loopPost 0 [] Inv Q) s := fun f => ⟨(h f).1, (h f).2⟩

/-! ## Decoding -/

theorem rdec_feed {ts : List FnType} {e : (ifaceSig ts).Op} {v : (ifaceSig ts).Ar e}
    {x : BitVec 64} (he : e.1.val = 0) (hx : e.2.1 = [.i64 x]) (hv : ansVals v = some []) :
    parseDec ringPix e v = some (.feed [x]) := by
  simp [parseDec, ringPix, hv, he, hx, i64Val, Writers.i64Arg, Val.i64]

theorem rdec_finish {ts : List FnType} {e : (ifaceSig ts).Op} {v : (ifaceSig ts).Ar e}
    {u h : BitVec 32} (he : e.1.val = 1) (hv : ansVals v = some [.i32 u, .i32 h]) :
    parseDec ringPix e v = some (.finish u.toNat h) := by
  simp [parseDec, ringPix, hv, he, i32Two, Val.i32]

/-! ## Lists -/

theorem ofAtoms_drop_pred {g : List (BitVec 64)} {i : Nat} (hi : 0 < i) (hlen : i ≤ g.length) :
    SExp2.ofAtoms (g.drop (i - 1)) =
      .cons (.atom (g[i - 1]'(by omega))) (SExp2.ofAtoms (g.drop i)) := by
  rw [List.drop_eq_getElem_cons (by omega)]
  have : i - 1 + 1 = i := by omega
  rw [this]
  rfl

/-! ## The module -/

/-- The invariant of `finish`'s loop, from the store `s` and the frame's module `mi`: the store
is unchanged, `i ≤ n`, and `acc` denotes the list of the buffered values `i … n - 1`. -/
def RingLoop (ρ : Env (BitVec 32) (SExp2 (BitVec 64))) (g : List (BitVec 64)) (n : BitVec 32)
    (s₀ : Store Nat) (mi : ModuleInst) (s : Store Nat) (f : Frame) : Prop :=
  s = s₀ ∧ ∃ i acc : BitVec 32, f = ⟨[some (.i32 n), some (.i32 i), some (.i32 acc)], mi⟩ ∧
    i.toNat ≤ n.toNat ∧ ρ acc = some (SExp2.ofAtoms ((g.take n.toNat).drop i.toNat))

private theorem ringSat {I : ScalarInstance} {cap : Nat} {preludeCode : List Instr}
    (hcap : RingCap cap) (P : Profile) (ρ : Env (BitVec 32) (SExp2 (BitVec 64)))
    (ppol : PPolicy (BitVec 32)) (hS : MShape I twoFTs chunkFTs (ringFnsWith cap preludeCode) [0, 1])
    (mem4 : (I.store.funcs[4]?).map (·.module.mems) = some [0])
    (mem5 : (I.store.funcs[5]?).map (·.module.mems) = some [0])
    (prepare : ∀ {s : Store Nat} {g st cnt f Q}, RingRep cap g s st cnt → f.module.mems = [0] →
      (∀ current, current.funcs = s.funcs → RingRep cap g current st cnt →
        HWP P (gameHost I (WSpec I ρ Set.univ)) current f (vals [] ++ expression (ringWriteBody cap)) Q) →
      (∀ current, current.funcs = s.funcs → RingRep cap g current st cnt → Q current f .trap) →
      HWP P (gameHost I (WSpec I ρ Set.univ)) s f (vals [] ++ expression (preludeCode ++ ringWriteBody cap)) Q) :
    SGameSat P I (WSpec I ρ Set.univ) (chunkSSpec ringPix ppol ρ takeR (ringInvFor I cap)) := by
  refine sgameSat_ofM hS (fun g s h => h.1) (fun g g' s h h' => ringInv_uniq h h')
    (fun g e v hv => ⟨fun e' hd => by simp [parseDec, hv] at hd, by
      simp [chunkSSpec, chunkNext, parseDec, hv]⟩)
    fun j fi s args ht g Q hfi hm hmg hinv hT hret => ?_
  obtain ⟨hfs, st, cnt, hrep⟩ := hinv
  have hlen : I.exports.length = 2 := by rw [hS.exports]; rfl
  have hgj := hS.get j
  obtain ⟨j, hj⟩ := j
  have hj2 : j < 2 := hlen ▸ hj
  rcases j with _ | _ | j
  · -- `feed(x)`
    have hFm : fi.module.mems = [0] := by
      have h4 := mem4
      rw [show (twoFTs.length + 0) = 4 from rfl] at hfi
      rw [hfi] at h4
      exact Option.some.inj h4
    have ht' := ht
    rw [hgj] at ht'
    obtain ⟨x, rfl⟩ : ∃ x, args = [.i64 x] := by
      rcases ht' with _ | ⟨⟨x, rfl⟩, hnil⟩
      cases hnil
      exact ⟨x, rfl⟩
    show HWP P _ s ⟨[some (.i64 x)], fi.module⟩ (vals [] ++ expression (ringFeedWith cap preludeCode)) Q
    simp only [ringFeedWith, ringGuard, List.cons_append, List.nil_append]
    refine X.globalGet (us := []) (x := ⟨1⟩) (a := 1) (by rw [hmg]; rfl) hrep.2.1 ?_
    refine X.i32Const (us := [] ++ [.i32 cnt]) ?_
    refine X.rel32 (us := []) ?_
    refine X.if_ (us := []) (fun _ => ?_) (fun hc => ?_)
    · exact Wp.unreachable (m := .part) (hT s ⟨hfs, st, cnt, hrep⟩ _).1
    · have hc8 := rel_eq_z hc
      refine prepare hrep hFm (fun s eqFuncs rep => ?_)
        (fun current eqFuncs rep => (hT current ⟨eqFuncs.trans hfs, st, cnt, rep⟩ _).1)
      have hfsCurrent := eqFuncs.trans hfs
      clear hrep eqFuncs hfs
      have hinv : ringInvFor I cap g s := ⟨hfsCurrent, st, cnt, rep⟩
      obtain ⟨h0, h1, hst, hcg, hgc, hml, hwidth, hld⟩ := rep
      simp only [ringWriteBody, slotAddr, List.cons_append, List.nil_append]
      have hlt : cnt.toNat < cap := by
        have : cnt.toNat ≠ cap := fun h =>
          hc8 (BitVec.eq_of_toNat_eq (by rw [h, capW_toNat hcap.2]))
        omega
      have hn : ∀ v : Answer (I.exports.get ⟨0, hj⟩), v.toResult = .values [] →
          chunkNext (I := I) ringPix g ⟨⟨0, hj⟩, ⟨[.i64 x], ht⟩⟩ v = g ++ [x] := fun v hv => by
        simp [chunkNext, rdec_feed (ts := I.exports) (e := ⟨⟨0, hj⟩, ⟨[.i64 x], ht⟩⟩) rfl rfl
          (ansVals_of hv), chunkStep]
      have hpost : ∀ v : Answer (I.exports.get ⟨0, hj⟩), v.toResult = .values [] →
          (chunkSSpec (I := I) ringPix ppol ρ takeR (ringInvFor I cap)).post g
            ⟨⟨0, hj⟩, ⟨[.i64 x], ht⟩⟩ v := fun v hv e hd => by
        rw [rdec_feed rfl rfl (ansVals_of hv)] at hd
        cases hd
        intro ps w h ps' _ hR
        exact hR.elim
      refine X.globalGet (us := []) (x := ⟨0⟩) (a := 0) (by rw [hmg]; rfl) h0 ?_
      refine X.globalGet (us := [] ++ [.i32 st]) (f := ⟨[some (.i64 x)], fi.module⟩) (x := ⟨1⟩)
        (a := 1) (by rw [hmg]; rfl) h1 ?_
      refine X.add32 (us := []) ?_
      refine X.remuC (us := []) (capW_ne hcap) ?_
      refine X.mul8 (us := []) ?_
      refine X.localGet (x := ⟨0⟩) (v := .i64 x) rfl ?_
      refine X.store64R (us := []) hFm hml ((hT s hinv _).1) fun mi b hmi hstb => ?_
      obtain ⟨hmi', hml', hfs', hgl'⟩ := setMem_mems (mi := { mi with bytes := b }) hml
      let s₁ := s.setMem 0 { mi with bytes := b }
      refine X.globalGet (s := s₁) (f := ⟨[some (.i64 x)], fi.module⟩) (us := []) (x := ⟨1⟩)
        (a := 1) (v := .i32 cnt)
        (by rw [hmg]; rfl) (by rw [gval_setMem]; exact h1) ?_
      refine X.i32Const (us := [] ++ [.i32 cnt]) ?_
      refine X.add32 (us := []) ?_
      refine X.globalSet (s := s₁) (f := ⟨[some (.i64 x)], fi.module⟩) (us := []) (x := ⟨1⟩)
        (a := 1) (by rw [hmg]; rfl)
        (by rw [gval_setMem, h1]; rfl) ?_
      refine X.return_ (hret _ _ [] (by rw [hgj]; rfl) fun v hv => ⟨hpost v hv, ?_⟩)
      show ringInvFor I cap (chunkNext (I := I) ringPix g ⟨⟨0, hj⟩, ⟨[.i64 x], ht⟩⟩ v) _
      rw [hn v hv]
      have haddr := slot_addr hcap hst hlt
      rw [haddr] at hstb
      refine ⟨by rw [setGlobal_funcs, hfs', hfsCurrent], st, cnt + 1, ?_, ?_, hst, ?_, ?_, ?_, ?_, ?_⟩
      · rw [gval_setGlobal, gval_setMem]; simpa using h0
      · rw [gval_setGlobal, gval_setMem, h1]; rfl
      · rw [cnt_succ hcap hlt, hcg]; simp
      · simp only [List.length_append, List.length_singleton]
        omega
      · rw [setGlobal_mems]; exact hml'
      · intro memory found
        rw [setGlobal_mems, hmi'] at found
        obtain rfl := Option.some.inj found
        exact hwidth mi hmi
      · intro i hi
        refine ⟨{ mi with bytes := b }, by rw [setGlobal_mems]; exact hmi', ?_⟩
        simp only [List.length_append, List.length_singleton] at hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · obtain ⟨mi₀, hmi₀, hl₀⟩ := hld i hi
          rw [hmi] at hmi₀
          cases hmi₀
          rw [List.getElem_append_left hi]
          show Memory.load b _ 8 = _
          rw [Silmaril.Wasm.Logic.Core.load_store_disjoint hstb
            (slot_ne hlt (by omega) (by omega))]
          exact hl₀
        · rw [List.getElem_append_right (Nat.le_refl _)]
          simp only [Nat.sub_self, List.getElem_singleton]
          rw [← hcg]
          exact Silmaril.Wasm.Logic.Core.load_store_same hstb
  · -- `finish(n)`
    have hFm : fi.module.mems = [0] := by
      have h5 := mem5
      rw [show (twoFTs.length + 1) = 5 from rfl] at hfi
      rw [hfi] at h5
      exact Option.some.inj h5
    have ht' := ht
    rw [hgj] at ht'
    obtain ⟨n, rfl⟩ : ∃ n, args = [.i32 n] := by
      rcases ht' with _ | ⟨⟨n, rfl⟩, hnil⟩
      cases hnil
      exact ⟨n, rfl⟩
    have hinv : ringInvFor I cap g s := ⟨hfs, st, cnt, hrep⟩
    have hT₀ := hT s hinv
    obtain ⟨h0, h1, hst, hcg, hgc, hml, hwidth, hld⟩ := hrep
    -- the returns of `finish(n)`, by their answer
    have hpost : ∀ (u r : BitVec 32) (y : SExp2 (BitVec 64)), ρ r = some y →
        (u.toNat ≤ g.length → y = SExp2.ofAtoms (g.take u.toNat)) →
        ∀ v : Answer (I.exports.get ⟨1, hj⟩), v.toResult = .values [.i32 u, .i32 r] →
        (chunkSSpec (I := I) ringPix ppol ρ takeR (ringInvFor I cap)).post g
          ⟨⟨1, hj⟩, ⟨[.i32 n], ht⟩⟩ v := fun u r y hy hu v hv e hd => by
      rw [rdec_finish rfl (ansVals_of hv)] at hd
      cases hd
      intro ps w h ps' hps hR _ y' hy'
      obtain ⟨hl, rfl, rfl, -⟩ := hR
      rw [hy] at hy'
      cases hy'
      rw [hps] at hl ⊢
      exact hu hl
    have hnext : ∀ (u r : BitVec 32) (v : Answer (I.exports.get ⟨1, hj⟩)),
        v.toResult = .values [.i32 u, .i32 r] →
        chunkNext (I := I) ringPix g ⟨⟨1, hj⟩, ⟨[.i32 n], ht⟩⟩ v =
          chunkStep g (.finish u.toNat r) := fun u r v hv => by
      simp [chunkNext, rdec_finish (ts := I.exports) (e := ⟨⟨1, hj⟩, ⟨[.i32 n], ht⟩⟩) rfl
        (ansVals_of hv)]
    show HWP P _ s ⟨[some (.i32 n), some (.i32 0), some (.i32 0)], fi.module⟩
      (vals [] ++ expression (ringFinBody cap)) Q
    simp only [ringFinBody]
    refine X.localGet (x := ⟨0⟩) (v := .i32 n) rfl ?_
    refine X.globalGet (us := [] ++ [.i32 n])
      (f := ⟨[some (.i32 n), some (.i32 0), some (.i32 0)], fi.module⟩) (x := ⟨1⟩) (a := 1)
      (by rw [hmg]; rfl) h1 ?_
    refine X.rel32 (us := []) ?_
    refine X.if_ (us := []) (fun _ => ?_) (fun hc => ?_)
    · -- `n > count`: nothing is consumed
      refine X.i32Const (us := []) ?_
      refine X.wNilM (us := [.i32 0]) hS hfs hm (Traps.label hT₀) fun r hr => ?_
      refine X.return_ (hret _ _ [.i32 0, .i32 r] (by rw [hgj]; rfl) fun v hv =>
        ⟨hpost 0 r _ hr (fun _ => by simp [SExp2.ofAtoms, SExp2.ofList]) v hv, ?_⟩)
      show ringInvFor I cap (chunkNext (I := I) ringPix g ⟨⟨1, hj⟩, ⟨[.i32 n], ht⟩⟩ v) _
      rw [hnext 0 r v hv]
      simpa [chunkStep] using hinv
    · have hnc := rel_gtu_z hc
      refine X.localGet (x := ⟨0⟩) (v := .i32 n) rfl ?_
      refine X.eqz (us := []) ?_
      refine X.if_ (us := []) (fun _ => ?_) (fun hc₀ => ?_)
      · -- `n = 0`: nothing is consumed
        refine X.i32Const (us := []) ?_
        refine X.wNilM (us := [.i32 0]) hS hfs hm (Traps.label hT₀) fun r hr => ?_
        refine X.return_ (hret _ _ [.i32 0, .i32 r] (by rw [hgj]; rfl) fun v hv =>
          ⟨hpost 0 r _ hr (fun _ => by simp [SExp2.ofAtoms, SExp2.ofList]) v hv, ?_⟩)
        show ringInvFor I cap (chunkNext (I := I) ringPix g ⟨⟨1, hj⟩, ⟨[.i32 n], ht⟩⟩ v) _
        rw [hnext 0 r v hv]
        simpa [chunkStep] using hinv
      · -- `0 < n ≤ count`: the loop
        have hn0 := eqz_z hc₀
        have hng : n.toNat ≤ g.length := hcg ▸ hnc
        refine X.wNilM (us := []) hS hfs hm hT₀ fun r₀ hr₀ => ?_
        refine X.localSet (x := ⟨2⟩) (by exact (by decide : (2 : Nat) < 3)) ?_
        refine X.localGet (x := ⟨0⟩) (v := .i32 n) rfl ?_
        refine X.localSet (x := ⟨1⟩) (by exact (by decide : (1 : Nat) < 3)) ?_
        refine HWP.block (us := []) (vs := []) (bt := .empty) (t₁ := []) (t₂ := [])
          (rest := expression [.unreachable]) rfl rfl ?_
        have hTL : Traps (labelPost P (gameHost I (WSpec I ρ Set.univ)) 0 [] []
            (seqPost P (gameHost I (WSpec I ρ Set.univ)) (expression [.unreachable]) Q)) s :=
          Traps.label hT₀
        refine X.loop (Inv := RingLoop ρ g n s fi.module)
          (fun s' f hI => ?_) ⟨rfl, n, r₀, rfl, le_rfl, by
            rw [List.drop_of_length_le (by simp)]; simpa [SExp2.ofAtoms, SExp2.ofList] using hr₀⟩
        obtain ⟨rfl, i, acc, rfl, hin, hacc⟩ := hI
        have hTo := Traps.loop (Inv := fun s'' f vs => vs = [] ∧ RingLoop ρ g n s' fi.module s'' f)
          hTL
        simp only [ringLoopBody, slotAddr, List.cons_append, List.nil_append]
        refine X.localGet (x := ⟨1⟩) (v := .i32 i) rfl ?_
        refine X.eqz (us := []) ?_
        refine X.if_ (us := []) (fun hi0 => ?_) (fun hi0 => ?_)
        · -- `i = 0`: advance the start slot, drop `n` values, return
          have hi : i = 0 := by simpa using bool32_ne_zero hi0
          subst hi
          let F : Frame := ⟨[some (.i32 n), some (.i32 0), some (.i32 acc)], fi.module⟩
          obtain ⟨hst', hstl⟩ := st_next hcap hst (by omega : n.toNat ≤ cap)
          refine X.globalGet (f := F) (us := []) (x := ⟨0⟩) (a := 0) (by rw [hmg]; rfl) h0 ?_
          refine X.localGet (x := ⟨0⟩) (v := .i32 n) rfl ?_
          refine X.add32 (us := []) ?_
          refine X.remuC (us := []) (capW_ne hcap) ?_
          refine X.globalSet (s := s') (f := F) (us := []) (x := ⟨0⟩) (a := 0)
            (by rw [hmg]; rfl) (by simp [h0]) ?_
          let s₁ := s'.setGlobal 0 (.i32 ((st + n) % capW cap))
          refine X.globalGet (s := s₁) (f := F) (us := []) (x := ⟨1⟩) (a := 1) (v := .i32 cnt)
            (by rw [hmg]; rfl) (by simp [s₁, gval_setGlobal, h1]) ?_
          refine X.localGet (x := ⟨0⟩) (v := .i32 n) rfl ?_
          refine X.sub32 (us := []) ?_
          refine X.globalSet (s := s₁) (f := F) (us := []) (x := ⟨1⟩) (a := 1)
            (by rw [hmg]; rfl) (by simp [s₁, gval_setGlobal, h1]) ?_
          refine X.localGet (x := ⟨0⟩) (v := .i32 n) rfl ?_
          refine X.localGet (x := ⟨2⟩) (v := .i32 acc) rfl ?_
          refine X.return_ (hret _ _ [.i32 n, .i32 acc] (by rw [hgj]; rfl) fun v hv =>
            ⟨hpost n acc _ hacc (fun _ => by simp) v hv, ?_⟩)
          show ringInvFor I cap (chunkNext (I := I) ringPix g ⟨⟨1, hj⟩, ⟨[.i32 n], ht⟩⟩ v) _
          rw [hnext n acc v hv]
          simp only [chunkStep, hng, ↓reduceIte]
          refine ⟨by simp [s₁, hfs], (st + n) % capW cap, cnt - n, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp [s₁, gval_setGlobal, h0]
          · simp [s₁, gval_setGlobal, h1]
          · rw [hst']; exact hstl
          · rw [cnt_sub hnc, hcg]; simp
          · simp only [List.length_drop]; omega
          · simpa [s₁] using hml
          · simpa [s₁] using hwidth
          · intro k hk
            simp only [List.length_drop] at hk
            obtain ⟨mi, hmi, hl⟩ := hld (n.toNat + k) (by omega)
            refine ⟨mi, by simpa [s₁] using hmi, ?_⟩
            rw [hst', slot_shift, List.getElem_drop]
            exact hl
        · -- `i ≠ 0`: add the value `i - 1`
          have hi0' : i ≠ 0 := by simpa using bool32_eq_zero hi0
          obtain ⟨hip, hilt⟩ := i_pred hi0'
          have hipos : 0 < i.toNat := by omega
          have hig : i.toNat - 1 < g.length := by omega
          refine X.localGet (x := ⟨1⟩) (v := .i32 i) rfl ?_
          refine X.i32Const (us := [] ++ [.i32 i]) ?_
          refine X.add32 (us := []) ?_
          refine X.localSet (x := ⟨1⟩) (by exact (by decide : (1 : Nat) < 3)) ?_
          let i' := i + BitVec.allOnes 32
          let F : Frame := ⟨[some (.i32 n), some (.i32 i'), some (.i32 acc)], fi.module⟩
          refine X.globalGet (f := F) (us := []) (x := ⟨0⟩) (a := 0) (by rw [hmg]; rfl) h0 ?_
          refine X.localGet (x := ⟨1⟩) (v := .i32 i') rfl ?_
          refine X.add32 (us := []) ?_
          refine X.remuC (us := []) (capW_ne hcap) ?_
          refine X.mul8 (us := []) ?_
          refine X.load64 (F := F) (us := []) hFm hml ((hTo F).1) fun mi c hmi hc => ?_
          obtain ⟨mi₀, hmi₀, hl₀⟩ := hld (i.toNat - 1) hig
          rw [hmi] at hmi₀
          cases hmi₀
          have hi'cap : i'.toNat < cap := by
            simp only [i', hip]; omega
          rw [slot_addr hcap hst hi'cap] at hc
          simp only [i', hip] at hc
          rw [hl₀] at hc
          cases hc
          refine X.wWordM hS hfs hm hTo fun a ha => ?_
          refine X.localGet (x := ⟨2⟩) (v := .i32 acc) rfl ?_
          refine X.wConsM hS hfs hm ha hacc hTo fun c hc => ?_
          refine X.localSet (x := ⟨2⟩) (by exact (by decide : (2 : Nat) < 3)) ?_
          refine X.br0 ⟨[], [], rfl, rfl, rfl, rfl, i', c, rfl, by simp only [i', hip]; omega, ?_⟩
          rw [hc]
          simp only [i', hip]
          have hgt : i.toNat ≤ (g.take n.toNat).length := by simp; omega
          rw [ofAtoms_drop_pred hipos hgt, List.getElem_take]
  · omega

/-- The fixed-page ring meets the chunk specification. -/
theorem chunkRingN_sat {cap : Nat} (hcap : RingCap cap) (P : Profile)
    (ρ : Env (BitVec 32) (SExp2 (BitVec 64))) (ppol : PPolicy (BitVec 32)) :
    SGameSat P (RI cap) (WSpec (RI cap) ρ Set.univ)
      (chunkSSpec ringPix ppol ρ takeR (ringInv cap)) := by
  have sat := ringSat hcap P ρ ppol (ring_shape cap) (ring_mems4 cap) (ring_mems5 cap)
    (fun rep _ resume _ => resume _ rfl rep)
  have same : ringInvFor (RI cap) cap = ringInv cap := by rw [RI_eq]
  rwa [same] at sat

/-- The growing ring meets the same chunk specification, including on grow refusal. -/
theorem chunkRingGrowing_satI {cap : Nat} (hcap : RingCap cap) (P : Profile)
    (ρ : Env (BitVec 32) (SExp2 (BitVec 64))) (ppol : PPolicy (BitVec 32)) :
    SGameSat P (Verify.instOf (chunkRingGrowing cap))
      (WSpec (Verify.instOf (chunkRingGrowing cap)) ρ Set.univ)
      (chunkSSpec ringPix ppol ρ takeR (growingRingInv cap)) := by
  have sat := ringSat hcap P ρ ppol (growing_shape cap) (growing_mems4 cap) (growing_mems5 cap)
    (fun {s _ _ _ _ _} rep addr resume traps => by
      have length := rep.2.2.2.2.2.1
      obtain ⟨mi, mem⟩ : ∃ mi, s.mems[0]? = some mi :=
        ⟨s.mems[0]'(by omega), List.getElem?_eq_getElem _⟩
      exact reserve_hwp rep mem addr (rep.2.2.2.2.2.2.1 mi mem) resume traps)
  rwa [RIG_eq] at sat

/-- `chunkRingN_sat` at the instance itself. -/
theorem chunkRingN_satI {cap : Nat} (hcap : RingCap cap) (P : Profile)
    (ρ : Env (BitVec 32) (SExp2 (BitVec 64))) (ppol : PPolicy (BitVec 32)) :
    SGameSat P (Verify.instOf (chunkRingN cap))
      (WSpec (Verify.instOf (chunkRingN cap)) ρ Set.univ)
      (chunkSSpec ringPix ppol ρ takeR (ringInv cap)) := by
  have h := chunkRingN_sat hcap P ρ ppol
  rw [RI_eq] at h
  exact h

end Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.Ring
