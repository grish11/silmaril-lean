module

public import Silmaril.Proofs.Sim.X86Real.Common
public import Silmaril.Wasm.Logic.Memory.Thms

/-!
# Representation M: the five accessors of `simM` meet their contracts

Byte-level: the location→offset table at `256` and the flag→bit table at `280` (from `okM`),
the register slots of `user_regs_struct`, `eflags` at `144`. A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.X86Real

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.VC
open Silmaril.Wasm.Logic.Core (bytesAt leNat Region)

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Bytes -/

theorem bytesAt_one {B : ByteArray} {a : Nat} {b : UInt8} (h : B.data[a]? = some b) :
    bytesAt B ⟨a, 1⟩ = [b] := by
  have ha : a < B.data.size := by
    rcases Nat.lt_or_ge a B.data.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at h; cases h
  simp only [bytesAt]
  rw [List.take_one, List.head?_drop, Array.getElem?_toList, h]
  rfl

theorem load1 {B : ByteArray} {a : Nat} {b : UInt8} (h : B.data[a]? = some b) :
    Memory.load B a 1 = some (BitVec.ofNat 8 b.toNat) := by
  have ha : a < B.size := by
    rcases Nat.lt_or_ge a B.data.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at h; cases h
  rw [Silmaril.Wasm.Logic.Core.load_eq (by omega), bytesAt_one h]
  simp [leNat]

theorem load_ldM {B : ByteArray} {a n : Nat} (h : a + n ≤ B.size) :
    Memory.load B a n = some (ldM B a n) := by
  rw [Silmaril.Wasm.Logic.Core.load_eq h]; simp [ldM, Silmaril.Wasm.Logic.Core.load_eq h]

/-! ## The tables -/

theorem byteval {o : Nat} (h : o < 256) :
    (BitVec.setWidth 32 (BitVec.ofNat 8 (UInt8.ofNat o).toNat)).toNat = o := by
  simp [UInt8.toNat_ofNat]; omega

theorem offM_lt : ∀ i, i < 17 → offM.getD i 0 + 8 ≤ 160 := by decide
theorem offM_disj : ∀ i, i < 17 → ∀ j, j < 17 → i ≠ j →
    offM.getD i 0 + 8 ≤ offM.getD j 0 ∨ offM.getD j 0 + 8 ≤ offM.getD i 0 := by decide
theorem offM_flags : ∀ i, i < 17 → offM.getD i 0 + 8 ≤ 144 ∨ 148 ≤ offM.getD i 0 := by decide

theorem memM_some {mi : ModuleInst} {s : Store H} {a : Nat} {m : MemInst}
    (h : memM s mi = some (a, m)) : mi.mems[0]? = some a ∧ s.mems[a]? = some m := by
  unfold memM at h
  split at h
  · rename_i a' ha'
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨m', hm', rfl, rfl⟩ := h
    exact ⟨ha', hm'⟩
  · cases h

theorem absM_reg {mi : ModuleInst} {s : Store H} {a : Nat} {m : MemInst}
    (h : memM s mi = some (a, m)) {l : Nat} (hl : l < 17) : absM mi s l = ldM m.bytes (offM.getD l 0) 8 := by
  simp [absM, h, hl]

/-! ## `$rget` -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rgetM_total {mi : ModuleInst} {fi : FuncInst H} {a : Nat}
    {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)}
    (hcode : fi.code = .wasm (fn simM 0)) (hmod : fi.module = mi)
    (he : Silmaril.Wasm.Validation.Expand fi.type (.func ps rs)) (hps : ps.length = 1)
    (hrs : rs.length = 1) :
    Silmaril.Wasm.Logic.Hoare.TFSpecAt P host a (rgetSpec (repM mi) fi a) := by
  refine tfspec_of_wpc VCSpecs.tvalid_empty (by simp [fn, simM, loops, ctl]) (fun _ _ h => h.1)
    hcode he (fun _ _ h => by obtain ⟨-, -, l, rfl, -⟩ := h; simp [hps]) ?_
  rintro s _ ⟨-, ⟨ma, m, hmm, hsz, htab, -⟩, l, rfl, hl⟩
  subst hmod
  obtain ⟨h0, hma⟩ := memM_some hmm
  have habs : absM fi.module s l.toNat = ldM m.bytes (offM.getD l.toNat 0) 8 := absM_reg hmm hl
  have hoff : offM.getD l.toNat 0 + 8 ≤ 160 := offM_lt _ hl
  have hb : m.bytes.data[l.toNat + 256]? = some (UInt8.ofNat (offM.getD l.toNat 0)) := by
    rw [Nat.add_comm]; exact htab l.toNat hl
  simp only [Func.body, fn, simM, Fin.isValue, Nat.reducePow, List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.ofNat_pos, getElem?_pos, List.getElem_cons_zero, Fin.zero_eta, Option.getD_some, hrs, rgetSpec,
    repM, Val.i32, Val.i64, List.cons.injEq, Val.num.injEq, numI32_inj, and_true, forall_eq', habs,
    List.getD_eq_getElem?_getD, Frame.forCall, List.map_cons, List.map_nil, Func.locals, List.append_nil, wpc, ctl,
    Wasm.Logic.Core.exec1, List.reverse_nil, Wasm.Logic.Core.localVal?, Frame.local?, Idx.toNat, Fin.coe_ofNat_eq_mod,
    Nat.zero_mod, zero_lt_one, Option.map_some, List.reverse_cons, List.nil_append, Wasm.Logic.Core.popInt,
    IntType.width, Store.mem?, h0, Option.pure_def, Option.bind_eq_bind, Option.bind_some, hma, PackSize.width,
    Nat.reduceDiv, Nat.reduceMul, effAddr, Nat.reduceMod, load1 hb, UInt8.toNat_ofNat', Nat.reduceLeDiff,
    BitVec.setWidth_eq, add_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat, dvd_refl, Nat.mod_mod_of_dvd, fnPost,
    List.length_reverse, Wasm.Logic.Core.Outcome.normal.injEq, List.reverse_eq_cons_iff]
  have e : offM.getD l.toNat 0 = offM[l.toNat]?.getD 0 := by simp
  have hld : Memory.load m.bytes (offM[l.toNat]?.getD 0) 8 =
      some (ldM m.bytes (offM[l.toNat]?.getD 0) 8) := load_ldM (by omega)
  rw [show offM[l.toNat]?.getD 0 % 256 % 4294967296 = offM[l.toNat]?.getD 0 by omega, hld]
  simp


/-! ## Writing the register block -/

theorem bytesAt_one' (B : ByteArray) (i : Nat) : bytesAt B ⟨i, 1⟩ = (B.data[i]?).toList := by
  simp only [bytesAt]
  rw [List.take_one, List.head?_drop, Array.getElem?_toList]

theorem data_store_disjoint {B B' : ByteArray} {o n : Nat} {w : BitVec (8 * n)}
    (h : Memory.store B o w = some B') {i : Nat} (hi : o + n ≤ i ∨ i + 1 ≤ o) :
    B'.data[i]? = B.data[i]? := by
  have := Silmaril.Wasm.Logic.Core.bytesAt_store_disjoint (r := ⟨i, 1⟩) h
    (by simp only [Region.Disjoint, Region.stop]; omega)
  rw [bytesAt_one', bytesAt_one'] at this
  cases h1 : B'.data[i]? <;> cases h2 : B.data[i]? <;> simp_all

theorem memM_setMem {mi : ModuleInst} {s : Store H} {a : Nat} {m : MemInst}
    (h : memM s mi = some (a, m)) (m' : MemInst) : memM (s.setMem a m') mi = some (a, m') := by
  obtain ⟨h0, h1⟩ := memM_some h
  have ha : a < s.mems.length := lt_of_getElem?_some h1
  simp [memM, h0, Store.setMem, List.getElem?_set, ha]

/-- A store into the register block `[0, 216)` keeps the M invariant and is an M frame step. -/
theorem storeM {mi : ModuleInst} {s : Store H} (hok : okM mi s) {a : Nat} {m : MemInst}
    (hmm : memM s mi = some (a, m)) {o n : Nat} {w : BitVec (8 * n)} {B' : ByteArray}
    (hst : Memory.store m.bytes o w = some B') (hreg : o + n ≤ 216) :
    memM (s.setMem a { m with bytes := B' }) mi = some (a, { m with bytes := B' }) ∧
      okM mi (s.setMem a { m with bytes := B' }) ∧ keepM mi s (s.setMem a { m with bytes := B' }) := by
  obtain ⟨a₀, m₀, hm₀, hsz, ht1, ht2⟩ := hok
  rw [hmm] at hm₀; cases hm₀
  have hs := Silmaril.Wasm.Logic.Core.size_store hst
  refine ⟨memM_setMem hmm _, ⟨a, _, memM_setMem hmm _, by simp [hs, hsz], fun k hk => ?_,
    fun j hj => ?_⟩, ⟨a, m, _, hmm, rfl, rfl, by simp [hs], fun i hi => ?_⟩⟩
  · simp only; rw [data_store_disjoint hst (by omega)]; exact ht1 k hk
  · simp only; rw [data_store_disjoint hst (by omega)]; exact ht2 j hj
  · simp only; exact data_store_disjoint hst (by omega)

theorem ldM_store_same {B B' : ByteArray} {o : Nat} {w : BitVec (8 * 8)}
    (h : Memory.store B o w = some B') : ldM B' o 8 = w := by
  simp [ldM, Silmaril.Wasm.Logic.Core.load_store_same h]

theorem ldM_store_disjoint {B B' : ByteArray} {o n p q : Nat} {w : BitVec (8 * n)}
    (h : Memory.store B o w = some B') (hd : o + n ≤ p ∨ p + q ≤ o) : ldM B' p q = ldM B p q := by
  simp only [ldM, Silmaril.Wasm.Logic.Core.load_store_disjoint h
    (by simp only [Region.Disjoint, Region.stop]; omega : Region.Disjoint ⟨o, n⟩ ⟨p, q⟩)]

/-- A 64-bit store at register `k`'s slot: the M read-back is `updL … k w`. -/
theorem absM_store_reg {mi : ModuleInst} {s : Store H} {a : Nat} {m : MemInst}
    (hmm : memM s mi = some (a, m)) {k : Nat} (hk : k < 17) {w : BitVec 64} {B' : ByteArray}
    (hst : Memory.store m.bytes (offM.getD k 0) (count := 8) w = some B') :
    absM mi (s.setMem a { m with bytes := B' }) = updL (absM mi s) k w := by
  funext j
  have h' := memM_setMem hmm { m with bytes := B' }
  simp only [absM, h', hmm, updL]
  by_cases hj : j = k
  · subst hj; simp only [hk, ite_true]; exact ldM_store_same hst
  · simp only [hj, ite_false]
    by_cases hj17 : j < 17
    · simp only [hj17, ite_true]
      exact ldM_store_disjoint hst (by have := offM_disj k hk j hj17 (Ne.symm hj); omega)
    · simp only [hj17, ite_false]
      rw [ldM_store_disjoint hst (by have := offM_flags k hk; omega)]

/-! ## `$rset` -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rsetM_total {mi : ModuleInst} {fi : FuncInst H} {a : Nat}
    {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)}
    (hcode : fi.code = .wasm (fn simM 1)) (hmod : fi.module = mi)
    (he : Silmaril.Wasm.Validation.Expand fi.type (.func ps rs)) (hps : ps.length = 2)
    (hrs : rs.length = 0) :
    Silmaril.Wasm.Logic.Hoare.TFSpecAt P host a (rsetSpec (repM mi) fi a) := by
  refine tfspec_of_wpc VCSpecs.tvalid_empty (by simp [fn, simM, loops, ctl]) (fun _ _ h => h.1)
    hcode he (fun _ _ h => by obtain ⟨-, -, l, v, rfl, -⟩ := h; simp [hps]) ?_
  rintro s _ ⟨-, hok, l, v, rfl, hl⟩
  subst hmod
  obtain ⟨ma, m, hmm, hsz, htab, -⟩ := id hok
  obtain ⟨h0, hma⟩ := memM_some hmm
  have hoff : offM.getD l.toNat 0 + 8 ≤ 160 := offM_lt _ hl
  have hb : m.bytes.data[l.toNat + 256]? = some (UInt8.ofNat (offM.getD l.toNat 0)) := by
    rw [Nat.add_comm]; exact htab l.toNat hl
  have e : offM.getD l.toNat 0 = offM[l.toNat]?.getD 0 := by simp
  obtain ⟨B', hst⟩ : ∃ B', Memory.store m.bytes (offM[l.toNat]?.getD 0) (count := 8) v = some B' :=
    ⟨_, Silmaril.Wasm.Logic.Core.store_eq (B := m.bytes) (a := offM[l.toNat]?.getD 0) (n := 8) v
      (by omega)⟩
  obtain ⟨-, h2, h3⟩ := storeM hok hmm hst (by omega)
  have h4 : absM fi.module (s.setMem ma { m with bytes := B' }) = updL (absM fi.module s) l.toNat v :=
    absM_store_reg hmm hl (by rw [e]; exact hst)
  simp only [Func.body, fn, simM, Fin.isValue, Nat.reducePow, List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.one_lt_ofNat, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero, Fin.zero_eta,
    Option.getD_some, hrs, rsetSpec, repM, Val.i32, Val.i64, exists_and_right, List.cons.injEq, Val.num.injEq,
    numI32_inj, numI64_inj, and_true, and_imp, forall_apply_eq_imp_iff, forall_eq', Frame.forCall, List.map_cons,
    List.map_nil, Func.locals, List.append_nil, wpc, ctl, Wasm.Logic.Core.exec1, List.reverse_nil,
    Wasm.Logic.Core.localVal?, Frame.local?, Idx.toNat, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.ofNat_pos,
    Option.map_some, List.reverse_cons, List.nil_append, Wasm.Logic.Core.popInt, IntType.width, Store.mem?, h0,
    Option.pure_def, Option.bind_eq_bind, Option.bind_some, hma, PackSize.width, Nat.reduceDiv, Nat.reduceMul, effAddr,
    Nat.reduceMod, load1 hb, List.getD_eq_getElem?_getD, UInt8.toNat_ofNat', Nat.reduceLeDiff, Nat.one_mod,
    List.cons_append, add_zero, BitVec.setWidth_eq, BitVec.toNat_setWidth, BitVec.toNat_ofNat, dvd_refl,
    Nat.mod_mod_of_dvd, fnPost, List.length_reverse, List.length_eq_zero_iff, Wasm.Logic.Core.Outcome.normal.injEq,
    List.reverse_eq_nil_iff, and_self_left]
  rw [show offM[l.toNat]?.getD 0 % 256 % 4294967296 = offM[l.toNat]?.getD 0 by omega, hst]
  exact ⟨rfl, h2, h4, h3⟩


/-! ## Flags -/

theorem bitM_lt : ∀ j, j < 7 → bitM.getD j 0 < 12 := by decide

theorem shr_and1 (E : BitVec 32) {b : Nat} (hb : b < 32) :
    (E >>> (b % 32) &&& 1#32) = (if E.getLsbD b then 1#64 else 0#64).setWidth 32 := by
  rw [Nat.mod_eq_of_lt hb]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h0 : i = 0
  · subst h0; by_cases h : E[b] = true <;> simp [h, hb]
  · have hg : E.getLsbD b = E[b] := BitVec.getLsbD_eq_getElem hb
    by_cases h : E[b] = true <;> simp [h, hg, h0, BitVec.getLsbD_one, hi]

theorem absM_flag {mi : ModuleInst} {s : Store H} {a : Nat} {m : MemInst}
    (h : memM s mi = some (a, m)) {l : Nat} (h1 : 17 ≤ l) (h2 : l < 24) :
    absM mi s l = if (ldM m.bytes 144 4).getLsbD (bitM.getD (l - 17) 0) then 1#64 else 0#64 := by
  have : ¬ l < 17 := by omega
  simp [absM, h, this, h2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fgetM_total {mi : ModuleInst} {fi : FuncInst H} {a : Nat}
    {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)}
    (hcode : fi.code = .wasm (fn simM 2)) (hmod : fi.module = mi)
    (he : Silmaril.Wasm.Validation.Expand fi.type (.func ps rs)) (hps : ps.length = 1)
    (hrs : rs.length = 1) :
    Silmaril.Wasm.Logic.Hoare.TFSpecAt P host a (fgetSpec (repM mi) fi a) := by
  refine tfspec_of_wpc VCSpecs.tvalid_empty (by simp [fn, simM, loops, ctl]) (fun _ _ h => h.1)
    hcode he (fun _ _ h => by obtain ⟨-, -, l, rfl, -⟩ := h; simp [hps]) ?_
  rintro s _ ⟨-, ⟨ma, m, hmm, hsz, -, htab⟩, l, rfl, hl1, hl2⟩
  subst hmod
  clear hcode he
  obtain ⟨h0, hma⟩ := memM_some hmm
  have hb := htab (l.toNat - 17) (by omega)
  rw [show 280 + (l.toNat - 17) = l.toNat + 263 by omega] at hb
  have hbit := bitM_lt (l.toNat - 17) (by omega)
  have hld := load_ldM (B := m.bytes) (a := 144) (n := 4) (by omega)
  have habs := absM_flag hmm hl1 hl2
  have e : bitM.getD (l.toNat - 17) 0 = bitM[l.toNat - 17]?.getD 0 := by simp
  rw [e] at hbit habs
  simp [fn, simM, wpc, ctl, Silmaril.Wasm.Logic.Core.exec1, Frame.forCall, fnPost, hrs,
    Silmaril.Wasm.Logic.Core.localVal?, Silmaril.Wasm.Logic.Core.popInt, Frame.local?, Idx.toNat,
    Val.i32, Val.i64, Store.mem?, h0, hma, fgetSpec, repM, Silmaril.Wasm.Execution.Core.effAddr,
    load1 hb, PackSize.width, IntType.width, byteval (show bitM.getD (l.toNat - 17) 0 < 256 by omega),
    hld, habs]
  exact shr_and1 _ (by omega)


theorem bitM_inj : ∀ i, i < 7 → ∀ j, j < 7 → bitM.getD i 0 = bitM.getD j 0 → i = j := by decide

theorem allones32 : ∀ i : Fin 32, (4294967295#32)[i.val] = true := by decide

theorem setbit (E v : BitVec 32) {b c : Nat} (hb : b < 32) (hc : c < 32) :
    (E &&& (1#32 <<< (b % 32) ^^^ 4294967295#32) ||| (v &&& 1#32) <<< (b % 32)).getLsbD c =
      if c = b then v.getLsbD 0 else E.getLsbD c := by
  rw [Nat.mod_eq_of_lt hb]
  by_cases h : c = b
  · subst h
    have := allones32 ⟨c, hc⟩
    simp at this
    simp [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, hc, this]
  · have := allones32 ⟨c, hc⟩
    simp at this
    simp [h, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, hc, this]
    have h1 : (decide (c < b) || !decide (c - b = 0)) = true := by
      rcases Nat.lt_or_ge c b with h' | h' <;> simp [h'] <;> omega
    have h2 : (!decide (c < b) && decide (c - b = 0)) = false := by
      rcases Nat.lt_or_ge c b with h' | h' <;> simp [h'] <;> omega
    rw [h1, Bool.and_true]
    cases E[c] <;> simp_all

/-- A 32-bit store of `eflags`: registers unchanged, flags read from the new word. -/
theorem absM_store_eflags {mi : ModuleInst} {s : Store H} {a : Nat} {m : MemInst}
    (hmm : memM s mi = some (a, m)) {E' : BitVec 32} {B' : ByteArray}
    (hst : Memory.store m.bytes 144 (count := 4) E' = some B') (j : Nat) :
    absM mi (s.setMem a { m with bytes := B' }) j =
      if 17 ≤ j ∧ j < 24 then (if E'.getLsbD (bitM.getD (j - 17) 0) then 1#64 else 0#64)
      else absM mi s j := by
  have h' := memM_setMem hmm { m with bytes := B' }
  have hE : ldM B' 144 4 = E' := by simp [ldM, Silmaril.Wasm.Logic.Core.load_store_same hst]
  simp only [absM, h', hmm]
  by_cases hj : j < 17
  · have : ¬ (17 ≤ j ∧ j < 24) := by omega
    simp only [hj, ite_true, this, ite_false]
    exact ldM_store_disjoint hst (by have := offM_flags j hj; omega)
  · by_cases hj2 : j < 24
    · simp [hj, hj2, hE, show 17 ≤ j by omega]
    · simp [hj, hj2]

theorem setFlag_same {E v : BitVec 32} (hv : v.toNat < 2) {b : Nat} (hb : b < 32) :
    (if (E &&& (1#32 <<< (b % 32) ^^^ 4294967295#32) ||| (v &&& 1#32) <<< (b % 32)).getLsbD b
      then 1#64 else 0#64) = v.setWidth 64 := by
  rw [setbit _ _ hb hb]
  simp only [ite_true]
  have hv01 : v = 0#32 ∨ v = 1#32 := by
    rcases Nat.lt_or_ge v.toNat 1 with h | h
    · left; apply BitVec.eq_of_toNat_eq; simp; omega
    · right; apply BitVec.eq_of_toNat_eq; simp; omega
  rcases hv01 with rfl | rfl <;> simp

theorem setFlag_other {E v : BitVec 32} {b c : Nat} (hb : b < 32) (hc : c < 32) (hne : c ≠ b) :
    (E &&& (1#32 <<< (b % 32) ^^^ 4294967295#32) ||| (v &&& 1#32) <<< (b % 32)).getLsbD c =
      E.getLsbD c := by
  simp only [setbit _ _ hb hc, hne, ite_false]

/-- A 32-bit store of `eflags` with flag `l` set to `v`: the M read-back is `updL … l v`. -/
theorem absM_setFlag {mi : ModuleInst} {s : Store H} {a : Nat} {m : MemInst}
    (hmm : memM s mi = some (a, m)) {l : Nat} (hl1 : 17 ≤ l) (hl2 : l < 24) {v : BitVec 32}
    (hv : v.toNat < 2) {B' : ByteArray}
    (hst : Memory.store m.bytes 144 (count := 4) (ldM m.bytes 144 4 &&&
      (1#32 <<< (bitM.getD (l - 17) 0 % 32) ^^^ 4294967295#32) |||
      (v &&& 1#32) <<< (bitM.getD (l - 17) 0 % 32)) = some B') :
    absM mi (s.setMem a { m with bytes := B' }) = updL (absM mi s) l (v.setWidth 64) := by
  have hb : bitM.getD (l - 17) 0 < 12 := bitM_lt (l - 17) (by omega)
  funext j
  rw [absM_store_eflags hmm hst j]
  unfold updL
  by_cases hj : j = l
  · subst hj
    simp only [show 17 ≤ j ∧ j < 24 from ⟨hl1, hl2⟩, ite_true]
    exact setFlag_same hv (by omega)
  · show (if 17 ≤ j ∧ j < 24 then _ else absM mi s j) = if j = l then v.setWidth 64 else absM mi s j
    simp only [hj, ite_false]
    by_cases hf : 17 ≤ j ∧ j < 24
    · have hne : bitM.getD (j - 17) 0 ≠ bitM.getD (l - 17) 0 :=
        fun h => hj (by have := bitM_inj _ (by omega) _ (by omega) h; omega)
      simp only [hf, and_self, ite_true]
      rw [setFlag_other (by omega) (by have := bitM_lt (j - 17) (by omega); omega) hne,
        absM_flag hmm hf.1 hf.2]
    · simp only [hf, ite_false]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fsetM_total {mi : ModuleInst} {fi : FuncInst H} {a : Nat}
    {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)}
    (hcode : fi.code = .wasm (fn simM 3)) (hmod : fi.module = mi)
    (he : Silmaril.Wasm.Validation.Expand fi.type (.func ps rs)) (hps : ps.length = 2)
    (hrs : rs.length = 0) :
    Silmaril.Wasm.Logic.Hoare.TFSpecAt P host a (fsetSpec (repM mi) fi a) := by
  refine tfspec_of_wpc VCSpecs.tvalid_empty (by simp [fn, simM, loops, ctl]) (fun _ _ h => h.1)
    hcode he (fun _ _ h => by obtain ⟨-, -, l, v, rfl, -⟩ := h; simp [hps]) ?_
  rintro s _ ⟨-, hok, l, v, rfl, hl1, hl2, hv⟩
  subst hmod
  obtain ⟨ma, m, hmm, hsz, -, htab⟩ := id hok
  obtain ⟨h0, hma⟩ := memM_some hmm
  have hb : m.bytes.data[l.toNat + 263]? = some (UInt8.ofNat (bitM.getD (l.toNat - 17) 0)) := by
    rw [show l.toNat + 263 = 280 + (l.toNat - 17) by omega]; exact htab (l.toNat - 17) (by omega)
  have e : bitM.getD (l.toNat - 17) 0 = bitM[l.toNat - 17]?.getD 0 := by simp
  have hbit : bitM[l.toNat - 17]?.getD 0 < 12 := by
    rw [← e]; exact bitM_lt (l.toNat - 17) (by omega)
  have hld : Memory.load m.bytes 144 4 = some (ldM m.bytes 144 4) := load_ldM (by omega)
  obtain ⟨B', hst⟩ : ∃ B', Memory.store m.bytes 144 (count := 4) (ldM m.bytes 144 4 &&&
      (1#32 <<< (bitM[l.toNat - 17]?.getD 0 % 32) ^^^ 4294967295#32) |||
      (v &&& 1#32) <<< (bitM[l.toNat - 17]?.getD 0 % 32)) = some B' :=
    ⟨_, Silmaril.Wasm.Logic.Core.store_eq (B := m.bytes) (a := 144) (n := 4) _ (by omega)⟩
  obtain ⟨-, h2, h3⟩ := storeM hok hmm hst (by omega)
  have habs : absM fi.module (s.setMem ma { m with bytes := B' }) =
      updL (absM fi.module s) l.toNat (v.setWidth 64) :=
    absM_setFlag hmm hl1 hl2 hv (by rw [e]; exact hst)
  simp only [Func.body, fn, simM, Fin.isValue, Nat.reducePow, List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero, Fin.zero_eta,
    Option.getD_some, hrs, fsetSpec, repM, Val.i32, List.cons.injEq, Val.num.injEq, numI32_inj, and_true, and_imp,
    forall_apply_eq_imp_iff, forall_eq', Frame.forCall, List.map_cons, List.map_nil, Func.locals, List.cons_append,
    List.nil_append, wpc, ctl, Wasm.Logic.Core.exec1, List.reverse_nil, Wasm.Logic.Core.localVal?, Frame.local?,
    Idx.toNat, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.ofNat_pos, Option.map_some, List.reverse_cons,
    Wasm.Logic.Core.popInt, IntType.width, Store.mem?, h0, Option.pure_def, Option.bind_eq_bind, Option.bind_some, hma,
    PackSize.width, Nat.reduceDiv, Nat.reduceMul, effAddr, Nat.reduceMod, load1 hb, List.getD_eq_getElem?_getD,
    UInt8.toNat_ofNat', Nat.reduceLeDiff, Wasm.Logic.Core.popV, Nat.lt_add_one, ↓reduceIte, Frame.setLocal,
    List.set_cons_succ, List.set_cons_zero, BitVec.setWidth_eq, BitVec.toNat_ofNat, hld,
    Wasm.Logic.Core.intBinOp_i32_shl, BitVec.toNat_setWidth, dvd_refl, Nat.mod_mod_of_dvd, Nat.reduceDvd,
    Wasm.Logic.Core.intBinOp_i32_xor, Wasm.Logic.Core.intBinOp_i32_and, Nat.one_mod, Nat.one_lt_ofNat,
    Wasm.Logic.Core.intBinOp_i32_or, fnPost, List.length_reverse, List.length_eq_zero_iff,
    Wasm.Logic.Core.Outcome.normal.injEq, List.reverse_eq_nil_iff, and_self_left]
  rw [hst]
  exact ⟨rfl, h2, habs, h3⟩



theorem small_bit {x : BitVec 32} (hx : x.toNat < 2) {k : Nat} (hk : 1 ≤ k) (hk' : k < 32) :
    x[k] = false := by
  have h2 : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
  have : x.getLsbD k = false := by
    rw [BitVec.getLsbD]; exact Nat.testBit_lt_two_pow (by omega)
  rwa [BitVec.getLsbD_eq_getElem hk'] at this

theorem bit0_val {x : BitVec 32} (hx : x.toNat < 2) :
    (if x[0] = true then 1#64 else 0#64) = x.setWidth 64 := by
  have : x = 0#32 ∨ x = 1#32 := by
    rcases Nat.lt_or_ge x.toNat 1 with h | h
    · left; apply BitVec.eq_of_toNat_eq; simp; omega
    · right; apply BitVec.eq_of_toNat_eq; simp; omega
  rcases this with rfl | rfl <;> simp

/-- A 32-bit store of `eflags` with the six status flags: the M read-back is `upd6`. -/
theorem absM_set6 {mi : ModuleInst} {s : Store H} {a : Nat} {m : MemInst}
    (hmm : memM s mi = some (a, m)) {c p a' z sf o : BitVec 32} (hc : c.toNat < 2)
    (hp : p.toNat < 2) (ha : a'.toNat < 2) (hz : z.toNat < 2) (hs : sf.toNat < 2)
    (ho : o.toNat < 2) {B' : ByteArray}
    (hst : Memory.store m.bytes 144 (count := 4) (ldM m.bytes 144 4 &&& 4294965034#32 |||
      (c ||| p <<< 2 ||| (a' <<< 4 ||| z <<< 6) ||| (sf <<< 7 ||| o <<< 11))) = some B') :
    absM mi (s.setMem a { m with bytes := B' }) = upd6 (absM mi s) c p a' z sf o := by
  have bc : ∀ k, 1 ≤ k → (hk' : k < 32) → c[k] = false := fun k hk hk' => small_bit hc hk hk'
  have bp : ∀ k, 1 ≤ k → (hk' : k < 32) → p[k] = false := fun k hk hk' => small_bit hp hk hk'
  have ba : ∀ k, 1 ≤ k → (hk' : k < 32) → a'[k] = false := fun k hk hk' => small_bit ha hk hk'
  have bz : ∀ k, 1 ≤ k → (hk' : k < 32) → z[k] = false := fun k hk hk' => small_bit hz hk hk'
  have bs : ∀ k, 1 ≤ k → (hk' : k < 32) → sf[k] = false := fun k hk hk' => small_bit hs hk hk'
  have bo : ∀ k, 1 ≤ k → (hk' : k < 32) → o[k] = false := fun k hk hk' => small_bit ho hk hk'
  funext j
  rw [absM_store_eflags hmm hst j]
  by_cases hf : 17 ≤ j ∧ j < 24
  · show (if 17 ≤ j ∧ j < 24 then _ else absM mi s j) = upd6 (absM mi s) c p a' z sf o j
    simp only [hf, and_self, ite_true]
    rcases (show j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp (config := { decide := true }) [upd6, updL, bitM, BitVec.getLsbD_or, BitVec.getLsbD_and,
        BitVec.getLsbD_shiftLeft, bc, bp, ba, bz, bs, bo, bit0_val hc, bit0_val hp, bit0_val ha,
        bit0_val hz, bit0_val hs, bit0_val ho]
    rw [absM_flag hmm (by decide) (by decide)]
    simp [bitM]
  · simp only [hf, ite_false]
    have hj : j ≠ 17 ∧ j ≠ 18 ∧ j ≠ 19 ∧ j ≠ 20 ∧ j ≠ 21 ∧ j ≠ 22 := by omega
    simp [upd6, updL, hj]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fset6M_total {mi : ModuleInst} {fi : FuncInst H} {a : Nat}
    {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)}
    (hcode : fi.code = .wasm (fn simM 4)) (hmod : fi.module = mi)
    (he : Silmaril.Wasm.Validation.Expand fi.type (.func ps rs)) (hps : ps.length = 6)
    (hrs : rs.length = 0) :
    Silmaril.Wasm.Logic.Hoare.TFSpecAt P host a (fset6Spec (repM mi) fi a) := by
  refine tfspec_of_wpc VCSpecs.tvalid_empty (by simp [fn, simM, loops, ctl]) (fun _ _ h => h.1)
    hcode he (fun _ _ h => by obtain ⟨-, -, c, p, a', z, sf, o, rfl, -⟩ := h; simp [hps]) ?_
  rintro s _ ⟨-, hok, c, p, a', z, sf, o, rfl, hc, hp, ha, hz, hs, ho⟩
  subst hmod
  obtain ⟨ma, m, hmm, hsz, -, -⟩ := id hok
  obtain ⟨h0, hma⟩ := memM_some hmm
  have hld : Memory.load m.bytes 144 4 = some (ldM m.bytes 144 4) := load_ldM (by omega)
  obtain ⟨B', hst⟩ : ∃ B', Memory.store m.bytes 144 (count := 4) (ldM m.bytes 144 4 &&& 4294965034#32 |||
      (c ||| p <<< 2 ||| (a' <<< 4 ||| z <<< 6) ||| (sf <<< 7 ||| o <<< 11))) = some B' :=
    ⟨_, Silmaril.Wasm.Logic.Core.store_eq (B := m.bytes) (a := 144) (n := 4) _ (by omega)⟩
  obtain ⟨-, h2, h3⟩ := storeM hok hmm hst (by omega)
  have habs : absM fi.module (s.setMem ma { m with bytes := B' }) =
      upd6 (absM fi.module s) c p a' z sf o := absM_set6 hmm hc hp ha hz hs ho hst
  simp only [Func.body, fn, simM, Fin.isValue, Nat.reducePow, List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.reduceLT, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero, Fin.zero_eta,
    Option.getD_some, hrs, fset6Spec, repM, Val.i32, List.cons.injEq, Val.num.injEq, numI32_inj, and_true, and_imp,
    Frame.forCall, List.map_cons, List.map_nil, Func.locals, List.append_nil, wpc, ctl, Wasm.Logic.Core.exec1,
    List.reverse_nil, List.reverse_cons, List.nil_append, List.cons_append, Wasm.Logic.Core.popInt, IntType.width,
    Store.mem?, Idx.toNat, Fin.coe_ofNat_eq_mod, Nat.zero_mod, h0, Option.pure_def, Option.bind_eq_bind,
    Option.bind_some, hma, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq, effAddr, Nat.reduceMod, BitVec.toNat_ofNat,
    hld, Option.map_some, Wasm.Logic.Core.intBinOp_i32_and, Wasm.Logic.Core.localVal?, Frame.local?, Nat.ofNat_pos,
    Nat.one_mod, Nat.one_lt_ofNat, Wasm.Logic.Core.intBinOp_i32_shl, Wasm.Logic.Core.intBinOp_i32_or, Nat.lt_add_one,
    fnPost, List.length_reverse, List.length_eq_zero_iff, Wasm.Logic.Core.Outcome.normal.injEq, List.reverse_eq_nil_iff]
  rw [hst]
  refine ⟨rfl, ?_⟩
  intro c' p' a'' z' sf' o' e₁ e₂ e₃ e₄ e₅ e₆
  subst e₁ e₂ e₃ e₄ e₅ e₆
  exact ⟨rfl, h2, habs, h3⟩



/-! ## The laws of representation M -/

theorem setMem_self {s : Store H} {a : Nat} {m : MemInst} (h : s.mems[a]? = some m) :
    s.setMem a m = s := by
  have ha := lt_of_getElem?_some h
  have : s.mems.set a m = s.mems := by
    rw [← getElem_of_getElem?_some h ha]; exact List.set_getElem_self ha
  simp [Store.setMem, this]

theorem setMem_setMem (s : Store H) (a : Nat) (m₁ m₂ : MemInst) :
    (s.setMem a m₁).setMem a m₂ = s.setMem a m₂ := by
  simp [Store.setMem, List.set_set]

theorem repM_laws (mi : ModuleInst) : (repM mi : Rep H).Laws where
  refl s hok := by
    obtain ⟨a, m, hmm, -⟩ := hok
    exact ⟨a, m, m, hmm, (setMem_self (memM_some hmm).2).symm, rfl, rfl, fun _ _ => rfl⟩
  trans s₁ s₂ s₃ h₁ h₂ := by
    obtain ⟨a, m, m₁, hm, rfl, ht1, hs1, hb1⟩ := h₁
    obtain ⟨a', m', m₂, hm', rfl, ht2, hs2, hb2⟩ := h₂
    rw [memM_setMem hm] at hm'
    cases hm'
    exact ⟨a, m, m₂, hm, setMem_setMem _ _ _ _, ht2.trans ht1, hs2.trans hs1,
      fun i hi => (hb2 i hi).trans (hb1 i hi)⟩
  funcs s s' h := by
    obtain ⟨a, m, m', -, rfl, -⟩ := h
    rfl
  flag s l hok h1 h2 := by
    obtain ⟨a, m, hmm, -⟩ := hok
    show absM mi s l < 2
    rw [absM_flag hmm h1 h2]
    split <;> decide

end Silmaril.Sim.X86Real
