module

public import Silmaril.Proofs.Sim.X86.GM.Sound

/-!
# GM: Wasm-level evaluation of the memory methods (no x86 state)

For Wasm proofs about dispatchers with memory: the checked accesses (`exec_loadW`,
`exec_storeW`) and the stack methods (`push_wstep`, `pop_wstep`, `call_wstep`, `ret_wstep`)
evaluated on a store described only by global values and its Wasm memory bytes: what changes
(stack pointer, RIP, one register, the bytes) and that every other global is unchanged
(`Same`).
-/

@[expose] public section

namespace Silmaril.Sim.X86.GM

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.X86 (Reg Word)
open Silmaril.Sim.X86.G
open Silmaril.Wasm.Logic.Core (exec exec1 exec_cons exec_nil exec_append)

variable {H : Type} {s : Store H} {f : Frame}

/-- The window's size bounds. -/
def Win.Ok (W : Win) : Prop := 8 ≤ W.size ∧ W.size ≤ 2 ^ 32 ∧ W.lo.toNat + W.size ≤ 2 ^ 64

/-- Every global outside `L` is unchanged. -/
def Same (s s' : Store H) (f : Frame) (L : Loc → Prop) : Prop := ∀ l, ¬ L l → gval s' f l = gval s f l

theorem Same.refl (s : Store H) (f : Frame) (L : Loc → Prop) : Same s s f L := fun _ _ => rfl

theorem Same.upd {s s' : Store H} {L : Loc → Prop} (h : Same s s' f L) (hl : Layout s' f) {l : Loc}
    (hL : L l) (v : Val) : Same s (upd s' f l v) f L := fun l' hl' => by
  have hne : l' ≠ l := fun e => hl' (by rw [e]; exact hL)
  rw [gval_upd hl]
  simp only [hne, ite_false]
  exact h l' hl'

theorem Same.setMem {s s' : Store H} {L : Loc → Prop} (h : Same s s' f L) (ma : Nat) (mi : MemInst) :
    Same s (s'.setMem ma mi) f L := fun l hl => by rw [gval_setMem]; exact h l hl

/-- **A checked load** (Wasm level). -/
theorem exec_loadW {W : Win} (hW : W.Ok) {X : List Instr} {x : Word} (hX : Pure s f X x)
    (hh : W.Holds x) {B : ByteArray} (hB : wbytes s f = some B) (hsz : W.size ≤ B.size)
    (rs : List Val) : ∃ v, Memory.load B (x.toNat - W.lo.toNat) 8 = some v ∧
      exec s f rs (loadCode W X) = some (s, f, Val.i64 v :: rs) := by
  obtain ⟨h8, h32, hlim⟩ := hW
  obtain ⟨ma, mi, hm, rfl⟩ := wbytes_eq hB
  obtain ⟨h1, h2⟩ := hh
  have hle : x.toNat - W.lo.toNat + 8 ≤ mi.bytes.size := by omega
  obtain ⟨v, hv⟩ : ∃ v, Memory.load mi.bytes (x.toNat - W.lo.toNat) 8 = some v :=
    ⟨_, Silmaril.Wasm.Logic.Core.load_eq hle⟩
  refine ⟨v, hv, ?_⟩
  rw [loadCode, exec_append, exec_append, exec_check hX h32 hlim,
    ite_eq_left_of_eq_true _ _ (eq_true ⟨h1, h2⟩)]
  simp only
  rw [exec_waddr hX]
  simp only
  have hl := hv
  rw [← (off_toNat h32 ⟨h1, h2⟩).1] at hl
  simp only [exec_cons, exec_nil, exec1_load64 hm hl]

/-- **A checked store** (Wasm level). -/
theorem exec_storeW {W : Win} (hW : W.Ok) {X V : List Instr} {x v : Word} (hX : Pure s f X x)
    (hV : Pure s f V v) (hh : W.Holds x) {B : ByteArray} (hB : wbytes s f = some B)
    (hsz : W.size ≤ B.size) (rs : List Val) :
    ∃ (ma : Nat) (mi : MemInst) (B' : ByteArray),
      Memory.store B (x.toNat - W.lo.toNat) (count := 8) v = some B' ∧
      exec s f rs (storeCode W X V) = some (s.setMem ma { mi with bytes := B' }, f, rs) ∧
      wbytes (s.setMem ma { mi with bytes := B' }) f = some B' := by
  obtain ⟨h8, h32, hlim⟩ := hW
  obtain ⟨ma, mi, hm, rfl⟩ := wbytes_eq hB
  obtain ⟨h1, h2⟩ := hh
  have hle : x.toNat - W.lo.toNat + 8 ≤ mi.bytes.size := by omega
  obtain ⟨B', hst⟩ : ∃ B', Memory.store mi.bytes (x.toNat - W.lo.toNat) (count := 8) v = some B' :=
    ⟨_, Silmaril.Wasm.Logic.Core.store_eq (B := mi.bytes) (a := x.toNat - W.lo.toNat) (n := 8) v hle⟩
  refine ⟨ma, mi, B', hst, ?_, wbytes_setMem hm _⟩
  rw [storeCode, exec_append, exec_append, exec_append, exec_check hX h32 hlim,
    ite_eq_left_of_eq_true _ _ (eq_true ⟨h1, h2⟩)]
  simp only
  rw [exec_waddr hX]
  simp only
  rw [hV]
  simp only
  rw [← (off_toNat h32 ⟨h1, h2⟩).1] at hst
  simp only [exec_cons, exec_nil, exec1_store64 hm hst]

/-! ## The stack methods -/

/-- The locations a stack method changes. -/
def SPR (r : Loc) (l : Loc) : Prop := l = .reg .rsp ∨ l = .rip ∨ l = r

theorem nextW (hl : Layout s f) {ip : Word} (hip : gval s f .rip = some (Val.i64 ip)) (len : Nat) :
    exec s f [] (nextCode len) = some (upd s f .rip (Val.i64 (ip + BitVec.ofNat 64 len)), f, []) := by
  simp only [nextCode, exec_cons, exec_nil, exec1_gget, hip, Option.map_some, exec1_c64, exec1_add,
    exec1_gset hl]

/-- `push r`. -/
theorem push_wstep {W : Win} (hW : W.Ok) (hl : Layout s f) {B : ByteArray} (hB : wbytes s f = some B)
    (hsz : W.size ≤ B.size) {r : Reg} {sp ip v : Word}
    (hsp : gval s f (.reg .rsp) = some (Val.i64 sp)) (hip : gval s f .rip = some (Val.i64 ip))
    (hr : gval s f (.reg r) = some (Val.i64 v)) (hh : W.Holds (sp - 8#64)) (len : Nat) :
    ∃ s' B', exec s f [] (storeCode W rspDown [gget (.reg r)] ++ rspDown ++ [gset (.reg .rsp)] ++
        nextCode len) = some (s', f, []) ∧
      Memory.store B ((sp - 8#64).toNat - W.lo.toNat) (count := 8) v = some B' ∧
      wbytes s' f = some B' ∧ Layout s' f ∧
      gval s' f (.reg .rsp) = some (Val.i64 (sp - 8#64)) ∧
      gval s' f .rip = some (Val.i64 (ip + BitVec.ofNat 64 len)) ∧ Same s s' f (SPR .rip) := by
  have hX : Pure s f rspDown (sp - 8#64) :=
    (pure_gget hsp).op (pure_c64 8) .sub (z := sp - 8#64) rfl
  obtain ⟨ma, mi, B', hst, he, hwb⟩ := exec_storeW hW hX (pure_gget hr) hh hB hsz []
  have hl₁ : Layout (s.setMem ma { mi with bytes := B' }) f := Layout.setMem hl _ _
  have hX₁ : Pure (s.setMem ma { mi with bytes := B' }) f rspDown (sp - 8#64) :=
    (pure_gget (by rw [gval_setMem]; exact hsp)).op (pure_c64 8) .sub (z := sp - 8#64) rfl
  have hl₂ : Layout (upd (s.setMem ma { mi with bytes := B' }) f (.reg .rsp) (Val.i64 (sp - 8#64))) f := hl₁.upd _ _
  have hip₂ : gval (upd (s.setMem ma { mi with bytes := B' }) f (.reg .rsp) (Val.i64 (sp - 8#64))) f .rip = some (Val.i64 ip) := by
    simp (maxDischargeDepth := 20) [gval_upd, hl, Layout.setMem, gval_setMem, hip]
  refine ⟨upd (upd (s.setMem ma { mi with bytes := B' }) f (.reg .rsp) (Val.i64 (sp - 8#64))) f .rip (Val.i64 (ip + BitVec.ofNat 64 len)), B', ?_, hst, ?_, hl₂.upd _ _, ?_, ?_, ?_⟩
  · rw [exec_append, exec_append, exec_append, he]
    simp only
    rw [hX₁]
    simp only [exec_cons, exec_nil, exec1_gset hl₁]
    exact nextW hl₂ hip₂ len
  · rw [wbytes_upd, wbytes_upd]; exact hwb
  · simp (maxDischargeDepth := 20) [gval_upd, hl, Layout.upd, Layout.setMem]
  · simp (maxDischargeDepth := 20) [gval_upd, hl, Layout.upd, Layout.setMem]
  · exact (((Same.refl s f _).setMem ma _).upd hl₁ (.inl rfl) _).upd hl₂ (.inr (.inl rfl)) _

/-- `call rel`. -/
theorem call_wstep {W : Win} (hW : W.Ok) (hl : Layout s f) {B : ByteArray} (hB : wbytes s f = some B)
    (hsz : W.size ≤ B.size) {sp ip : Word}
    (hsp : gval s f (.reg .rsp) = some (Val.i64 sp)) (hip : gval s f .rip = some (Val.i64 ip))
    (hh : W.Holds (sp - 8#64)) (len : Nat) (rel : BitVec 32) :
    ∃ s' B', exec s f [] (storeCode W rspDown [gget .rip, c64 (BitVec.ofNat 64 len), b64op .add] ++
        rspDown ++ [gset (.reg .rsp), gget .rip, c64 (BitVec.ofNat 64 len + rel.signExtend 64),
          b64op .add, gset .rip]) = some (s', f, []) ∧
      Memory.store B ((sp - 8#64).toNat - W.lo.toNat) (count := 8) (ip + BitVec.ofNat 64 len) =
        some B' ∧
      wbytes s' f = some B' ∧ Layout s' f ∧
      gval s' f (.reg .rsp) = some (Val.i64 (sp - 8#64)) ∧
      gval s' f .rip = some (Val.i64 (ip + (BitVec.ofNat 64 len + rel.signExtend 64))) ∧
      Same s s' f (SPR .rip) := by
  have hX : Pure s f rspDown (sp - 8#64) :=
    (pure_gget hsp).op (pure_c64 8) .sub (z := sp - 8#64) rfl
  have hV : Pure s f [gget .rip, c64 (BitVec.ofNat 64 len), b64op .add] (ip + BitVec.ofNat 64 len) :=
    (pure_gget hip).op (pure_c64 _) .add (z := ip + BitVec.ofNat 64 len) rfl
  obtain ⟨ma, mi, B', hst, he, hwb⟩ := exec_storeW hW hX hV hh hB hsz []
  have hl₁ : Layout (s.setMem ma { mi with bytes := B' }) f := Layout.setMem hl _ _
  have hX₁ : Pure (s.setMem ma { mi with bytes := B' }) f rspDown (sp - 8#64) :=
    (pure_gget (by rw [gval_setMem]; exact hsp)).op (pure_c64 8) .sub (z := sp - 8#64) rfl
  have hl₂ : Layout (upd (s.setMem ma { mi with bytes := B' }) f (.reg .rsp) (Val.i64 (sp - 8#64))) f := hl₁.upd _ _
  have hip₂ : gval (upd (s.setMem ma { mi with bytes := B' }) f (.reg .rsp) (Val.i64 (sp - 8#64))) f .rip = some (Val.i64 ip) := by
    simp (maxDischargeDepth := 20) [gval_upd, hl, Layout.setMem, gval_setMem, hip]
  refine ⟨upd (upd (s.setMem ma { mi with bytes := B' }) f (.reg .rsp) (Val.i64 (sp - 8#64))) f .rip (Val.i64 (ip + (BitVec.ofNat 64 len + rel.signExtend 64))), B', ?_, hst, ?_,
    hl₂.upd _ _, ?_, ?_, ?_⟩
  · rw [exec_append, exec_append, he]
    simp only
    rw [hX₁]
    simp only [exec_cons, exec_nil, exec1_gset hl₁, exec1_gget, hip₂, Option.map_some, exec1_c64,
      exec1_add, exec1_gset hl₂]
  · rw [wbytes_upd, wbytes_upd]; exact hwb
  · simp (maxDischargeDepth := 20) [gval_upd, hl, Layout.upd, Layout.setMem]
  · simp (maxDischargeDepth := 20) [gval_upd, hl, Layout.upd, Layout.setMem]
  · exact (((Same.refl s f _).setMem ma _).upd hl₁ (.inl rfl) _).upd hl₂ (.inr (.inl rfl)) _

/-- `pop r` (`r ≠ rsp`). -/
theorem pop_wstep {W : Win} (hW : W.Ok) (hl : Layout s f) {B : ByteArray} (hB : wbytes s f = some B)
    (hsz : W.size ≤ B.size) {r : Reg} (hr : r ≠ .rsp) {sp ip : Word}
    (hsp : gval s f (.reg .rsp) = some (Val.i64 sp)) (hip : gval s f .rip = some (Val.i64 ip))
    (hh : W.Holds sp) (len : Nat) :
    ∃ s' v, exec s f [] (loadCode W [gget (.reg .rsp)] ++ [gget (.reg .rsp), c64 8, b64op .add,
        gset (.reg .rsp), gset (.reg r)] ++ nextCode len) = some (s', f, []) ∧
      Memory.load B (sp.toNat - W.lo.toNat) 8 = some v ∧
      wbytes s' f = some B ∧ Layout s' f ∧
      gval s' f (.reg .rsp) = some (Val.i64 (sp + 8#64)) ∧ gval s' f (.reg r) = some (Val.i64 v) ∧
      gval s' f .rip = some (Val.i64 (ip + BitVec.ofNat 64 len)) ∧ Same s s' f (SPR (.reg r)) := by
  obtain ⟨v, hv, he⟩ := exec_loadW hW (pure_gget hsp) hh hB hsz []
  have hl₁ : Layout (upd s f (.reg .rsp) (Val.i64 (sp + 8#64))) f := hl.upd _ _
  have hl₂ : Layout (upd (upd s f (.reg .rsp) (Val.i64 (sp + 8#64))) f (.reg r) (Val.i64 v)) f := hl₁.upd _ _
  have hne : (Loc.reg r) ≠ Loc.reg .rsp := fun e => hr (Loc.reg.inj e)
  have hip₂ : gval (upd (upd s f (.reg .rsp) (Val.i64 (sp + 8#64))) f (.reg r) (Val.i64 v)) f .rip = some (Val.i64 ip) := by
    simp (maxDischargeDepth := 20) [gval_upd, hl, Layout.upd, hip]
  refine ⟨upd (upd (upd s f (.reg .rsp) (Val.i64 (sp + 8#64))) f (.reg r) (Val.i64 v)) f .rip (Val.i64 (ip + BitVec.ofNat 64 len)), v, ?_, hv, ?_, hl₂.upd _ _, ?_, ?_, ?_,
    ?_⟩
  · rw [exec_append, exec_append, he]
    simp (maxDischargeDepth := 20) only [exec_cons, exec_nil, exec1_gget, hsp, Option.map_some,
      exec1_c64, exec1_add, exec1_gset, hl, Layout.upd]
    exact nextW hl₂ hip₂ len
  · rw [wbytes_upd, wbytes_upd, wbytes_upd]; exact hB
  · simp (maxDischargeDepth := 20) [gval_upd, hl, Layout.upd, hne.symm]
  · simp (maxDischargeDepth := 20) [gval_upd, hl, Layout.upd]
  · simp (maxDischargeDepth := 20) [gval_upd, hl, Layout.upd]
  · exact ((((Same.refl s f _).upd hl (.inl rfl) _).upd hl₁ (.inr (.inr rfl)) _).upd hl₂
      (.inr (.inl rfl)) _)

/-- `ret`. -/
theorem ret_wstep {W : Win} (hW : W.Ok) (hl : Layout s f) {B : ByteArray} (hB : wbytes s f = some B)
    (hsz : W.size ≤ B.size) {sp : Word} (hsp : gval s f (.reg .rsp) = some (Val.i64 sp))
    (hh : W.Holds sp) :
    ∃ s' v, exec s f [] (loadCode W [gget (.reg .rsp)] ++ [gget (.reg .rsp), c64 8, b64op .add,
        gset (.reg .rsp), gset .rip]) = some (s', f, []) ∧
      Memory.load B (sp.toNat - W.lo.toNat) 8 = some v ∧
      wbytes s' f = some B ∧ Layout s' f ∧
      gval s' f (.reg .rsp) = some (Val.i64 (sp + 8#64)) ∧ gval s' f .rip = some (Val.i64 v) ∧
      Same s s' f (SPR .rip) := by
  obtain ⟨v, hv, he⟩ := exec_loadW hW (pure_gget hsp) hh hB hsz []
  have hl₁ : Layout (upd s f (.reg .rsp) (Val.i64 (sp + 8#64))) f := hl.upd _ _
  refine ⟨upd (upd s f (.reg .rsp) (Val.i64 (sp + 8#64))) f .rip (Val.i64 v), v, ?_, hv, ?_, hl₁.upd _ _, ?_, ?_, ?_⟩
  · rw [exec_append, he]
    simp (maxDischargeDepth := 20) only [exec_cons, exec_nil, exec1_gget, hsp, Option.map_some,
      exec1_c64, exec1_add, exec1_gset, hl, Layout.upd]
    rfl
  · rw [wbytes_upd, wbytes_upd]; exact hB
  · simp (maxDischargeDepth := 20) [gval_upd, hl, Layout.upd]
  · simp (maxDischargeDepth := 20) [gval_upd, hl, Layout.upd]
  · exact (((Same.refl s f _).upd hl (.inl rfl) _).upd hl₁ (.inr (.inl rfl)) _)

end Silmaril.Sim.X86.GM
