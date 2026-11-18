module

public import Silmaril.Sim.RV64.LForm.Defs
public import Silmaril.Sim.RV64.Mem.Thms

/-!
# The L-form chunks have the specialised semantics of `step`

**`lReg_sound`**: from memory bytes `B` (well formed, memory `0` of the frame), the chunk
`lReg b rd rs1 rs2` (`binop op = some b`) falls through with the memory now `B'`, where
`absState B' = Silmaril.RiscV.step (.reg op rd rs1 rs2) (absState B)` and only the register
block changed: the same post-state as a call of `step` on that instruction's word
(`StepPost`, via `wb_state`). Verified by `wpc` on the chunk (a dozen instructions); total
correctness, every profile and host relation (`wpc_sound_total`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.RV64.LForm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.VC Silmaril.Sim.RV64 Silmaril.Sim.RV64.Mem
open Silmaril.Wasm.Logic.Words (MemAt SameOutside)
open Silmaril.Wasm.Logic.Core (Post Outcome storeLE)
open Silmaril.RiscV (RegOp Reg State)

variable {H : Type}

/-- The `rd` field of an encoded instruction, as the simulator computes it. -/
theorem rd_field (i : Silmaril.RiscV.Instr) :
    ((Silmaril.RiscV.encode i >>> 7) % 32#32) = i.dest.setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  rw [reg_toNat, ← dest_of_decode (Silmaril.RiscV.decode_encode _)]
  simp
  have := i.dest.isLt; omega

set_option linter.unusedSimpArgs false

/-- Pushing an operand pushes the reference register value. -/
theorem wpc_opnd {s : Store H} {ls : List (Option Val)} {mi : ModuleInst} {ma : Nat}
    {mt : MemoryType} {B : ByteArray} (hm : MemAt s mi ma mt B) (hB : WF B) (inv : Invs H)
    (k : Nat) (r : Reg) (rest : List Instr) (Q : Post H) (vs : List Val)
    (h : wpc inv k rest Q s ⟨ls, mi⟩ (vs ++ [.num ⟨.int .i64, (absState B).read r⟩])) :
    wpc inv k (opnd r ++ rest) Q s ⟨ls, mi⟩ vs := by
  unfold WF at hB
  by_cases hr : r = 0#5
  · simp only [opnd, hr, ite_true, List.cons_append, List.nil_append] at h ⊢
    rw [wpc]
    simpa [Silmaril.Wasm.Logic.VC.ctl, Silmaril.Wasm.Logic.Core.exec1, State.read] using h
  · have hreg : 8 * r.toNat % 4294967296 = 8 * r.toNat := by have := r.isLt; omega
    have hrd : 8 * r.toNat + 8 ≤ B.size := by have := r.isLt; omega
    simp only [opnd, hr, ite_false, List.cons_append, List.nil_append]
    rw [wpc]
    simp only [Silmaril.Wasm.Logic.VC.ctl, Silmaril.Wasm.Logic.Core.exec1]
    rw [wpc]
    simpa [Silmaril.Wasm.Logic.VC.ctl, Silmaril.Wasm.Logic.Core.exec1, Silmaril.Wasm.Logic.Core.popInt,
      Silmaril.Wasm.Idx.toNat, IntType.width, effAddr, memq hm, load8, hreg, hrd, State.read,
      absState, hr] using h

theorem wpc_c64 {s : Store H} {f : Frame} (inv : Invs H) (k n : Nat) (rest : List Instr)
    (Q : Post H) (vs : List Val)
    (h : wpc inv k rest Q s f (vs ++ [.num ⟨.int .i64, BitVec.ofNat 64 n⟩])) :
    wpc inv k (c64 n :: rest) Q s f vs := by
  rw [wpc]; simpa [Silmaril.Wasm.Logic.VC.ctl, Silmaril.Wasm.Logic.Core.exec1] using h

theorem wpc_binop {s : Store H} {f : Frame} (inv : Invs H) (k : Nat) (b : IntBinOp)
    (x y z : BitVec 64) (hb : intBinOp .i64 b x y = .ok z) (rest : List Instr) (Q : Post H)
    (vs : List Val) (h : wpc inv k rest Q s f (vs ++ [.num ⟨.int .i64, z⟩])) :
    wpc inv k (.intBinOp .i64 b :: rest) Q s f (vs ++ [.num ⟨.int .i64, x⟩, .num ⟨.int .i64, y⟩]) := by
  rw [wpc]
  simpa [Silmaril.Wasm.Logic.VC.ctl, Silmaril.Wasm.Logic.Core.exec1, Silmaril.Wasm.Logic.Core.popInt, hb]
    using h

set_option maxRecDepth 10000 in
/-- **A chunk `lAlu rd ops`** whose `ops` push `v` writes `v` to `x[rd]` and bumps `pc`: the
memory becomes `wb B rd v pc`. -/
theorem lAlu_vc (rd : Reg) (ops : List Instr) (v : BitVec 64)
    (s : Store H) (ls : List (Option Val)) (mi : ModuleInst) (ma : Nat) (mt : MemoryType)
    (B : ByteArray) (hm : MemAt s mi ma mt B) (hB : WF B)
    (hops : ∀ (rest : List Instr) (Q : Post H) (vs : List Val),
      wpc (fun _ _ _ _ => True) 0 rest Q s ⟨ls, mi⟩ (vs ++ [.num ⟨.int .i64, v⟩]) →
      wpc (fun _ _ _ _ => True) 0 (ops ++ rest) Q s ⟨ls, mi⟩ vs) (Q : Post H)
    (hQ : Q (s.setMem ma ⟨mt, wb B (rd.setWidth 32) v (ld64 B 0)⟩) ⟨ls, mi⟩ (.normal [])) :
    wpc (fun _ _ _ _ => True) 0 (lAlu rd ops) Q s ⟨ls, mi⟩ [] := by
  have hB' : 65536 ≤ B.size := hB
  have hrd' : (rd.setWidth 32).toNat * 8 = 8 * rd.toNat := by simp; omega
  have hreg : 8 * rd.toNat % 4294967296 = 8 * rd.toNat := by have := rd.isLt; omega
  have hrd : 8 * rd.toNat + 8 ≤ B.size := by have := rd.isLt; omega
  have hs : (storeLE B (8 * rd.toNat) 8 v.toNat).size = B.size := size_storeLE' _ hrd
  by_cases h0 : rd = 0#5
  · simpa [lAlu, bumpPc, h0, Silmaril.Wasm.Logic.VC.wpc, Silmaril.Wasm.Logic.VC.ctl,
      Silmaril.Wasm.Logic.Core.exec1, Silmaril.Wasm.Logic.Core.popInt, Silmaril.Wasm.Logic.Core.popV,
      Silmaril.Wasm.Idx.toNat, IntType.width, effAddr, memq hm, load8, Silmaril.Sim.RV64.Mem.store_ite,
      show 8 ≤ B.size by omega, wb] using hQ
  · show wpc (fun _ _ _ _ => True) 0 (lAlu rd ops) Q s ⟨ls, mi⟩ []
    simp only [lAlu, h0, ite_false, List.append_assoc, List.singleton_append, List.cons_append]
    rw [wpc]
    simp only [Silmaril.Wasm.Logic.VC.ctl, Silmaril.Wasm.Logic.Core.exec1]
    refine hops _ _ [_] ?_
    have hpos : 1 ≤ rd.toNat := by
      rcases Nat.eq_zero_or_pos rd.toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) h0
      · exact h
    have hz : ¬ rd.setWidth 32 = 0#32 := fun h => by
      have h32 : (rd.setWidth 32).toNat = 0 := by rw [h]; rfl
      omega
    have hw : wb B (rd.setWidth 32) v (ld64 B 0) = storeLE (storeLE B (8 * rd.toNat) 8 v.toNat)
        0 8 (((ld64 B 0).toNat + 4) % 18446744073709551616) := by
      simp only [wb, hz, ite_false, hrd', BitVec.toNat_add]; rfl
    have hQ' : Q (s.setMem ma ⟨mt, storeLE (storeLE B (8 * rd.toNat) 8 v.toNat) 0 8
        (((ld64 (storeLE B (8 * rd.toNat) 8 v.toNat) 0).toNat + 4) % 18446744073709551616)⟩)
        ⟨ls, mi⟩ (.normal []) := by
      rw [ld64_storeLE_ne_nat _ hrd (by omega), ← hw]; exact hQ
    simpa [bumpPc, Silmaril.Wasm.Logic.VC.wpc, Silmaril.Wasm.Logic.VC.ctl,
      Silmaril.Wasm.Logic.Core.exec1, Silmaril.Wasm.Logic.Core.popInt, Silmaril.Wasm.Logic.Core.popV,
      Silmaril.Wasm.Idx.toNat, IntType.width, effAddr, memq hm, mem?_setMem hm, load8, Silmaril.Sim.RV64.Mem.store_ite,
      hreg, hrd, hs, show 8 ≤ B.size by omega] using hQ'

theorem binop_eval {op : RegOp} {b : IntBinOp} (h : binop op = some b) (x y : BitVec 64) :
    intBinOp .i64 b x y = .ok (RegOp.eval op x y) := by
  cases op <;> simp only [binop, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

theorem immop_eval {op : Silmaril.RiscV.ImmOp} {b : IntBinOp} (h : immop op = some b)
    (imm : BitVec 12) (x y : BitVec 64) (hy : y = imm.signExtend 64) :
    intBinOp .i64 b x y = .ok (Silmaril.RiscV.ImmOp.eval op x imm) := by
  subst hy
  cases op <;> simp only [immop, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

private theorem plain_nil : ∀ l : Instr, l ∈ ([] : List Instr) → ctl l = .plain :=
  fun _ hl => absurd hl List.not_mem_nil

private theorem plain_cons {i : Instr} {r : List Instr} (hi : ctl i = .plain)
    (hr : ∀ l, l ∈ r → ctl l = .plain) : ∀ l, l ∈ i :: r → ctl l = .plain :=
  fun l hl => (List.mem_cons.mp hl).elim (fun h => h ▸ hi) (hr l)

private theorem plain_append {a b : List Instr} (ha : ∀ l, l ∈ a → ctl l = .plain)
    (hb : ∀ l, l ∈ b → ctl l = .plain) : ∀ l, l ∈ a ++ b → ctl l = .plain :=
  fun l hl => (List.mem_append.mp hl).elim (ha l) (hb l)

private theorem opnd_plain (r : Reg) : ∀ l, l ∈ opnd r → ctl l = .plain := by
  unfold opnd
  split
  · exact plain_cons rfl plain_nil
  · exact plain_cons rfl (plain_cons rfl plain_nil)

private theorem lReg_ops {s : Store H} {ls : List (Option Val)} {mi : ModuleInst} {ma : Nat}
    {mt : MemoryType} {B : ByteArray} (hm : MemAt s mi ma mt B) (hB : WF B) {op : RegOp}
    {b : IntBinOp} (hb : binop op = some b) {rd rs1 rs2 : Reg} (rest : List Instr) (Q : Post H)
    (vs : List Val) (hk : wpc (fun _ _ _ _ => True) 0 rest Q s ⟨ls, mi⟩
      (vs ++ [.num ⟨.int .i64, (Silmaril.RiscV.Instr.reg op rd rs1 rs2).value (absState B)⟩])) :
    wpc (fun _ _ _ _ => True) 0 ((opnd rs1 ++ opnd rs2 ++ [.intBinOp .i64 b]) ++ rest) Q s
      ⟨ls, mi⟩ vs := by
  simp only [List.append_assoc, List.singleton_append]
  refine wpc_opnd hm hB _ _ rs1 _ _ _ (wpc_opnd hm hB _ _ rs2 _ _ _ ?_)
  simp only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]
  exact wpc_binop _ _ b _ _ _ (binop_eval hb _ _) _ _ _ hk

private theorem lImm_ops {s : Store H} {ls : List (Option Val)} {mi : ModuleInst} {ma : Nat}
    {mt : MemoryType} {B : ByteArray} (hm : MemAt s mi ma mt B) (hB : WF B)
    {op : Silmaril.RiscV.ImmOp} {b : IntBinOp} (hb : immop op = some b) {rd rs1 : Reg}
    {imm : BitVec 12} (rest : List Instr) (Q : Post H) (vs : List Val)
    (hk : wpc (fun _ _ _ _ => True) 0 rest Q s ⟨ls, mi⟩
      (vs ++ [.num ⟨.int .i64, (Silmaril.RiscV.Instr.imm op rd rs1 imm).value (absState B)⟩])) :
    wpc (fun _ _ _ _ => True) 0
      ((opnd rs1 ++ [c64 (imm.signExtend 64).toNat, .intBinOp .i64 b]) ++ rest) Q s
      ⟨ls, mi⟩ vs := by
  simp only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]
  refine wpc_opnd hm hB _ _ rs1 _ _ _ (wpc_c64 _ _ _ _ _ _ ?_)
  simp only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]
  exact wpc_binop _ _ b _ _ _ (immop_eval hb imm _ _ (by simp)) _ _ _ hk

/-- The chunk of each supported instruction, as `lAlu` with a value-pushing `ops`. -/
theorem lInstr_alu {i : Silmaril.RiscV.Instr} {c : List Instr} (h : lInstr i = some c)
    {s : Store H} {ls : List (Option Val)} {mi : ModuleInst} {ma : Nat} {mt : MemoryType}
    {B : ByteArray} (hm : MemAt s mi ma mt B) (hB : WF B) :
    ∃ ops, c = lAlu i.dest ops ∧ (∀ (rest : List Instr) (Q : Post H) (vs : List Val),
      wpc (fun _ _ _ _ => True) 0 rest Q s ⟨ls, mi⟩
        (vs ++ [.num ⟨.int .i64, i.value (absState B)⟩]) →
      wpc (fun _ _ _ _ => True) 0 (ops ++ rest) Q s ⟨ls, mi⟩ vs) ∧
      (∀ l, l ∈ ops → ctl l = .plain) := by
  match i, h with
  | .reg op rd rs1 rs2, h =>
    obtain ⟨b, hb, hc⟩ : ∃ b, binop op = some b ∧ lReg b rd rs1 rs2 = c :=
      Option.map_eq_some_iff.mp h
    exact ⟨_, hc.symm, lReg_ops hm hB hb,
      plain_append (plain_append (opnd_plain rs1) (opnd_plain rs2)) (plain_cons rfl plain_nil)⟩
  | .imm op rd rs1 imm, h =>
    obtain ⟨b, hb, hc⟩ : ∃ b, immop op = some b ∧ lImm b rd rs1 imm = c :=
      Option.map_eq_some_iff.mp h
    exact ⟨_, hc.symm, lImm_ops hm hB hb,
      plain_append (opnd_plain rs1) (plain_cons rfl (plain_cons rfl plain_nil))⟩
  | .upper .lui rd imm, h =>
    rw [← Option.some.inj h]
    refine ⟨_, rfl, fun rest Q vs hk => wpc_c64 _ _ _ _ _ _ ?_, plain_cons rfl plain_nil⟩
    simpa [Silmaril.RiscV.Instr.value, Silmaril.RiscV.UpperOp.eval] using hk

theorem loops_plain : ∀ (l : List Instr), (∀ x, x ∈ l → ctl x = .plain) → loops l = 0
  | [], _ => by simp [loops]
  | i :: r, h => by
    have hi := h i (by simp)
    rw [loops_other (i := i) (r := r) (by simp [hi]) (by simp [hi]) (by simp [hi])]
    exact loops_plain r fun x hx => h x (by simp [hx])

theorem loops_lAlu (rd : Reg) (ops : List Instr) (h : ∀ x, x ∈ ops → ctl x = .plain) :
    loops (lAlu rd ops) = 0 := by
  apply loops_plain
  intro x hx
  by_cases h0 : rd = 0#5 <;> simp [lAlu, bumpPc, h0] at hx
  · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · rcases hx with rfl | hx | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rfl
    · exact h x hx
    all_goals rfl

/-- The post-state of one chunk: falls through, frame unchanged, memory `B'` holding the
reference step of `i`, changed only in the register block. -/
def ChunkPost (s : Store H) (ls : List (Option Val)) (mi : ModuleInst)
    (ma : Nat) (mt : MemoryType) (B : ByteArray) (σ' : State) : Post H := fun s' f' o =>
  o = .normal [] ∧ f' = ⟨ls, mi⟩ ∧ ∃ B', s' = s.setMem ma ⟨mt, B'⟩ ∧ absState B' = σ' ∧
    SameOutside B B' 0 256

/-- **One L-form chunk has the specialised semantics of `step`** (total, every profile/host). -/
theorem lInstr_twp {P : Profile} {host : HostSemantics H} {i : Silmaril.RiscV.Instr}
    {c : List Instr} (h : lInstr i = some c) {s : Store H} {ls : List (Option Val)}
    {mi : ModuleInst} {ma : Nat} {mt : MemoryType} {B : ByteArray} (hm : MemAt s mi ma mt B)
    (hB : WF B) :
    Silmaril.Wasm.Logic.Hoare.TWP P host s ⟨ls, mi⟩ (expression c)
      (ChunkPost s ls mi ma mt B (Silmaril.RiscV.step i (absState B))) := by
  obtain ⟨ops, rfl, hops, hpl⟩ := lInstr_alu (ls := ls) h hm hB
  have hst : absState (wb B (i.dest.setWidth 32) (i.value (absState B)) (ld64 B 0)) =
      Silmaril.RiscV.step i (absState B) := by
    have := wb_state hB (Silmaril.RiscV.decode_encode i)
    rw [rd_field] at this
    exact this
  have hso : SameOutside B (wb B (i.dest.setWidth 32) (i.value (absState B)) (ld64 B 0)) 0 256 :=
    wb_same hB (by simp; omega) _ _
  have hv := wpc_sound_total (P := P) (host := host) (fun _ _ _ _ => True) 0 _
    (loops_lAlu _ _ hpl) (ChunkPost s ls mi ma mt B (Silmaril.RiscV.step i (absState B))) s _ []
    (lAlu_vc _ ops _ s ls mi ma mt B hm hB hops _ ⟨rfl, rfl, _, rfl, hst, hso⟩)
  simpa [vals] using hv

/-- The post-state of a program: the fold of the reference steps. -/
def ChunkPost' (is : List Silmaril.RiscV.Instr) (s : Store H) (ls : List (Option Val))
    (mi : ModuleInst) (ma : Nat) (mt : MemoryType) (B : ByteArray) : Post H := fun s' f' o =>
  o = .normal [] ∧ f' = ⟨ls, mi⟩ ∧ ∃ B', s' = s.setMem ma ⟨mt, B'⟩ ∧
    absState B' = is.foldl (fun σ i => Silmaril.RiscV.step i σ) (absState B) ∧
    SameOutside B B' 0 256

/-- **A straight-line L-form program** runs the reference steps of its instructions in order
(total, every profile/host). -/
theorem lProg_twp {P : Profile} {host : HostSemantics H} :
    ∀ {is : List Silmaril.RiscV.Instr} {c : List Instr}, lProg is = some c →
    ∀ {s : Store H} {ls : List (Option Val)} {mi : ModuleInst} {ma : Nat} {mt : MemoryType}
    {B : ByteArray}, MemAt s mi ma mt B → WF B →
    Silmaril.Wasm.Logic.Hoare.TWP P host s ⟨ls, mi⟩ (expression c)
      (ChunkPost' is s ls mi ma mt B)
  | [], c, h, s, ls, mi, ma, mt, B, hm, hB => by
    simp only [lProg, Option.some.injEq] at h
    subst h
    refine Silmaril.Wasm.Logic.Hoare.TSafe.exit (.normal []) rfl ⟨rfl, rfl, B, ?_, rfl, ?_⟩
    · exact (MemAt.setMem_self hm).symm
    · exact SameOutside.refl B 0 256
  | i :: is, c, h, s, ls, mi, ma, mt, B, hm, hB => by
    obtain ⟨c₁, h₁, h'⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨c₂, h₂, rfl⟩ := Option.map_eq_some_iff.mp h'
    rw [expression_append]
    refine Silmaril.Wasm.Logic.Hoare.TWP.seq (Silmaril.Wasm.Logic.Hoare.TSafe.post_mono
      (lInstr_twp (P := P) (host := host) h₁ hm hB) fun s' f' o hq => ?_)
    obtain ⟨rfl, rfl, B₁, rfl, hσ₁, hso₁⟩ := hq
    have hm₁ := hm.setMem B₁
    have hB₁ := wf_of_sameOutside hso₁ hB
    have ih := lProg_twp (P := P) (host := host) h₂ hm₁ hB₁ (ls := ls)
    refine Silmaril.Wasm.Logic.Hoare.TSafe.post_mono (P := P) (host := host) ih fun s'' f'' o hq => ?_
    obtain ⟨rfl, rfl, B₂, rfl, hσ₂, hso₂⟩ := hq
    refine ⟨rfl, rfl, B₂, by simp [Silmaril.Wasm.Logic.Words.setMem_setMem], ?_, hso₁.trans hso₂⟩
    rw [hσ₂, hσ₁]; rfl

/-! ## The reference run of the program's words -/

/-- Running the words of `is` placed after `pre` at `base`, from `pc = base + 4 |pre|`, retires
exactly the instructions of `is` in order. -/
theorem refRun_codeAt (base : Nat) (hb : base % 4 = 0) :
    ∀ (is : List Silmaril.RiscV.Instr) (pre : List (BitVec 32)) (σ : State),
      σ.pc.toNat = base + 4 * pre.length →
      base + 4 * (pre.length + is.length) < 2 ^ 64 →
      refRun (codeAt base (pre ++ is.map Silmaril.RiscV.encode)) is.length σ =
        some (is.foldl (fun σ i => Silmaril.RiscV.step i σ) σ)
  | [], pre, σ, _, _ => rfl
  | i :: is, pre, σ, hpc, hlen => by
    have hfetch : codeAt base (pre ++ (i :: is).map Silmaril.RiscV.encode) σ.pc =
        some (Silmaril.RiscV.encode i) := by
      simp only [codeAt, hpc]
      rw [ite_eq_left ⟨by omega, by omega⟩]
      simp [show (base + 4 * pre.length - base) / 4 = pre.length by omega]
    have hstep : refStep (codeAt base (pre ++ (i :: is).map Silmaril.RiscV.encode)) σ =
        some (Silmaril.RiscV.step i σ) := by
      simp only [refStep, hfetch, Option.bind_some, Silmaril.RiscV.decode_encode, Option.map_some]
    show (refStep _ σ).bind (refRun _ is.length) = _
    rw [hstep, Option.bind_some]
    have := refRun_codeAt base hb is (pre ++ [Silmaril.RiscV.encode i]) (Silmaril.RiscV.step i σ)
      (by simp [Silmaril.RiscV.step_pc, BitVec.toNat_add, hpc]; simp at hlen; omega)
      (by simp at hlen ⊢; omega)
    simpa using this

/-- **The composed L-form refines the reference** (total, every profile/host): if the L-form of
the straight-line program `is` is `c`, then from memory bytes `B` at `pc = 0x1000`, the code `c`
terminates with memory `B'` such that the reference machine, running the program's actual words
`is.map encode` at `0x1000`, reaches `absState B'` after exactly `|is|` steps; only the register
block changes. -/
theorem lProg_refines {P : Profile} {host : HostSemantics H} {is : List Silmaril.RiscV.Instr}
    {c : List Instr} (h : lProg is = some c) (hlen : 4096 + 4 * is.length < 2 ^ 64)
    {s : Store H} {ls : List (Option Val)} {mi : ModuleInst} {ma : Nat} {mt : MemoryType}
    {B : ByteArray} (hm : MemAt s mi ma mt B) (hB : WF B) (hpc : ld64 B 0 = 0x1000#64) :
    Silmaril.Wasm.Logic.Hoare.TWP P host s ⟨ls, mi⟩ (expression c) fun s' f' o =>
      o = .normal [] ∧ f' = ⟨ls, mi⟩ ∧ ∃ B', s' = s.setMem ma ⟨mt, B'⟩ ∧
        refRun (codeAt 4096 (is.map Silmaril.RiscV.encode)) is.length (absState B) =
          some (absState B') ∧ SameOutside B B' 0 256 := by
  refine Silmaril.Wasm.Logic.Hoare.TSafe.post_mono (lProg_twp (P := P) (host := host) h hm hB)
    fun s' f' o hq => ?_
  obtain ⟨h1, h2, B', h3, h4, h5⟩ := hq
  refine ⟨h1, h2, B', h3, ?_, h5⟩
  rw [h4]
  simpa using refRun_codeAt 4096 (by decide) is [] (absState B)
    (by show (ld64 B 0).toNat = _; rw [hpc]; rfl) (by simpa using hlen)

end Silmaril.Sim.RV64.LForm
