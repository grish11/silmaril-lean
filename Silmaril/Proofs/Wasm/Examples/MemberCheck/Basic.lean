module

public import Silmaril.Wasm.Examples.MemberCheck.Defs
public import Silmaril.Wasm.Verify.FnSpec.Thms
public import Silmaril.Wasm.Logic.Memory.Thms
public import Silmaril.Wasm.Logic.Words.Thms
public import Silmaril.Wasm.Logic.VCTotal.Thms
public import Silmaril.Wasm.Logic.Total.Thms
public import Silmaril.Wasm.Examples.Wat.Thms

/-!
# The finite membership checker as a core Wasm module: proofs

* `spec_vc`: `check` meets `spec` (the `wpc` generator, as for
  `Silmaril.Wasm.Examples.JsonAccept`); the loop step is `inv_step`.
* `check_total`: total correctness, the loop variant being `len - i` (`t_while`), hence
  `check_exists`.
* `memb_iff`: `memb` on byte values is membership in `memberLang`.
* The instance and the embedding, as for `Silmaril.Wasm.Examples.EmptyCheck`.

New proofs, following `Silmaril.Proofs.Wasm.Examples.JsonAccept`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Examples.MemberCheck

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Verify Silmaril.Wasm.Logic.Words
open Silmaril.Wasm.Examples.MemberCheck
open Silmaril.Wasm.Examples.JsonAccept (bd bytesN segment)
open Silmaril.Wasm.Validation Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Game
open Silmaril.Wasm.Game.Accept
open Silmaril.Wasm.Numerics (Profile)

/-- A one-byte load is `bd` in bounds and fails out of bounds. -/
theorem load1_ite (B : ByteArray) (a : Nat) :
    Execution.Memory.load B a 1 = if a + 1 ≤ B.size then some (bd B a) else none := by
  split
  · unfold bd
    rw [Silmaril.Wasm.Logic.Core.load_eq ‹_›]; rfl
  · exact Silmaril.Wasm.Logic.Core.load_eq_none (B := B) (a := a) (n := 1) (by omega)

theorem bytesN_succ (B : ByteArray) (a k : Nat) :
    bytesN B a (k + 1) = bytesN B a k ++ [(bd B (a + k)).toNat] := by
  simp [bytesN, List.range_succ]

theorem inv_step (B : ByteArray) (p : Nat) (i c r : BitVec 32) (v : BitVec 8)
    (hc : c = BitVec.ofNat 32 ((bytesN B p i.toNat).head?.getD 0))
    (hr : r = if memb (bytesN B p i.toNat) = true then 1#32 else 0#32) :
    (c + if i = 0#32 then BitVec.setWidth 32 v else 0#32) =
      BitVec.ofNat 32 ((bytesN B p i.toNat ++ [v.toNat]).head?.getD 0) ∧
    (r ||| (if i = 0#32 then 0#32 else 1#32) &&&
        if BitVec.setWidth 32 v = c then 1#32 else 0#32) =
      if memb (bytesN B p i.toNat ++ [v.toNat]) = true then 1#32 else 0#32 := by
  have hv : v.toNat < 256 := v.isLt
  have hsw : BitVec.setWidth 32 v = BitVec.ofNat 32 v.toNat := by
    apply BitVec.eq_of_toNat_eq; simp
  rw [hsw]
  by_cases hi : i = 0#32
  · subst hi
    have h0 : bytesN B p (0#32).toNat = [] := rfl
    rw [h0] at hc hr ⊢
    simp only [List.head?_nil, Option.getD_none, memb, Bool.false_eq_true, ↓reduceIte] at hc hr
    subst hc hr
    simp [memb]
  · have hpos : 0 < i.toNat := by
      rcases Nat.eq_zero_or_pos i.toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hi
      · exact h
    obtain ⟨h, t, ht⟩ : ∃ h t, bytesN B p i.toNat = h :: t := by
      cases hl : bytesN B p i.toNat with
      | nil =>
        have := congrArg List.length hl
        simp [bytesN] at this; omega
      | cons h t => exact ⟨h, t, rfl⟩
    have hh : h < 256 := by
      have hmem : h ∈ bytesN B p i.toNat := by rw [ht]; exact List.mem_cons_self
      simp only [bytesN, List.mem_map, List.mem_range] at hmem
      obtain ⟨j, -, rfl⟩ := hmem
      exact (bd B (p + j)).isLt
    rw [ht] at hc hr ⊢
    simp only [List.head?_cons, Option.getD_some, List.cons_append, memb] at hc hr ⊢
    subst hc hr
    simp only [hi, ↓reduceIte, BitVec.add_zero, true_and]
    have heq : (BitVec.ofNat 32 v.toNat = BitVec.ofNat 32 h) ↔ v.toNat = h := by
      constructor
      · intro e
        have := congrArg BitVec.toNat e
        simp only [BitVec.toNat_ofNat] at this
        omega
      · intro e; rw [e]
    simp only [heq, List.contains_append, List.contains_cons, List.contains_nil, Bool.or_false]
    have hb : (h == v.toNat) = decide (v.toNat = h) := by
      by_cases e : v.toNat = h
      · simp [e]
      · simp [e, Ne.symm e]
    rw [hb]
    by_cases e1 : t.contains h = true <;> by_cases e : v.toNat = h <;>
      simp only [e1, e, Bool.or_eq_true, decide_eq_true_eq, or_true, or_false, ↓reduceIte] <;>
      decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
set_option linter.unusedSimpArgs false in
theorem spec_vc : spec.vc prog.funcs[0] := by
  simp only [Silmaril.Wasm.Verify.FnSpec.vc, Silmaril.Wasm.Verify.FnSpec.mem,
    Silmaril.Wasm.Logic.Words.MemAt, spec, prog]
  simp (maxSteps := 100000000) [Silmaril.Wasm.Logic.VC.wpc, Silmaril.Wasm.Logic.VC.ctl,
    Silmaril.Wasm.Logic.VC.loops, Silmaril.Wasm.Logic.VC.enterVC, Silmaril.Wasm.Logic.VC.labelQ,
    Silmaril.Wasm.Logic.VC.loopQ, Silmaril.Wasm.Logic.VC.popI32,
    Silmaril.Wasm.Execution.Core.Frame.forCall, Silmaril.Wasm.Examples.Common.bodyPost,
    Silmaril.Wasm.Execution.Core.ModuleInst.blockType?, Silmaril.Wasm.Logic.VC.defaultVal_i32,
    wat_vc_simp, -Silmaril.Wasm.Logic.Core.intTestOp_eqz,
    Silmaril.Wasm.Execution.Core.Store.mem?, Silmaril.Wasm.Execution.Core.effAddr,
    Silmaril.Wasm.IntType.width, load1_ite, Silmaril.Wasm.PackSize.width]
  intro p n mi s ma mt B hm0 hm hpre1 hpre2
  refine ⟨fun _ _ _ _ _ => by simp [bytesN, memb], ?_⟩
  intro s' f' hs i c r b hloc hle hinv hmod
  subst hs hmod
  obtain ⟨locals, module⟩ := f'
  simp only at hloc hinv ⊢
  subst hloc
  simp (maxSteps := 100000000) [Silmaril.Wasm.Logic.VC.wpc, Silmaril.Wasm.Logic.VC.ctl,
    Silmaril.Wasm.Logic.VC.loops, Silmaril.Wasm.Logic.VC.enterVC, Silmaril.Wasm.Logic.VC.labelQ,
    Silmaril.Wasm.Logic.VC.loopQ, Silmaril.Wasm.Logic.VC.popI32,
    Silmaril.Wasm.Examples.Common.bodyPost, wat_vc_simp, -Silmaril.Wasm.Logic.Core.intTestOp_eqz,
    Silmaril.Wasm.Execution.Core.Store.mem?, Silmaril.Wasm.Execution.Core.effAddr,
    Silmaril.Wasm.IntType.width, load1_ite, Silmaril.Wasm.PackSize.width]
  simp only at hm0
  refine ⟨fun hin ma' mt' B' h1 h2 => ?_, fun hne => ?_⟩
  · rw [hm0] at h1; cases h1
    rw [hm] at h2; cases h2
    refine ⟨(Silmaril.Wasm.Verify.setMem_eq_self hm).symm, ?_⟩
    subst hin
    exact (hinv ma mt B hm0 hm).2
  have hlt : i.toNat < n.toNat := lt_of_le_of_ne hle (fun h => hne (BitVec.eq_of_toNat_eq h))
  have h1 : (p.toNat + i.toNat) % 4294967296 = p.toNat + i.toNat := Nat.mod_eq_of_lt (by omega)
  have hb : p.toNat + i.toNat + 1 ≤ B.size := by omega
  simp only [hm0, hm, Option.bind_some, h1, hb, ↓reduceIte]
  simp (maxSteps := 100000000) [Silmaril.Wasm.Logic.VC.wpc, Silmaril.Wasm.Logic.VC.ctl,
    Silmaril.Wasm.Logic.VC.loops, Silmaril.Wasm.Logic.VC.enterVC, Silmaril.Wasm.Logic.VC.labelQ,
    Silmaril.Wasm.Logic.VC.loopQ, Silmaril.Wasm.Logic.VC.popI32,
    wat_vc_simp, -Silmaril.Wasm.Logic.Core.intTestOp_eqz,
    Silmaril.Wasm.Execution.Core.Store.mem?, Silmaril.Wasm.Execution.Core.effAddr,
    Silmaril.Wasm.IntType.width, load1_ite, Silmaril.Wasm.PackSize.width]
  refine ⟨by omega, fun ma' mt' B' h1' h2' => ?_⟩
  rw [hm0] at h1'; cases h1'
  rw [hm] at h2'; cases h2'
  obtain ⟨hc, hr⟩ := hinv ma mt B hm0 hm
  rw [show (i.toNat + 1) % 4294967296 = i.toNat + 1 from Nat.mod_eq_of_lt (by omega), bytesN_succ]
  exact inv_step B p.toNat i c r _ hc hr

/-! ## Membership -/

theorem memb_iff (w : List UInt8) : memb (w.map UInt8.toNat) = true ↔ w ∈ memberLang := by
  cases w with
  | nil =>
    simp only [List.map_nil, memb, Bool.false_eq_true, false_iff]
    rintro ⟨_, _, h, -⟩; cases h
  | cons c as =>
    simp only [List.map_cons, memb, List.contains_iff_mem, List.mem_map]
    constructor
    · rintro ⟨a, ha, he⟩
      exact ⟨c, as, rfl, (UInt8.toNat_inj.1 he) ▸ ha⟩
    · rintro ⟨c', as', h, hm⟩
      obtain ⟨rfl, rfl⟩ := List.cons.inj h
      exact ⟨_, hm, rfl⟩

theorem bytesN_eq_segment (B : ByteArray) (a k : Nat) :
    bytesN B a k = (segment B a k).map UInt8.toNat := by
  simp only [segment, bytesN, List.map_map]
  congr 1; funext j
  simp [Function.comp_def]

/-! ## Returning runs -/

variable {P : Profile} {host : HostSemantics Nat} {s : Store Nat} {a : Nat} {fi : FuncInst Nat}
  {ps rs : Validation.Ty (.list .val)} {ma : Nat} {mt : MemoryType} {B : ByteArray}
  {p n : BitVec 32}

theorem check_returns (hfi : s.funcs[a]? = some fi) (hc : fi.code = .wasm prog.funcs[0])
    (he : Validation.Expand fi.type (.func ps rs)) (hps : ps.length = 2) (hrs : rs.length = 1)
    (hmem : MemAt s fi.module ma mt B) (hb : p.toNat + n.toNat ≤ B.size)
    (hov : p.toNat + n.toNat < 2 ^ 32) {s' : Store Nat} {f' : Frame} {res : List Val}
    (hs : Steps P host (invoke s a [.i32 p, .i32 n]) ⟨s', f', vals res⟩) :
    s' = s ∧ res = [.i32 (if memb (bytesN B p.toNat n.toNat) then 1 else 0)] := by
  have hv := FnSpec.sound (P := P) (host := host) (a := a) spec_vc hc he
    (fun _ => by simp [spec, FnSpec.mem, hps]) (by simpa [spec, FnSpec.mem] using hrs) (p, n)
  obtain ⟨res', hres, hpost⟩ :=
    FSpecValid.invoke_vals hv ⟨hfi, rfl, ma, mt, B, hmem, hb, hov⟩ hs
  cases hres
  obtain ⟨hs', hr⟩ := hpost ma mt B hmem
  exact ⟨hs'.trans (setMem_eq_self hmem.2), hr⟩

/-! ## Total correctness -/

/-- The loop body. -/
def loopBody : List Instr := match prog.funcs[0].body with
  | .block _ [.loop _ b] :: _ => b
  | _ => []

/-- The code after the loop. -/
def tailCode : List Instr := match prog.funcs[0].body with
  | _ :: t => t
  | _ => []

theorem body_eq : prog.funcs[0].body = .block .empty [.loop .empty loopBody] :: tailCode := rfl
theorem loops_loopBody : Silmaril.Wasm.Logic.VC.loops loopBody = 0 := by decide +kernel
theorem loops_tail : Silmaril.Wasm.Logic.VC.loops tailCode = 0 := by decide +kernel

/-- The value of the `i32` local `k`, or `0`. -/
def localI (f : Frame) (k : Nat) : Nat :=
  match f.locals[k]? with
  | some (some (.num ⟨.int .i32, x⟩)) => x.toNat
  | _ => 0

/-- The loop invariant. -/
def loopInv (s : Store Nat) (mi : ModuleInst) (B : ByteArray) (p n : BitVec 32) (s' : Store Nat)
    (f : Frame) : Prop :=
  s' = s ∧ f.module = mi ∧ ∃ i c r b : BitVec 32,
    f.locals = [some (.i32 p), some (.i32 n), some (.i32 i), some (.i32 c), some (.i32 r),
      some (.i32 b)] ∧ i.toNat ≤ n.toNat ∧
    c = BitVec.ofNat 32 ((bytesN B p.toNat i.toNat).head?.getD 0) ∧
    r = (if memb (bytesN B p.toNat i.toNat) then 1 else 0)

/-- The variant: bytes left to read. -/
def loopVar (n : BitVec 32) (_ : Store Nat) (f : Frame) : Nat := n.toNat - localI f 2

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
set_option linter.unusedSimpArgs false in
theorem check_total {fi : FuncInst Nat} {a : Nat} (hcode : fi.code = .wasm prog.funcs[0])
    (he : Validation.Expand fi.type (.func ps rs)) (hps : ps.length = 2) (hrs : rs.length = 1)
    (x : BitVec 32 × BitVec 32) : TFSpecAt P host a (spec.fspec fi a x) := by
  obtain ⟨p, n⟩ := x
  refine TFSpecAt.of_body (fun s args h => h.1) hcode he
    (fun s args h => by rw [h.2.1]; simp [spec, FnSpec.mem, hps]) ?_
  rintro s args ⟨hfi, rfl, ma, mt, B, hmem, hb, hov⟩ f vs₀
  rw [body_eq]
  show TWP P host s (Frame.forCall fi.module (spec.args (p, n)) prog.funcs[0].locals)
    (vals ([] : List Val).reverse ++ .plain (.block .empty [.loop .empty loopBody]) ::
      expression tailCode) _
  refine t_while (Inv := loopInv s fi.module B p n) (V := loopVar n) ?_ ?_
  · refine ⟨rfl, rfl, 0, 0, 0, 0, ?_, by simp, by simp [bytesN], by simp [bytesN, memb]⟩
    simp [Frame.forCall, spec, FnSpec.mem, prog,
      Silmaril.Wasm.Logic.VC.defaultVal_i32, Silmaril.Wasm.Logic.VC.defaultVal_int32]
    rfl
  · intro s' f' hinv
    obtain ⟨hs', hmod, i, c, r, b, hloc, hle, hc, hr⟩ := hinv
    subst hs'
    refine Silmaril.Wasm.Logic.VC.wpc_sound_total (fun _ _ _ _ => True) 0 loopBody loops_loopBody
      _ s' f' [] ?_
    obtain ⟨locals, module⟩ := f'
    simp only at hloc hmod
    subst hloc hmod
    simp (maxSteps := 100000000) [Silmaril.Wasm.Logic.VC.wpc, Silmaril.Wasm.Logic.VC.ctl,
      Silmaril.Wasm.Logic.VC.loops, Silmaril.Wasm.Logic.VC.enterVC, Silmaril.Wasm.Logic.VC.labelQ,
      Silmaril.Wasm.Logic.VC.loopQ, Silmaril.Wasm.Logic.VC.popI32,
      wat_vc_simp, -Silmaril.Wasm.Logic.Core.intTestOp_eqz,
      Silmaril.Wasm.Execution.Core.Store.mem?, Silmaril.Wasm.Execution.Core.effAddr,
      Silmaril.Wasm.IntType.width, load1_ite, Silmaril.Wasm.PackSize.width, loopBody, prog]
    obtain ⟨hm0, hm⟩ := hmem
    refine ⟨fun hin => ?_, fun hne => ?_⟩
    · refine whilePostT_exit ?_
      refine Silmaril.Wasm.Logic.VC.wpc_sound_total (fun _ _ _ _ => True) 0 tailCode loops_tail
        _ s' _ [] ?_
      simp (maxSteps := 100000000) [Silmaril.Wasm.Logic.VC.wpc, Silmaril.Wasm.Logic.VC.ctl,
          Silmaril.Wasm.Logic.VC.popI32, wat_vc_simp, -Silmaril.Wasm.Logic.Core.intTestOp_eqz,
          tailCode, prog]
      refine bodyPostT_normal (by simpa using hrs.symm) ⟨_, rfl, ?_⟩
      rintro ma' mt' B' ⟨h1, h2⟩
      rw [hm0] at h1; cases h1
      rw [hm] at h2; cases h2
      refine ⟨(setMem_eq_self hm).symm, ?_⟩
      subst hin
      show [Val.i32 r] = _
      rw [hr]
    · have hlt : i.toNat < n.toNat := lt_of_le_of_ne hle (fun h => hne (BitVec.eq_of_toNat_eq h))
      have h1 : (p.toNat + i.toNat) % 4294967296 = p.toNat + i.toNat :=
        Nat.mod_eq_of_lt (by omega)
      have hb' : p.toNat + i.toNat + 1 ≤ B.size := by omega
      simp only [hm0, hm, Option.bind_some, h1, hb', ↓reduceIte]
      simp (maxSteps := 100000000) [Silmaril.Wasm.Logic.VC.wpc, Silmaril.Wasm.Logic.VC.ctl,
        Silmaril.Wasm.Logic.VC.loops, Silmaril.Wasm.Logic.VC.enterVC, Silmaril.Wasm.Logic.VC.labelQ,
        Silmaril.Wasm.Logic.VC.loopQ, Silmaril.Wasm.Logic.VC.popI32,
        wat_vc_simp, -Silmaril.Wasm.Logic.Core.intTestOp_eqz,
        Silmaril.Wasm.Execution.Core.Store.mem?, Silmaril.Wasm.Execution.Core.effAddr,
        Silmaril.Wasm.IntType.width, load1_ite, Silmaril.Wasm.PackSize.width, loopBody, prog]
      have hi1 : (i + 1#32).toNat = i.toNat + 1 := by
        have := n.isLt
        rw [BitVec.toNat_add]
        simp only [BitVec.toNat_ofNat]
        omega
      have hstep := inv_step B p.toNat i c r (bd B (p.toNat + i.toNat)) hc hr
      rw [← bytesN_succ, ← hi1] at hstep
      refine whilePostT_cont ⟨rfl, rfl, i + 1#32, _, _, _, rfl, by omega, hstep.1, hstep.2⟩ ?_
      change n.toNat - (i + 1#32 : BitVec 32).toNat < n.toNat - i.toNat
      rw [hi1]; omega

theorem TSafe.exists_exit {Q : Silmaril.Wasm.Logic.Core.Post Nat} {c : Config Nat}
    (h : TSafe P host Q c) :
    ∃ c', Steps P host c c' ∧ ∃ o, Exits o c'.code ∧ Q c'.store c'.frame o := by
  induction h with
  | exit o he hq => exact ⟨_, .refl, o, he, hq⟩
  | step hex _ ih =>
    obtain ⟨c₁, h₁⟩ := hex
    obtain ⟨c', hs, rest⟩ := ih c₁ h₁
    exact ⟨c', .head h₁ hs, rest⟩

theorem check_exists (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm prog.funcs[0])
    (he : Validation.Expand fi.type (.func ps rs)) (hps : ps.length = 2) (hrs : rs.length = 1)
    (hmem : MemAt s fi.module ma mt B) (hb : p.toNat + n.toNat ≤ B.size)
    (hov : p.toNat + n.toNat < 2 ^ 32) :
    ∃ f', Steps P host (invoke s a [.i32 p, .i32 n])
      ⟨s, f', vals [.i32 (if memb (bytesN B p.toNat n.toNat) then 1 else 0)]⟩ := by
  have ht := check_total (P := P) (host := host) (a := a) hcode he hps hrs (p, n)
  have hsafe : TSafe P host (callPost {} [] ((spec.fspec fi a (p, n)).post s [.i32 p, .i32 n]))
      (invoke s a [.i32 p, .i32 n]) :=
    ht s [.i32 p, .i32 n] ⟨hfi, rfl, ma, mt, B, hmem, hb, hov⟩ {} []
      (.callRefType ((s.funcs[a]?.map FuncInst.type).getD default)) trivial
  obtain ⟨⟨s', f', code⟩, hs, o, hex, hq⟩ := TSafe.exists_exit hsafe
  obtain ⟨-, hq⟩ := hq
  rcases hq with ⟨res, rfl, res', hres, hpost⟩ | ⟨rfl, res', hres, -⟩ |
      ⟨x, rfl, res', hres, -⟩
  · cases hres
    obtain ⟨hs', hr⟩ := hpost ma mt B hmem
    simp only [List.nil_append] at hex
    simp only at hex hs'
    subst hex
    rw [hs'.trans (setMem_eq_self hmem.2), hr] at hs
    exact ⟨f', hs⟩
  · cases hres
  · cases hres

/-! ## The instance -/

abbrev mt0 := specMT
abbrev prep := specPrep
abbrev inst := specInst

set_option maxRecDepth 100000

theorem t_valid : (validate? prog).isSome = true := by decide +kernel
theorem t_prep : (prepare? evalConst? (importStore (CExternType.funcs mt0.imports)) prog
    (importAddrs mt0)).isSome = true := by decide +kernel
theorem t_start : prep.2 = none := by decide +kernel
theorem t_code : prep.1.code.isEmpty = true := by decide +kernel
theorem t_nf : prep.1.store.funcs.length = 1 := by decide +kernel
theorem t_fcode : prep.1.store.funcs.map FuncInst.code = [.wasm prog.funcs[0]] := rfl
theorem t_ty : prep.1.store.funcs.map (fun fi => FnType.ofDefType? fi.type) =
    [some ⟨[.num (.int .i32), .num (.int .i32)], [.num (.int .i32)]⟩] := by decide +kernel
theorem t_fmems : prep.1.store.funcs.map (fun fi => fi.module.mems) = [[0]] := by decide +kernel
theorem t_frame_mems : prep.1.frame.module.mems = [0] := by decide +kernel
theorem t_export : exportFunc? prep.1.frame.module "check" = some 0 := by decide +kernel
theorem t_addrs : exportFuncAddrs prep.1.frame.module = [0] := by decide +kernel
theorem t_nmems : prep.1.store.mems.length = 1 := by decide +kernel
theorem t_imports : mt0.imports = [] := by decide +kernel

theorem validate_eq : validate? prog = some mt0 := by
  obtain ⟨mt, h⟩ := Option.isSome_iff_exists.1 t_valid
  simp [mt0, specMT, h]

theorem prepare_eq : prepare? evalConst? (importStore (CExternType.funcs mt0.imports)) prog
    (importAddrs mt0) = some prep := by
  obtain ⟨x, h⟩ := Option.isSome_iff_exists.1 t_prep
  simp [prep, specPrep, h]

theorem exists_fi : ∃ fi : FuncInst Nat, prep.1.store.funcs = [fi] ∧
    fi.code = .wasm prog.funcs[0] ∧
    FnType.ofDefType? fi.type = some ⟨[.num (.int .i32), .num (.int .i32)], [.num (.int .i32)]⟩ ∧
    fi.module.mems = [0] := by
  obtain ⟨fi, h⟩ := List.length_eq_one_iff.1 t_nf
  have h1 := t_fcode; have h2 := t_ty; have h3 := t_fmems
  rw [h] at h1 h2 h3
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h1 h2 h3
  exact ⟨fi, h, h1, h2, h3⟩

theorem spec_instance_eq {mt : CModuleType} {I : ScalarInstance} {c₀ : Config Nat}
    (hI : IsSpecInstance prog mt I c₀) : mt = mt0 ∧ c₀ = prep.1 := by
  have hmt : mt = mt0 := Option.some.inj (hI.valid.symm.trans validate_eq)
  subst hmt
  obtain ⟨c, st, hp, hc0, -, -⟩ := hI.prepared
  have h := Option.some.inj (hp.symm.trans prepare_eq)
  have hc : c = prep.1 := congrArg Prod.fst h
  have hs : st = prep.2 := congrArg Prod.snd h
  refine ⟨rfl, ?_⟩
  rw [hc0, hc, hs, t_start]; rfl

theorem isSpecInstance : IsSpecInstance prog mt0 inst prep.1 where
  valid := validate_eq
  funcImports := by rw [t_imports]; simp
  importTypes := by rw [t_imports]; exact .nil
  prepared := ⟨prep.1, prep.2, prepare_eq, by rw [t_start]; rfl, rfl, t_addrs⟩
  exportTypes := by
    obtain ⟨fi, hfuncs, -, hty, -⟩ := exists_fi
    exact .cons ⟨fi, by show prep.1.store.funcs[0]? = _; rw [hfuncs]; rfl, hty⟩ .nil

theorem prep_eq : prep.1 = ⟨prep.1.store, prep.1.frame, vals []⟩ := by
  have : prep.1.code = [] := List.isEmpty_iff.1 t_code
  cases hp : prep.1 with
  | mk st fr cd => rw [hp] at this; subst this; rfl

theorem steps_from_prep {s₀ : Store Nat} {f₀ : Frame}
    (h : Steps P host prep.1 ⟨s₀, f₀, vals []⟩) : s₀ = prep.1.store := by
  rcases Relation.ReflTransGen.cases_head h with he | ⟨c, hs, -⟩
  · rw [prep_eq] at he
    cases he; rfl
  · rw [prep_eq] at hs
    exact absurd hs Silmaril.Wasm.Execution.Core.Step.not_vals

/-! ## The embedding -/

/-- The bytes `[p, p + n)` as read by `check` are the memory's. -/
theorem segment_eq {B : ByteArray} {p n : Nat} (h : p + n ≤ B.size) :
    memSegment B p n = some (segment B p n) := by
  simp only [memSegment, Execution.Memory.readBytes, h, ↓reduceIte, Option.map_some,
    Option.some.injEq]
  apply List.ext_getElem
  · simp [segment, bytesN]; omega
  · intro i h1 h2
    have hi : i < n := by simpa [segment, bytesN] using h2
    simp only [segment, bytesN, List.getElem_map, List.getElem_range, bd]
    rw [Silmaril.Wasm.Logic.Core.load_eq (by omega)]
    simp only [Option.getD_some, Silmaril.Wasm.Logic.Core.bytesAt,
      Silmaril.Wasm.Logic.Core.leNat]
    simp [ByteArray.data_extract, List.take_one, Array.getElem_toList]
    have hlt : p + i < B.data.size := by
      have : B.size = B.data.size := rfl
      omega
    rw [Array.getElem?_eq_getElem hlt]
    simp only [Option.elim_some, Nat.mod_eq_of_lt (B.data[p + i]).toNat_lt]
    exact (UInt8.ofNat_toNat).symm

theorem ite_memb (w : List UInt8) :
    (if memb (w.map UInt8.toNat) = true then (1 : BitVec 32) else 0) =
      if w ∈ memberLang then 1 else 0 := by
  by_cases h : w ∈ memberLang
  · simp [h, (memb_iff w).2 h]
  · simp [h, show ¬ memb (w.map UInt8.toNat) = true from fun e => h ((memb_iff w).1 e)]

/-- **A run of the embedding answers by membership.** -/
theorem exportAnswered_eq {Hosts : Set (HostSemantics Nat)} {r : BitVec 32} {w : List UInt8}
    (hw : w ∈ exportAnswered P Hosts prog "check" r) :
    r = if w ∈ memberLang then 1 else 0 := by
  obtain ⟨mt, I, c₀, hI, host, -, s₀, f₀, hsteps, a, ma, mt', B₀, B, p, n, hexp, hm0, hs0, hseg,
    hov, hbeh⟩ := hw
  obtain ⟨-, rfl⟩ := spec_instance_eq hI
  have hs₀ := steps_from_prep hsteps
  subst hs₀
  rw [t_export] at hexp; cases hexp
  rw [t_frame_mems] at hm0; cases hm0
  have hb : p.toNat + n.toNat ≤ B.size := by
    unfold memSegment Execution.Memory.readBytes at hseg
    split_ifs at hseg with h
    · exact h
    · cases hseg
  rw [segment_eq hb] at hseg
  cases hseg
  obtain ⟨fi, hfuncs, hcode, hty, hmems⟩ := exists_fi
  have hfi : (prep.1.store.setMem 0 ⟨mt', B⟩).funcs[0]? = some fi := by
    show prep.1.store.funcs[0]? = some fi
    rw [hfuncs]; rfl
  have hmem : MemAt (prep.1.store.setMem 0 ⟨mt', B⟩) fi.module 0 mt' B :=
    ⟨by rw [hmems]; rfl, by rw [getElem?_mems_setMem_self, hs0]; rfl⟩
  have he := FnType.expand_of_ofDefType? hty
  rcases hbeh with ⟨⟨s', f', code⟩, res, hs, hcode', hr⟩ | ⟨h, -⟩
  · cases res with
    | values vs =>
      simp only [Result.toBehaviour, Behaviour.returns.injEq] at hr
      subst hr
      simp only [Result.toAdmin] at hcode'
      subst hcode'
      have := (check_returns hfi hcode he (by simp [Ty.length, Ty.ofList])
        (by simp [Ty.length, Ty.ofList]) hmem hb hov hs).2
      rw [bytesN_eq_segment, ite_memb] at this
      simp only [Val.i32, List.cons.injEq, Val.num.injEq, and_true] at this
      cases this; rfl
    | trap => cases hr
    | throw _ => cases hr
  · cases h

theorem memSegment_length {B : ByteArray} {p n : Nat} {w : List UInt8}
    (h : memSegment B p n = some w) : w.length = n := by
  unfold memSegment at h
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [Array.length_toList]
  exact Execution.Memory.readBytes_size B b p n hb

theorem memSegment_ofList (w : List UInt8) :
    memSegment ⟨w.toArray⟩ 0 w.length = some w := by
  simp [memSegment, Execution.Memory.readBytes, ByteArray.size, ByteArray.data_extract]

theorem exportAnswered_length {Hosts : Set (HostSemantics Nat)} {r : BitVec 32}
    {w : List UInt8} (hw : w ∈ exportAnswered P Hosts prog "check" r) : w.length < 2 ^ 32 := by
  obtain ⟨mt, I, c₀, hI, host, hhost, s₀, f₀, hsteps, a, ma, mt', B₀, B, p, n, hexp, hm0, hs0,
    hseg, hov, hbeh⟩ := hw
  rw [memSegment_length hseg]; exact n.isLt

set_option maxRecDepth 100000 in
/-- **Every admitted input gets its answer.** -/
theorem exportAnswered_of_run {Hosts : Set (HostSemantics Nat)} (hh : host ∈ Hosts)
    {w : List UInt8} (hw : w.length < 2 ^ 32) :
    w ∈ exportAnswered P Hosts prog "check" (if w ∈ memberLang then 1 else 0) := by
  have h0 : 0 < prep.1.store.mems.length := by rw [t_nmems]; decide
  obtain ⟨mi₀, hmi⟩ : ∃ mi₀, prep.1.store.mems[0]? = some mi₀ :=
    ⟨_, List.getElem?_eq_getElem h0⟩
  obtain ⟨fi, hfuncs, hcode, hty, hmems⟩ := exists_fi
  set B : ByteArray := ⟨w.toArray⟩
  set n : BitVec 32 := BitVec.ofNat 32 w.length
  have hn : n.toNat = w.length := by
    simp only [n, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hw
  have hBs : B.size = w.length := by simp [B, ByteArray.size]
  have hseg : memSegment B (0 : BitVec 32).toNat n.toNat = some w := by
    rw [hn]; exact memSegment_ofList w
  have hfi : (prep.1.store.setMem 0 ⟨mi₀.type, B⟩).funcs[0]? = some fi := by
    show prep.1.store.funcs[0]? = some fi
    rw [hfuncs]; rfl
  have hmem : MemAt (prep.1.store.setMem 0 ⟨mi₀.type, B⟩) fi.module 0 mi₀.type B :=
    ⟨by rw [hmems]; rfl, by rw [getElem?_mems_setMem_self, hmi]; rfl⟩
  have hb : (0 : BitVec 32).toNat + n.toNat ≤ B.size := by rw [hn, hBs]; simp
  have hov : (0 : BitVec 32).toNat + n.toNat < 2 ^ 32 := by rw [hn]; simpa using hw
  obtain ⟨f', hs⟩ := check_exists (P := P) (host := host) hfi hcode
    (FnType.expand_of_ofDefType? hty) (by simp [Validation.Ty.length, Validation.Ty.ofList])
    (by simp [Validation.Ty.length, Validation.Ty.ofList]) hmem hb hov
  have hsegl : segment B 0 w.length = w := by
    have := segment_eq (B := B) (p := 0) (n := w.length) (by simp [hBs])
    rw [memSegment_ofList] at this
    exact (Option.some.inj this).symm
  rw [hn, bytesN_eq_segment, show (0 : BitVec 32).toNat = 0 from rfl, hsegl, ite_memb] at hs
  refine ⟨mt0, inst, prep.1, isSpecInstance, host, hh, prep.1.store, prep.1.frame,
    by rw [← prep_eq], 0, 0, mi₀.type, mi₀.bytes, B, 0, n, t_export, by rw [t_frame_mems]; rfl,
    by rw [hmi], hseg, hov, ?_⟩
  exact .inl ⟨_, .values _, hs, rfl, rfl⟩

end Silmaril.Proofs.Wasm.Examples.MemberCheck
