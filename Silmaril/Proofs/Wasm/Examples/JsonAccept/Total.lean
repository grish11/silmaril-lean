module

public import Silmaril.Wasm.Examples.JsonAccept.Instance.Thms
public import Silmaril.Wasm.Logic.Words.Thms
public import Silmaril.Wasm.Logic.VCTotal.Thms
public import Silmaril.Wasm.Logic.Total.Thms
public import Mathlib.Tactic.IntervalCases
import Silmaril.Proofs.Wasm.Examples.JsonAccept.Basic
public import Silmaril.Proofs.Wasm.Examples.JsonAccept.Instance

@[expose] public section

namespace Silmaril.Proofs.Wasm.Examples.JsonAccept

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Verify Silmaril.Wasm.Logic.Words
open Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Examples.JsonAccept
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept

/-- The loop body of `accept`. -/
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

/-- The loop invariant, for the call on `(p, n)` from the store `s` with memory `B`. -/
def loopInv (s : Store Nat) (mi : ModuleInst) (B : ByteArray) (p n : BitVec 32) (s' : Store Nat)
    (f : Frame) : Prop :=
  s' = s ∧ f.module = mi ∧ ∃ i q b c : BitVec 32,
    f.locals = [some (.i32 p), some (.i32 n), some (.i32 i), some (.i32 q), some (.i32 b),
      some (.i32 c)] ∧ i.toNat ≤ n.toNat ∧ q = BitVec.ofNat 32 (runN 0 (bytesN B p.toNat i.toNat))

/-- The variant: bytes left to read. -/
def loopVar (n : BitVec 32) (_ : Store Nat) (f : Frame) : Nat := n.toNat - localI f 2

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
set_option linter.unusedSimpArgs false in
theorem accept_total {P : Profile} {host : HostSemantics Nat} {fi : FuncInst Nat} {a : Nat}
    {ps rs : Validation.Ty (.list .val)} (hcode : fi.code = .wasm prog.funcs[0])
    (he : Validation.Expand fi.type (.func ps rs)) (hps : ps.length = 2) (hrs : rs.length = 1)
    (x : BitVec 32 × BitVec 32) : TFSpecAt P host a (spec.fspec fi a x) := by
  obtain ⟨p, n⟩ := x
  refine TFSpecAt.of_body (fun s args h => h.1) hcode he
    (fun s args h => by rw [h.2.1]; simp [spec, Silmaril.Wasm.Verify.FnSpec.mem, hps]) ?_
  rintro s args ⟨hfi, rfl, ma, mt, B, hmem, hb, hov⟩ f vs₀
  rw [body_eq]
  show TWP P host s (Frame.forCall fi.module (spec.args (p, n)) prog.funcs[0].locals)
    (vals ([] : List Val).reverse ++ .plain (.block .empty [.loop .empty loopBody]) ::
      expression tailCode) _
  refine t_while (Inv := loopInv s fi.module B p n) (V := loopVar n) ?_ ?_
  · refine ⟨rfl, rfl, 0, 0, 0, 0, ?_, by simp, by simp [bytesN, runN]⟩
    simp [Frame.forCall, spec, Silmaril.Wasm.Verify.FnSpec.mem, prog,
      Silmaril.Wasm.Logic.VC.defaultVal_i32, Silmaril.Wasm.Logic.VC.defaultVal_int32]
    rfl
  · intro s' f' hinv
    obtain ⟨hs', hmod, i, q, b, c, hloc, hle, hq⟩ := hinv
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
    · -- exit: run the code after the loop
      refine whilePostT_exit ?_
      refine Silmaril.Wasm.Logic.VC.wpc_sound_total (fun _ _ _ _ => True) 0 tailCode loops_tail
        _ s' _ [] ?_
      simp (maxSteps := 100000000) [Silmaril.Wasm.Logic.VC.wpc, Silmaril.Wasm.Logic.VC.ctl,
          Silmaril.Wasm.Logic.VC.popI32, wat_vc_simp, -Silmaril.Wasm.Logic.Core.intTestOp_eqz,
          tailCode, prog]
      refine bodyPostT_normal (by simpa using hrs.symm) ⟨_, rfl, ?_⟩
      rintro ma' mt' B' ⟨h1, h2⟩
      rw [hm0] at h1; cases h1
      rw [hm] at h2; cases h2
      refine ⟨(Silmaril.Wasm.Verify.setMem_eq_self hm).symm, ?_⟩
      subst hin
      dsimp only
      generalize hk : runN 0 (bytesN B p.toNat i.toNat) = k at hq
      have hk6 : k < 6 := hk ▸ runN_lt (by decide) _
      subst hq
      clear hk
      interval_cases k <;> decide
    · have hlt : i.toNat < n.toNat := lt_of_le_of_ne hle (fun h => hne (BitVec.eq_of_toNat_eq h))
      have h1 : (p.toNat + i.toNat) % 4294967296 = p.toNat + i.toNat := Nat.mod_eq_of_lt (by omega)
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
      refine whilePostT_cont ⟨rfl, rfl, i + 1#32, _, _, _, rfl, by omega, ?_⟩ ?_
      · have hq' := hq
        rw [hi1, bytesN_succ, runN_append_single]
        generalize hk : runN 0 (bytesN B p.toNat i.toNat) = k at hq'
        have hk6 : k < 6 := hk ▸ runN_lt (by decide) _
        subst hq'
        generalize bd B (p.toNat + i.toNat) = v
        clear hk hq
        interval_cases k <;> revert v <;> decide
      · simp only [loopVar, localI, List.getElem?_cons_succ, List.getElem?_cons_zero]
        change n.toNat - (i + 1#32 : BitVec 32).toNat < n.toNat - i.toNat
        rw [hi1]; omega

/-- A totally correct configuration has a terminating run (`TSafe` is inductive, and its `step`
case provides a successor). -/
theorem TSafe.exists_exit {P : Profile} {host : HostSemantics Nat} {Q : Silmaril.Wasm.Logic.Core.Post Nat}
    {c : Config Nat} (h : TSafe P host Q c) :
    ∃ c', Steps P host c c' ∧ ∃ o, Exits o c'.code ∧ Q c'.store c'.frame o := by
  induction h with
  | exit o he hq => exact ⟨_, .refl, o, he, hq⟩
  | step hex _ ih =>
    obtain ⟨c₁, h₁⟩ := hex
    obtain ⟨c', hs, rest⟩ := ih c₁ h₁
    exact ⟨c', .head h₁ hs, rest⟩

/-- **`accept` terminates and returns**: on admitted arguments, some run of `$invoke` returns
the automaton's answer and leaves the store unchanged. -/
theorem accept_exists {P : Profile} {host : HostSemantics Nat} {s : Store Nat} {a : Nat}
    {fi : FuncInst Nat} {ps rs : Validation.Ty (.list .val)} (hfi : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm prog.funcs[0]) (he : Validation.Expand fi.type (.func ps rs))
    (hps : ps.length = 2) (hrs : rs.length = 1) {ma : Nat} {mt : MemoryType} {B : ByteArray}
    (hmem : MemAt s fi.module ma mt B) {p n : BitVec 32} (hb : p.toNat + n.toNat ≤ B.size)
    (hov : p.toNat + n.toNat < 2 ^ 32) :
    ∃ f', Steps P host (invoke s a [.i32 p, .i32 n]) ⟨s, f', vals [.i32 (if 2 ≤ runN 0
      (bytesN B p.toNat n.toNat) ∧ runN 0 (bytesN B p.toNat n.toNat) ≤ 4 then 1 else 0)]⟩ := by
  have ht := accept_total (P := P) (host := host) (a := a) hcode he hps hrs (p, n)
  have hsafe : TSafe P host (callPost {} [] ((spec.fspec fi a (p, n)).post s [.i32 p, .i32 n]))
      (invoke s a [.i32 p, .i32 n]) :=
    ht s [.i32 p, .i32 n] ⟨hfi, rfl, ma, mt, B, hmem, hb, hov⟩ {} []
      (.callRefType ((s.funcs[a]?.map FuncInst.type).getD default)) trivial
  obtain ⟨⟨s', f', code⟩, hs, o, hex, hq⟩ := TSafe.exists_exit hsafe
  obtain ⟨-, hq⟩ := hq
  rcases hq with ⟨res, rfl, res', hres, hpost⟩ | ⟨rfl, res', hres, -⟩ | ⟨x, rfl, res', hres, -⟩
  · cases hres
    obtain ⟨hs', hr⟩ := hpost ma mt B hmem
    simp only [List.nil_append] at hex
    simp only at hex hs'
    subst hex
    rw [hs'.trans (Silmaril.Wasm.Verify.setMem_eq_self hmem.2), hr] at hs
    exact ⟨f', hs⟩
  · cases hres
  · cases hres

/-! ## The embedded acceptor: exact characterisation -/

theorem prep_eq : prep.1 = ⟨prep.1.store, prep.1.frame, vals []⟩ := by
  have : prep.1.code = [] := List.isEmpty_iff.1 t_code
  cases hp : prep.1 with
  | mk st fr cd => rw [hp] at this; subst this; rfl

theorem memSegment_length {B : ByteArray} {p n : Nat} {w : List UInt8}
    (h : memSegment B p n = some w) : w.length = n := by
  unfold memSegment at h
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [Array.length_toList]
  exact Execution.Memory.readBytes_size B b p n hb

theorem memSegment_ofList (w : List UInt8) :
    memSegment ⟨w.toArray⟩ 0 w.length = some w := by
  simp [memSegment, Execution.Memory.readBytes, ByteArray.size, ByteArray.data_extract]

/-- Any run of the embedding answering `r` read a string shorter than `2 ^ 32`. -/
theorem exportAnswered_length {P : Profile} {Hosts : Set (HostSemantics Nat)} {r : BitVec 32}
    {w : List UInt8} (hw : w ∈ exportAnswered P Hosts prog "accept" r) : w.length < 2 ^ 32 := by
  obtain ⟨mt, I, c₀, hI, host, hhost, s₀, f₀, hsteps, a, ma, mt', B₀, B, p, n, hexp, hm0, hs0,
    hseg, hov, hbeh⟩ := hw
  rw [memSegment_length hseg]; exact n.isLt

set_option maxRecDepth 100000 in
/-- **Every admitted input gets an answer**: for an input `w` shorter than `2 ^ 32`, the embedding
(the spec instance, the input written at offset `0`, `accept(0, |w|)`) has a run returning the
automaton's answer. -/
theorem exportAnswered_of_run {P : Profile} {Hosts : Set (HostSemantics Nat)} {host : HostSemantics Nat}
    (hh : host ∈ Hosts) {w : List UInt8} (hw : w.length < 2 ^ 32) :
    w ∈ exportAnswered P Hosts prog "accept"
      (if 2 ≤ runN 0 (w.map UInt8.toNat) ∧ runN 0 (w.map UInt8.toNat) ≤ 4 then 1 else 0) := by
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
    ⟨by rw [hmems]; rfl, by rw [Silmaril.Wasm.Verify.getElem?_mems_setMem_self, hmi]; rfl⟩
  have hb : (0 : BitVec 32).toNat + n.toNat ≤ B.size := by rw [hn, hBs]; simp
  have hov : (0 : BitVec 32).toNat + n.toNat < 2 ^ 32 := by rw [hn]; simpa using hw
  obtain ⟨f', hs⟩ := accept_exists (P := P) (host := host) hfi hcode (FnType.expand_of_ofDefType? hty)
    (by simp [Validation.Ty.length, Validation.Ty.ofList])
    (by simp [Validation.Ty.length, Validation.Ty.ofList]) hmem hb hov
  have hsegl : segment B 0 w.length = w := by
    have := segment_eq (B := B) (p := 0) (n := w.length) (by simp [hBs])
    rw [memSegment_ofList] at this
    exact (Option.some.inj this).symm
  rw [hn, bytesN_eq_segment, show (0 : BitVec 32).toNat = 0 from rfl, hsegl] at hs
  refine ⟨mt0, inst, prep.1, isSpecInstance, host, hh, prep.1.store, prep.1.frame,
    by rw [← prep_eq], 0, 0, mi₀.type, mi₀.bytes, B, 0, n, t_export, by rw [t_frame_mems]; rfl,
    by rw [hmi], hseg, hov, ?_⟩
  exact .inl ⟨_, .values _, hs, rfl, rfl⟩

end Silmaril.Proofs.Wasm.Examples.JsonAccept
