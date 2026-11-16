module

public import Silmaril.Proofs.Sim.X86Real.Common
public import Silmaril.Wasm.Logic.VCCalls.Thms

/-!
# The shared core of `simG`/`simM`, verified once against the accessor contracts

For an abstract representation `ρ` (`Rep.Laws`) and instance `I`, the core functions `$mask`,
`$sbit`, `$parity`, `$fres`, `$rd`, `$wr`, `$alu` and the method `i_alu_rr` (64-bit
add/sub/cmp) meet their contracts (`Silmaril.Sim.X86Real.maskSpec` … `iAluRRSpec`), with total
correctness, **given** that the five accessors meet theirs (`rgetSpec` … `fset6Spec`). The
proofs use the accessors only through these contracts (modular calls of `wpc` with a spec
context): this is the code-substitution principle of the simulator framework (`ExportSim.methodOK_of_ctxSat`)
in its total form, and it is why one proof serves both representations. A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.X86Real

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.VC
open Silmaril.Wasm.Logic.Hoare (FSpec TFSpecAt)

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {H : Type} {P : Profile} {host : HostSemantics H}

section
variable (ρ : Rep H) (I : Inst H)

/-- The contract of defined function `k` with its number of parameters. -/
def entry (k : Nat) : Nat × FSpec H :=
  match k with
  | 0 => (1, rgetSpec ρ (I.fi 0) (I.A 0))
  | 1 => (2, rsetSpec ρ (I.fi 1) (I.A 1))
  | 2 => (1, fgetSpec ρ (I.fi 2) (I.A 2))
  | 3 => (2, fsetSpec ρ (I.fi 3) (I.A 3))
  | 4 => (6, fset6Spec ρ (I.fi 4) (I.A 4))
  | 5 => (1, maskSpec ρ I)
  | 6 => (1, sbitSpec ρ I)
  | 9 => (1, paritySpec ρ I)
  | 10 => (5, fresSpec ρ I)
  | 11 => (2, rdSpec ρ I)
  | 12 => (3, wrSpec ρ I)
  | 17 => (4, aluSpec ρ I)
  | 42 => (4, iAluRRSpec ρ I)
  | _ => (0, ⟨fun _ _ => False, fun _ _ _ _ => True⟩)

/-- The spec context of the functions `ks`. -/
@[reducible] def specsOf (ks : List Nat) : VCSpecs H :=
  ⟨fun a => (ks.find? (fun k => I.A k == a)).map (entry ρ I)⟩

/-- The functions whose contracts are covered. -/
def coreKs : List Nat := [0, 1, 2, 3, 4, 5, 6, 9, 10, 11, 12, 17, 42]

/-- Distinct addresses for the covered functions. -/
def Inst.Inj (I : Inst H) : Prop := ∀ i ∈ coreKs, ∀ j ∈ coreKs, I.A i = I.A j → i = j

end

theorem find_at (A : Nat → Nat) (k : Nat) :
    ∀ ks : List Nat, (∀ i ∈ ks, A i = A k → i = k) → k ∈ ks →
      ks.find? (fun j => A j == A k) = some k
  | [], _, h => absurd h List.not_mem_nil
  | j :: ks, hi, hk => by
    by_cases hj : A j = A k
    · have := hi j (by simp) hj; subst this; simp
    · have hjk : j ≠ k := fun h => hj (h ▸ rfl)
      have hb : (A j == A k) = false := by simp [hj]
      rw [List.find?_cons, hb]
      exact find_at A k ks (fun i hi' => hi i (by simp [hi'])) (by simpa [hjk.symm] using hk)

theorem specsOf_at {ρ : Rep H} {I : Inst H} {ks : List Nat} (hks : ∀ i ∈ ks, i ∈ coreKs)
    (hinj : Inst.Inj I) {k : Nat} (hk : k ∈ ks) :
    (specsOf ρ I ks).specs (I.A k) = some (entry ρ I k) := by
  rw [show (specsOf ρ I ks).specs (I.A k) = (ks.find? (fun j => I.A j == I.A k)).map (entry ρ I)
    from rfl]
  rw [find_at I.A k ks (fun i hi h => hinj i (hks i hi) k (hks k hk) h) hk]
  rfl

theorem entry_funcs {ρ : Rep H} {I : Inst H} {k : Nat} {s : Store H} {args : List Val}
    (hk : k ∈ coreKs) (h : (entry ρ I k).2.pre s args) : (s.funcs[I.A k]?).isSome := by
  simp only [coreKs, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | (rw [h.1]; rfl) | (rw [h.1.1]; rfl)

theorem specsOf_tvalid {ρ : Rep H} {I : Inst H} {ks : List Nat} (hks : ∀ i ∈ ks, i ∈ coreKs)
    (h : ∀ k ∈ ks, TFSpecAt P host (I.A k) (entry ρ I k).2) : (specsOf ρ I ks).TValid P host := by
  intro a n S hs
  change (ks.find? (fun j => I.A j == a)).map (entry ρ I) = some (n, S) at hs
  rw [Option.map_eq_some_iff] at hs
  obtain ⟨k, hf, he⟩ := hs
  have hmem := List.mem_of_find?_eq_some hf
  have hA : I.A k = a := by simpa using List.find?_some hf
  subst hA
  have := h k hmem
  rw [he] at this
  exact ⟨this, fun s args hp => entry_funcs (hks k hmem) (by rw [he]; exact hp)⟩

/-! ## Per-operation conditions (expanded below) -/

set_option hygiene false in
/-- The condition of `$alu` for one operation `op` (one theorem per operation, so that the
three are elaborated in parallel). Defined here, before the proofs: a macro definition waits for
the proofs above it. -/
local macro "alu_case" name:ident op:num : command => `(
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem $name {ρ : Rep H} {I : Inst H} {rs : Silmaril.Wasm.Validation.Ty (.list .val)}
    (hinj : I.Inj) (hmod : (I.fi 17).module = I.mi) (hrs : rs.length = 1) (s : Store H)
    (hok : ρ.ok s) (hI : I.Ok s) (a b : BitVec 64) (args : List Val)
    (hargs : args = [Val.i32 $op, Val.i32 8, Val.i64 a, Val.i64 b]) :
    wpc (Γ := specsOf ρ I ks2) (fun _ _ _ _ => True) 0 (fn simG 17).body
      (fnPost rs.length ((aluSpec ρ I).post s args)) s
      (Frame.forCall (I.fi 17).module args (fn simG 17).locals) [] := by
  obtain ⟨f5, s5, e5, l5, g5⟩ : FnAt ρ I s ks2 5 15 :=
    hI.fnAt ks2_sub hinj rfl (by decide) (by decide)
  obtain ⟨f6, s6, e6, l6, g6⟩ : FnAt ρ I s ks2 6 16 :=
    hI.fnAt ks2_sub hinj rfl (by decide) (by decide)
  obtain ⟨f10, s10, e10, l10, g10⟩ : FnAt ρ I s ks2 10 20 :=
    hI.fnAt ks2_sub hinj rfl (by decide) (by decide)
  have c5 := callVC_at (Γ := specsOf ρ I ks2) (m := I.mi) (x := ⟨15⟩) f5 e5
  have c6 := callVC_at (Γ := specsOf ρ I ks2) (m := I.mi) (x := ⟨16⟩) f6 e6
  have c10 := callVC_at (Γ := specsOf ρ I ks2) (m := I.mi) (x := ⟨20⟩) f10 e10
  simp [↓c5, ↓c6, ↓c10, ↓tableVC_cons_self, ↓tableVC_cons_of_ne, ↓tableVC_nil_of_le, fn, simG, wpc, ctl, enterVC, labelQ_normal, labelQ_br_zero, labelQ_br_succ, labelQ_ret, labelQ_trap, labelQ_throw, labelQ_tail, popI32, popSelect,
    Silmaril.Wasm.Logic.Core.exec1,
    Silmaril.Wasm.Execution.Core.ModuleInst.blockType?, Frame.forCall, fnPost, hrs,
    Silmaril.Wasm.Logic.Core.localVal?, Silmaril.Wasm.Logic.Core.popInt, Silmaril.Wasm.Logic.Core.popV,
    Frame.local?, Frame.setLocal, Idx.toNat, IntType.width, NumType.width, extendU32,
    NumVal.mk.injEq, heq_eq_eq, Val.i32, Val.i64, bool32, cvt1, callK, corePre,
    hmod, f5, s5, e5, l5, g5, f6, s6, e6, l6, g6, f10, s10, e10, l10, g10,
    entry, maskSpec, sbitSpec, fresSpec, aluSpec, hok, hI, hargs]
  refine ⟨by repeat' (first | apply And.intro | (split <;> decide) | exact Nat.mod_lt _ (by decide)),
    fun s' o h => ?_⟩
  obtain ⟨rfl, h1, h0, h3, h2⟩ := h _ _ _ _ rfl rfl rfl rfl
  simp [h1, h0, h2, h3, aluFlags, aluRes, updF, zfOf, sfOf])

set_option hygiene false in
/-- The condition of `i_alu_rr` for one operation `op` (one theorem per operation). -/
local macro "alu_rr_case" name:ident op:num : command => `(
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem $name {ρ : Rep H} (hL : ρ.Laws) {I : Inst H} {rs : Silmaril.Wasm.Validation.Ty (.list .val)}
    (hinj : I.Inj) (hmod : (I.fi 42).module = I.mi) (hrs : rs.length = 0) (s : Store H)
    (hok : ρ.ok s) (hI : I.Ok s) (d r : BitVec 32) (hd : d.toNat < 16) (hr : r.toNat < 16)
    (args : List Val) (hargs : args = [Val.i32 $op, Val.i32 8, Val.i32 d, Val.i32 r]) :
    wpc (Γ := specsOf ρ I ks3) (fun _ _ _ _ => True) 0 (fn simG 42).body
      (fnPost rs.length ((iAluRRSpec ρ I).post s args)) s
      (Frame.forCall (I.fi 42).module args (fn simG 42).locals) [] := by
  obtain ⟨f11, s11, e11, l11, g11⟩ : FnAt ρ I s ks3 11 21 :=
    hI.fnAt ks3_sub hinj rfl (by decide) (by decide)
  obtain ⟨f12, s12, e12, l12, g12⟩ : FnAt ρ I s ks3 12 22 :=
    hI.fnAt ks3_sub hinj rfl (by decide) (by decide)
  obtain ⟨f17, s17, e17, l17, g17⟩ : FnAt ρ I s ks3 17 27 :=
    hI.fnAt ks3_sub hinj rfl (by decide) (by decide)
  have c11 := callVC_at (Γ := specsOf ρ I ks3) (m := I.mi) (x := ⟨21⟩) f11 e11
  have c12 := callVC_at (Γ := specsOf ρ I ks3) (m := I.mi) (x := ⟨22⟩) f12 e12
  have c17 := callVC_at (Γ := specsOf ρ I ks3) (m := I.mi) (x := ⟨27⟩) f17 e17
  simp [↓c11, ↓c12, ↓c17, ↓tableVC_cons_self, ↓tableVC_cons_of_ne, ↓tableVC_nil_of_le, fn, simG, wpc, ctl, enterVC, labelQ_normal, labelQ_br_zero, labelQ_br_succ, labelQ_ret, labelQ_trap, labelQ_throw, labelQ_tail, popI32, popSelect,
    Silmaril.Wasm.Logic.Core.exec1,
    Silmaril.Wasm.Execution.Core.ModuleInst.blockType?, Frame.forCall, fnPost, hrs,
    Silmaril.Wasm.Logic.Core.localVal?, Silmaril.Wasm.Logic.Core.popInt, Silmaril.Wasm.Logic.Core.popV,
    Frame.local?, Frame.setLocal, Idx.toNat, IntType.width, NumType.width, extendU32,
    NumVal.mk.injEq, heq_eq_eq, Val.i32, Val.i64, bool32, cvt1, callK, corePre, hmod,
    f11, s11, e11, l11, g11, f12, s12, e12, l12, g12, f17, s17, e17, l17, g17,
    entry, rdSpec, wrSpec, aluSpec, iAluRRSpec, AluOp, hok, hI, hd, hr, hargs]
  intro s' h1 h2 h3 h4
  first
    | exact ⟨⟨by rw [hL.funcs s s' h3]; exact s12, h1, h2⟩,
        fun s'' g1 g2 g3 g4 => ⟨g1, g2, hL.trans _ _ _ h3 g3, by rw [g4, h4]⟩⟩
    | exact ⟨h1, h2, h3, h4⟩)

/-! ## Leaf functions -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask_total {ρ : Rep H} {I : Inst H} {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)}
    (hcode : (I.fi 5).code = .wasm (fn simG 5))
    (he : Silmaril.Wasm.Validation.Expand (I.fi 5).type (.func ps rs)) (hps : ps.length = 1)
    (hrs : rs.length = 1) :
    TFSpecAt P host (I.A 5) (maskSpec ρ I) := by
  refine tfspec_of_wpc VCSpecs.tvalid_empty (by simp [fn, simG, loops, ctl]) (fun _ _ h => h.1.1)
    hcode he (fun _ _ h => by obtain ⟨-, rfl⟩ := h; simp [hps]) ?_
  rintro s _ ⟨-, rfl⟩
  simp [fn, simG, wpc, ctl, enterVC, labelQ, popI32, Silmaril.Wasm.Logic.Core.exec1,
    Silmaril.Wasm.Execution.Core.ModuleInst.blockType?, Frame.forCall, fnPost, hrs,
    Silmaril.Wasm.Logic.Core.localVal?, Silmaril.Wasm.Logic.Core.popInt, Frame.local?, Idx.toNat,
    Val.i32, Val.i64, maskSpec, bool32, cvt1]


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sbit_total {ρ : Rep H} {I : Inst H} {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)}
    (hcode : (I.fi 6).code = .wasm (fn simG 6))
    (he : Silmaril.Wasm.Validation.Expand (I.fi 6).type (.func ps rs)) (hps : ps.length = 1)
    (hrs : rs.length = 1) :
    TFSpecAt P host (I.A 6) (sbitSpec ρ I) := by
  refine tfspec_of_wpc VCSpecs.tvalid_empty (by simp [fn, simG, loops, ctl]) (fun _ _ h => h.1.1)
    hcode he (fun _ _ h => by obtain ⟨-, rfl⟩ := h; simp [hps]) ?_
  rintro s _ ⟨-, rfl⟩
  simp [fn, simG, wpc, ctl, enterVC, labelQ, popI32, popSelect, Silmaril.Wasm.Logic.Core.exec1,
    Silmaril.Wasm.Execution.Core.ModuleInst.blockType?, Frame.forCall, fnPost, hrs,
    Silmaril.Wasm.Logic.Core.localVal?, Silmaril.Wasm.Logic.Core.popInt, Silmaril.Wasm.Logic.Core.popV,
    Frame.local?, Frame.setLocal, Idx.toNat, IntType.width, NumType.width, extendU32,
    NumVal.mk.injEq, heq_eq_eq, Val.i32, Val.i64, bool32, cvt1, callVC, callK, corePre, sbitSpec, sb64]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem parity_total {ρ : Rep H} {I : Inst H} {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)}
    (hcode : (I.fi 9).code = .wasm (fn simG 9))
    (he : Silmaril.Wasm.Validation.Expand (I.fi 9).type (.func ps rs)) (hps : ps.length = 1)
    (hrs : rs.length = 1) :
    TFSpecAt P host (I.A 9) (paritySpec ρ I) := by
  refine tfspec_of_wpc VCSpecs.tvalid_empty (by simp [fn, simG, loops, ctl]) (fun _ _ h => h.1.1)
    hcode he (fun _ _ h => by obtain ⟨-, r, rfl⟩ := h; simp [hps]) ?_
  rintro s _ ⟨-, r, rfl⟩
  simp [fn, simG, wpc, ctl, enterVC, labelQ, popI32, popSelect, Silmaril.Wasm.Logic.Core.exec1,
    Silmaril.Wasm.Execution.Core.ModuleInst.blockType?, Frame.forCall, fnPost, hrs,
    Silmaril.Wasm.Logic.Core.localVal?, Silmaril.Wasm.Logic.Core.popInt, Silmaril.Wasm.Logic.Core.popV,
    Frame.local?, Frame.setLocal, Idx.toNat, IntType.width, NumType.width, extendU32,
    NumVal.mk.injEq, heq_eq_eq, Val.i32, Val.i64, bool32, cvt1, callVC, callK, corePre, paritySpec, par]

/-! ## Functions calling accessors and leaves -/

theorem Inst.Ok.at {I : Inst H} {s : Store H} (h : I.Ok s) (k : Nat) (hk : k < nCore) :
    I.mi.funcs[nImports + k]? = some (I.A k) ∧ s.funcs[I.A k]? = some (I.fi k) := h k hk

theorem Inst.Ok.keep {ρ : Rep H} (hL : ρ.Laws) {I : Inst H} {s s' : Store H} (h : I.Ok s)
    (hk : ρ.keep s s') : I.Ok s' := fun k hk' => by rw [hL.funcs s s' hk]; exact h k hk'

/-- What `I.Ok s` and the context `ks` give about defined function `k`, at function index `n`. -/
def FnAt (ρ : Rep H) (I : Inst H) (s : Store H) (ks : List Nat) (k n : Nat) : Prop :=
  I.mi.funcs[n]? = some (I.A k) ∧ s.funcs[I.A k]? = some (I.fi k) ∧
    (specsOf ρ I ks).specs (I.A k) = some (entry ρ I k) ∧
    ∃ l : I.A k < s.funcs.length, s.funcs[I.A k] = I.fi k

theorem Inst.Ok.fnAt {ρ : Rep H} {I : Inst H} {s : Store H} {ks : List Nat}
    (hks : ∀ i ∈ ks, i ∈ coreKs) (hinj : I.Inj) (h : I.Ok s) {k n : Nat} (hn : nImports + k = n)
    (hk : k < nCore) (hkm : k ∈ ks) : FnAt ρ I s ks k n := by
  obtain ⟨f, hs⟩ : I.mi.funcs[nImports + k]? = some (I.A k) ∧ s.funcs[I.A k]? = some (I.fi k) :=
    h k hk
  exact ⟨hn ▸ f, hs, specsOf_at hks hinj hkm, lt_of_getElem?_some hs,
    getElem_of_getElem?_some hs (lt_of_getElem?_some hs)⟩

/-- The context of accessors and leaves. -/
abbrev ks1 : List Nat := [0, 1, 2, 3, 4, 5, 6, 9]

theorem ks1_sub : ∀ i ∈ ks1, i ∈ coreKs := by decide

theorem tvalid1 {ρ : Rep H} {I : Inst H}
    (hacc : ∀ k ∈ [0, 1, 2, 3, 4], TFSpecAt P host (I.A k) (entry ρ I k).2)
    (h5 : TFSpecAt P host (I.A 5) (maskSpec ρ I)) (h6 : TFSpecAt P host (I.A 6) (sbitSpec ρ I))
    (h9 : TFSpecAt P host (I.A 9) (paritySpec ρ I)) : (specsOf ρ I ks1).TValid P host :=
  specsOf_tvalid ks1_sub fun k hk => by
    simp only [ks1, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact hacc _ (by decide) | exact h5 | exact h6 | exact h9

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rd_total {ρ : Rep H} {I : Inst H} {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)}
    (hΓ : (specsOf ρ I ks1).TValid P host) (hinj : I.Inj)
    (hcode : (I.fi 11).code = .wasm (fn simG 11)) (hmod : (I.fi 11).module = I.mi)
    (he : Silmaril.Wasm.Validation.Expand (I.fi 11).type (.func ps rs)) (hps : ps.length = 2)
    (hrs : rs.length = 1) :
    TFSpecAt P host (I.A 11) (rdSpec ρ I) := by
  refine @tfspec_of_wpc _ _ _ (specsOf ρ I ks1) hΓ _ _ _ _ _ _ (by simp [fn, simG, loops, ctl])
    (fun _ _ h => h.1.1) hcode he (fun _ _ h => by obtain ⟨-, r, rfl, -⟩ := h; simp [hps]) ?_
  rintro s _ ⟨⟨-, hok, hI⟩, r, rfl, hr⟩
  obtain ⟨f0, s0⟩ := hI.at 0 (by decide)
  obtain ⟨f5, s5⟩ := hI.at 5 (by decide)
  simp only [nImports] at f0 f5
  have e0 := specsOf_at (ρ := ρ) ks1_sub hinj (k := 0) (by decide)
  have e5 := specsOf_at (ρ := ρ) ks1_sub hinj (k := 5) (by decide)
  have l0 := lt_of_getElem?_some s0
  have l5 := lt_of_getElem?_some s5
  have hr17 : r.toNat < 17 := by omega
  simp [fn, simG, wpc, ctl, enterVC, labelQ, popI32, popSelect, Silmaril.Wasm.Logic.Core.exec1,
    Silmaril.Wasm.Execution.Core.ModuleInst.blockType?, Frame.forCall, fnPost, hrs,
    Silmaril.Wasm.Logic.Core.localVal?, Silmaril.Wasm.Logic.Core.popInt, Silmaril.Wasm.Logic.Core.popV,
    Frame.local?, Frame.setLocal, Idx.toNat, IntType.width, NumType.width, extendU32,
    NumVal.mk.injEq, heq_eq_eq, Val.i32, Val.i64, bool32, cvt1, callVC, callK, corePre, hmod, f0, s0, f5, s5, l0, l5, hr17,
    getElem_of_getElem?_some s0 l0, getElem_of_getElem?_some s5 l5, e0, e5, entry, rgetSpec, maskSpec, rdSpec, hok, hI, hr]


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wr_total {ρ : Rep H} (hL : ρ.Laws) {I : Inst H} {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)}
    (hΓ : (specsOf ρ I ks1).TValid P host) (hinj : I.Inj)
    (hcode : (I.fi 12).code = .wasm (fn simG 12)) (hmod : (I.fi 12).module = I.mi)
    (he : Silmaril.Wasm.Validation.Expand (I.fi 12).type (.func ps rs)) (hps : ps.length = 3)
    (hrs : rs.length = 0) :
    TFSpecAt P host (I.A 12) (wrSpec ρ I) := by
  refine @tfspec_of_wpc _ _ _ (specsOf ρ I ks1) hΓ _ _ _ _ _ _ (by simp [fn, simG, loops, ctl])
    (fun _ _ h => h.1.1) hcode he (fun _ _ h => by obtain ⟨-, r, v, rfl, -⟩ := h; simp [hps]) ?_
  rintro s args ⟨⟨-, hok, hI⟩, r, v, hargs, hr⟩
  obtain ⟨f1, s1, e1, l1, g1⟩ : FnAt ρ I s ks1 1 11 :=
    hI.fnAt ks1_sub hinj rfl (by decide) (by decide)
  obtain ⟨f5, s5, e5, l5, g5⟩ : FnAt ρ I s ks1 5 15 :=
    hI.fnAt ks1_sub hinj rfl (by decide) (by decide)
  have hr17 : r.toNat < 17 := by omega
  simp only [Func.body, fn, simG, Fin.isValue, List.length_cons, List.length_nil, zero_add,
      Nat.reduceAdd, Nat.reduceLT, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero,
      Nat.reducePow, Fin.zero_eta, Option.getD_some, hrs, wrSpec, corePre, Val.i32,
      BitVec.ofNat_eq_ofNat, Val.i64, exists_and_right, hargs, List.cons.injEq, Val.num.injEq,
      numI32_inj, numI64_inj, and_true, true_and, and_imp, forall_apply_eq_imp_iff, forall_eq',
      Frame.forCall, List.map_cons, List.map_nil, hmod, Func.locals, List.cons_append,
      List.nil_append, wpc, ctl, Wasm.Logic.Core.exec1, List.reverse_nil, Wasm.Logic.Core.localVal?,
      Frame.local?, Idx.toNat, Fin.coe_ofNat_eq_mod, Nat.one_mod, Nat.one_lt_ofNat, Option.map_some,
      List.reverse_cons, Wasm.Logic.Core.popInt, IntType.width, Wasm.Logic.Core.intRelOp_i32_geU,
      bool32, ge_iff_le, decide_eq_true_eq, NumType.width, Option.bind_some, BitVec.toNat_ofNat,
      Nat.reduceMod, popI32, ne_eq, ite_eq_right_iff, BitVec.one_eq_zero_iff, OfNat.ofNat_ne_zero,
      imp_false, not_le, hr, not_true_eq_false, enterVC, ModuleInst.blockType?, Std.le_refl,
      tsub_self, List.take_nil, Nat.zero_mod, List.reverse_reverse, List.reverse_append, zero_le,
      tsub_zero, List.take_length, callVC, List.length_reverse, callK, Wasm.Logic.Core.popV,
      Frame.setLocal, Wasm.Logic.Core.intBinOp_i64_xor, Wasm.Logic.Core.intBinOp_i64_and,
      Wasm.Logic.Core.intBinOp_i64_or, fnPost, List.length_append, List.length_take,
      tsub_le_iff_right, le_add_iff_nonneg_right, inf_of_le_left, Nat.add_eq_zero_iff,
      List.length_eq_zero_iff, Wasm.Logic.Core.Outcome.normal.injEq, List.append_eq_nil_iff,
      List.take_eq_nil_iff, List.reverse_eq_nil_iff, reduceCtorEq, false_and, List.drop_length,
      labelQ, List.drop_length_add_append, List.drop_eq_nil_iff, List.append_nil, List.drop_nil,
      Wasm.Logic.Core.intBinOp_i32_sub, ↓reduceIte, List.set_cons_succ, List.set_cons_zero,
      List.append_assoc, Wasm.Logic.Core.intBinOp_i64_shl, IsEmpty.forall_iff, Nat.ofNat_pos,
      Nat.reduceLeDiff, not_false_eq_true, f5, e5, entry, maskSpec, BitVec.reduceAllOnes,
      Nat.one_le_ofNat, l5, g5, hok, hI, and_self, Nat.add_one_sub_one, List.drop_succ_cons,
      List.drop_zero, List.take_succ_cons, List.take_zero, forall_eq_apply_imp_iff,
      Wasm.Logic.VC.and_ones64, f1, e1, rsetSpec, exists_and_left, ↓existsAndEq, exists_eq_left',
      hr17, forall_eq, l1, g1, forall_const, Nat.lt_add_one, BitVec.xor_self, BitVec.and_zero]
  intro s' h1 h2 h3
  exact ⟨h1, hI.keep hL h3, h3, h2⟩


theorem par_lt (r : BitVec 64) : (par r).toNat < 2 := by
  unfold par; split <;> decide

@[simp] theorem ite_one_zero_lt (c : Prop) [Decidable c] : (if c then 1#32 else 0#32).toNat < 2 := by
  split <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fres_total {ρ : Rep H} (hL : ρ.Laws) {I : Inst H} {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)}
    (hΓ : (specsOf ρ I ks1).TValid P host) (hinj : I.Inj)
    (hcode : (I.fi 10).code = .wasm (fn simG 10)) (hmod : (I.fi 10).module = I.mi)
    (he : Silmaril.Wasm.Validation.Expand (I.fi 10).type (.func ps rs)) (hps : ps.length = 5)
    (hrs : rs.length = 0) :
    TFSpecAt P host (I.A 10) (fresSpec ρ I) := by
  refine @tfspec_of_wpc _ _ _ (specsOf ρ I ks1) hΓ _ _ _ _ _ _ (by simp [fn, simG, loops, ctl])
    (fun _ _ h => h.1.1) hcode he
    (fun _ _ h => by obtain ⟨-, r, cf, af, of, rfl, -⟩ := h; simp [hps]) ?_
  rintro s args ⟨⟨-, hok, hI⟩, r, cf, af, of, hargs, hcf, haf, hof⟩
  obtain ⟨f4, s4, e4, l4, g4⟩ : FnAt ρ I s ks1 4 14 :=
    hI.fnAt ks1_sub hinj rfl (by decide) (by decide)
  obtain ⟨f6, s6, e6, l6, g6⟩ : FnAt ρ I s ks1 6 16 :=
    hI.fnAt ks1_sub hinj rfl (by decide) (by decide)
  obtain ⟨f9, s9, e9, l9, g9⟩ : FnAt ρ I s ks1 9 19 :=
    hI.fnAt ks1_sub hinj rfl (by decide) (by decide)
  have hp : (par r).toNat < 2 := par_lt r
  simp only [Func.body, fn, simG, Fin.isValue, List.length_cons, List.length_nil, zero_add,
      Nat.reduceAdd, Nat.reduceLT, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero,
      Nat.reducePow, Fin.zero_eta, Option.getD_some, hrs, fresSpec, corePre, Val.i32,
      BitVec.ofNat_eq_ofNat, Val.i64, hargs, List.cons.injEq, Val.num.injEq, numI64_inj, numI32_inj,
      and_true, true_and, and_imp, Frame.forCall, List.map_cons, List.map_nil, hmod, Func.locals,
      List.append_nil, wpc, ctl, Wasm.Logic.Core.exec1, List.reverse_nil, Wasm.Logic.Core.localVal?,
      Frame.local?, Idx.toNat, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Option.map_some,
      List.reverse_cons, List.nil_append, Nat.one_mod, Nat.one_lt_ofNat, List.cons_append, callVC,
      f9, e9, entry, paritySpec, Nat.one_le_ofNat, l9, g9, hok, hI, and_self, Nat.add_one_sub_one,
      List.drop_succ_cons, List.drop_zero, exists_eq', forall_eq', callK, List.take_succ_cons,
      List.take_zero, List.reverse_append, List.reverse_reverse, List.append_assoc, IntType.width,
      eqz64, Wasm.Logic.Core.popInt, Nat.zero_mod, Nat.ofNat_pos, f6, e6, sbitSpec,
      List.length_append, le_add_iff_nonneg_left, zero_le, add_tsub_cancel_right,
      List.drop_length_add_append, NumType.width, Wasm.Logic.Core.intBinOp_i64_and, ne64,
      Option.bind_some, List.length_reverse, fnPost, List.length_take, tsub_le_iff_right,
      le_add_iff_nonneg_right, inf_of_le_left, Nat.add_eq_zero_iff, List.length_eq_zero_iff,
      Wasm.Logic.Core.Outcome.normal.injEq, List.append_eq_nil_iff, List.take_eq_nil_iff,
      List.reverse_eq_nil_iff, reduceCtorEq, false_and, imp_false, forall_eq_apply_imp_iff,
      forall_eq, Nat.lt_add_one, f4, e4, fset6Spec, Std.le_refl, tsub_self, ↓existsAndEq, hof,
      ite_one_zero_lt, haf, hp, exists_eq_left', hcf, or_false, l6, g6, l4, g4]
  refine ⟨by repeat' (first | apply And.intro | (split <;> decide) | exact Nat.mod_lt _ (by decide)), fun s' o h => ?_⟩
  obtain ⟨rfl, h1, h2, h3⟩ := h _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
  have hI' : I.Ok s' := hI.keep hL h3
  simp only [h1, hI', h3, h2, zfOf, sfOf, true_and]
  rintro _ _ _ _ rfl rfl rfl rfl
  rfl

/-- The context of accessors, leaves and `fres`/`rd`/`wr`. -/
abbrev ks2 : List Nat := [0, 1, 2, 3, 4, 5, 6, 9, 10, 11, 12]

theorem ks2_sub : ∀ i ∈ ks2, i ∈ coreKs := by decide


alu_case alu_vc_add 0
alu_case alu_vc_sub 5
alu_case alu_vc_cmp 7

set_option maxRecDepth 100000 in
theorem alu_total {ρ : Rep H} {I : Inst H} {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)}
    (hΓ : (specsOf ρ I ks2).TValid P host) (hinj : I.Inj)
    (hcode : (I.fi 17).code = .wasm (fn simG 17)) (hmod : (I.fi 17).module = I.mi)
    (he : Silmaril.Wasm.Validation.Expand (I.fi 17).type (.func ps rs)) (hps : ps.length = 4)
    (hrs : rs.length = 1) :
    TFSpecAt P host (I.A 17) (aluSpec ρ I) := by
  refine @tfspec_of_wpc _ _ _ (specsOf ρ I ks2) hΓ _ _ _ _ _ _ (by simp [fn, simG, loops, ctl])
    (fun _ _ h => h.1.1) hcode he
    (fun _ _ h => by obtain ⟨-, op, a, b, rfl, -⟩ := h; simp [hps]) ?_
  rintro s args ⟨⟨-, hok, hI⟩, op, a, b, hargs, hop⟩
  rcases hop with rfl | rfl | rfl
  · exact alu_vc_add hinj hmod hrs s hok hI a b args hargs
  · exact alu_vc_sub hinj hmod hrs s hok hI a b args hargs
  · exact alu_vc_cmp hinj hmod hrs s hok hI a b args hargs


/-- The context for `i_alu_rr`. -/
abbrev ks3 : List Nat := [0, 1, 2, 3, 4, 5, 6, 9, 10, 11, 12, 17]

theorem ks3_sub : ∀ i ∈ ks3, i ∈ coreKs := by decide


alu_rr_case alu_rr_vc_add 0
alu_rr_case alu_rr_vc_sub 5
alu_rr_case alu_rr_vc_cmp 7

set_option maxRecDepth 100000 in
theorem iAluRR_total {ρ : Rep H} (hL : ρ.Laws) {I : Inst H}
    {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)}
    (hΓ : (specsOf ρ I ks3).TValid P host) (hinj : I.Inj)
    (hcode : (I.fi 42).code = .wasm (fn simG 42)) (hmod : (I.fi 42).module = I.mi)
    (he : Silmaril.Wasm.Validation.Expand (I.fi 42).type (.func ps rs)) (hps : ps.length = 4)
    (hrs : rs.length = 0) :
    TFSpecAt P host (I.A 42) (iAluRRSpec ρ I) := by
  refine @tfspec_of_wpc _ _ _ (specsOf ρ I ks3) hΓ _ _ _ _ _ _ (by simp [fn, simG, loops, ctl])
    (fun _ _ h => h.1.1) hcode he
    (fun _ _ h => by obtain ⟨-, op, d, r, rfl, -⟩ := h; simp [hps]) ?_
  rintro s args ⟨⟨-, hok, hI⟩, op, d, r, hargs, hop, hd, hr⟩
  rcases hop with rfl | rfl | rfl
  · exact alu_rr_vc_add hL hinj hmod hrs s hok hI d r hd hr args hargs
  · exact alu_rr_vc_sub hL hinj hmod hrs s hok hI d r hd hr args hargs
  · exact alu_rr_vc_cmp hL hinj hmod hrs s hok hI d r hd hr args hargs


end Silmaril.Sim.X86Real
