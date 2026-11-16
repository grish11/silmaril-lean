import Silmaril.Proofs.Sim.X86.Max2.State
import Silmaril.Wasm.Logic.VCCalls.Thms

/-!
# The `max2` problem: verification conditions of the functions

One theorem per function of `max2M` on `max2`'s path (`*_vc`): the generator's condition `wpc`
for the body, with the specification of `Silmaril.Sim.X86.Max2.specOf` as postcondition and the
callees' specifications (`ctxBelow`) for the calls, from the precondition. Each is closed by
`wat_vc` over a symbolic store (globals by `globalVal`/`setGlobalIdx`, memory by `memB`), plus
at most one line (`fget`/`fset`: the `br_table` index; `f_400005`: the store invariant and the
signed comparison from SF/OF, `msb_and`, `slt_flags`).

Not a `module`: in the module system the kernel rejects the proof term `simp` builds for the
calls of `cond_vc` (an application type mismatch the elaborator accepts; not investigated
further), so this file and `Silmaril.Sim.X86.Max2.Thms` are ordinary Lean files.
-/

namespace Silmaril.Sim.X86.Max2

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.VC Silmaril.Wasm.Logic.Core

variable {H : Type} {mi : ModuleInst} {ma : Nat} {mt : MemoryType} {fis : Nat → FuncInst H}

/-- No loop invariants. -/
abbrev noInv : Invs H := fun _ _ _ _ => True

theorem ctxBelow_specs (n a : Nat) : (ctxBelow mi ma mt fis n).specs a =
    if a < n then specOf mi ma mt fis a else none := rfl

set_option maxRecDepth 10000

set_option hygiene false in
/-- The call lemma (`Silmaril.Wasm.Logic.VC.callVC_fn`) for a call of address `k` from function `n`:
the callee's specification `specOf k` in the context `ctxBelow n`. Needs `hf` in scope. Scoped
to `Silmaril.Sim.X86.Max2` (also used by `Silmaril.Proofs.Sim.X86.Max2.Main`). -/
scoped macro "vc_call" n:num k:num : term =>
  `(callVC_fn (Γ := ctxBelow mi ma mt fis $n) (m := mi) (x := ⟨$k⟩) (a := $k) (by rw [hf]; rfl) rfl
    (fun _ _ _ _ => Iff.rfl))

theorem rget_vc (s : Store H) (args : List Val) (hpre : (sRget mi ma mt fis).pre s args) :
    wpc (Γ := ctxBelow mi ma mt fis 5) noInv 0 max2M.funcs[3].body (fnPost 1 ((sRget mi ma mt fis).post s args)) s
      (Frame.forCall mi args max2M.funcs[3].locals) [] := by
  obtain ⟨hG, r, rfl, hr⟩ := hpre
  wat_vc [max2M, fnPost, sRget, pureSpec, a32, globalVal_R hG]

theorem rset_vc (s : Store H) (args : List Val) (hpre : (sRset mi ma mt fis).pre s args) :
    wpc (Γ := ctxBelow mi ma mt fis 6) noInv 0 max2M.funcs[4].body (fnPost 0 ((sRset mi ma mt fis).post s args)) s
      (Frame.forCall mi args max2M.funcs[4].locals) [] := by
  obtain ⟨hG, r, v, rfl, hr⟩ := hpre
  wat_vc [max2M, fnPost, sRset, procSpec, a32, a64, globalVal_R hG]

theorem fget_vc (s : Store H) (args : List Val) (hpre : (sFget mi ma mt fis).pre s args) :
    wpc (Γ := ctxBelow mi ma mt fis 7) noInv 0 max2M.funcs[5].body (fnPost 1 ((sFget mi ma mt fis).post s args)) s
      (Frame.forCall mi args max2M.funcs[5].locals) [] := by
  obtain ⟨hG, r, rfl, hr, hr'⟩ := hpre
  wat_vc [max2M, fnPost, sFget, pureSpec, a32, globalVal_Fl hG]
  all_goals (congr 1; omega)

theorem fset_vc (s : Store H) (args : List Val) (hpre : (sFset mi ma mt fis).pre s args) :
    wpc (Γ := ctxBelow mi ma mt fis 8) noInv 0 max2M.funcs[6].body (fnPost 0 ((sFset mi ma mt fis).post s args)) s
      (Frame.forCall mi args max2M.funcs[6].locals) [] := by
  obtain ⟨hG, r, v, rfl, hr, hr'⟩ := hpre
  wat_vc [max2M, fnPost, sFset, procSpec, a32, globalVal_Fl hG]
  all_goals (congr 1; omega)

theorem fset6_vc (hnd : mi.globals.Nodup) (s : Store H) (args : List Val) (hpre : (sFset6 mi ma mt fis).pre s args) :
    wpc (Γ := ctxBelow mi ma mt fis 9) noInv 0 max2M.funcs[7].body (fnPost 0 ((sFset6 mi ma mt fis).post s args)) s
      (Frame.forCall mi args max2M.funcs[7].locals) [] := by
  obtain ⟨hG, c, p, a, z, sg, o, rfl⟩ := hpre
  wat_vc [max2M, fnPost, sFset6, procSpec, a32, set6, globalVal_Fl hG, globalVal_setGlobalIdx_ne hnd,
    good_isSome hG]

theorem mask_vc (s : Store H) (args : List Val) (hpre : (sMask mi ma mt fis).pre s args) :
    wpc (Γ := ctxBelow mi ma mt fis 10) noInv 0 max2M.funcs[8].body (fnPost 1 ((sMask mi ma mt fis).post s args)) s
      (Frame.forCall mi args max2M.funcs[8].locals) [] := by
  obtain ⟨hG, rfl⟩ := hpre
  wat_vc [max2M, fnPost, sMask, pureSpec]

theorem sbit_vc (s : Store H) (args : List Val) (hpre : (sSbit mi ma mt fis).pre s args) :
    wpc (Γ := ctxBelow mi ma mt fis 11) noInv 0 max2M.funcs[9].body (fnPost 1 ((sSbit mi ma mt fis).post s args)) s
      (Frame.forCall mi args max2M.funcs[9].locals) [] := by
  obtain ⟨hG, rfl⟩ := hpre
  wat_vc [max2M, fnPost, sSbit, pureSpec]

theorem off_vc (s : Store H) (args : List Val) (hpre : (sOff mi ma mt fis).pre s args) :
    wpc (Γ := ctxBelow mi ma mt fis 2) noInv 0 max2M.funcs[0].body (fnPost 1 ((sOff mi ma mt fis).post s args)) s
      (Frame.forCall mi args max2M.funcs[0].locals) [] := by
  obtain ⟨hG, x, n, rfl, h1, h2⟩ := hpre
  wat_vc [max2M, fnPost, sOff, pureSpec, a64]

theorem off_toNat {x : BitVec 64} (h1 : 1048576 ≤ x.toNat) (h2 : x.toNat ≤ 1114112) :
    (BitVec.setWidth 32 (x - 1048576#64)).toNat = x.toNat - 1048576 := by
  bv_omega

theorem load64_vc (hm : mi.mems[0]? = some ma) (hf : mi.funcs = List.range 29) (s : Store H) (args : List Val)
    (hpre : (sLoad64 mi ma mt fis).pre s args) :
    wpc (Γ := ctxBelow mi ma mt fis 3) noInv 0 max2M.funcs[1].body (fnPost 1 ((sLoad64 mi ma mt fis).post s args)) s
      (Frame.forCall mi args max2M.funcs[1].locals) [] := by
  obtain ⟨hG, x, rfl, h1, h2⟩ := hpre
  have hsz := hG.size
  wat_vc_calls [↓vc_call 3 2,
    max2M, fnPost, sLoad64, sOff, pureSpec, a64, ctxBelow_specs, specOf, hm, InWin, mem?_good hG hm,
    load_ite, effAddr, IntType.width, off_toNat h1 (by omega), ld64, show x.toNat - 1048576 + 8 ≤ (memB s ma).size by omega]

theorem store64_vc (hm : mi.mems[0]? = some ma) (hf : mi.funcs = List.range 29) (s : Store H) (args : List Val)
    (hpre : (sStore64 mi ma mt fis).pre s args) :
    wpc (Γ := ctxBelow mi ma mt fis 4) noInv 0 max2M.funcs[2].body (fnPost 0 ((sStore64 mi ma mt fis).post s args)) s
      (Frame.forCall mi args max2M.funcs[2].locals) [] := by
  obtain ⟨hG, x, v, rfl, h1, h2⟩ := hpre
  have hsz := hG.size
  wat_vc_calls [↓vc_call 4 2,
    max2M, fnPost, sStore64, sOff, pureSpec, procSpec, a64, ctxBelow_specs, specOf, hm, InWin, mem?_good hG hm,
    store_ite, effAddr, IntType.width, off_toNat h1 (by omega), show x.toNat - 1048576 + 8 ≤ (memB s ma).size by omega]

theorem parity_vc (s : Store H) (args : List Val) (hpre : (sParity mi ma mt fis).pre s args) :
    wpc (Γ := ctxBelow mi ma mt fis 13) noInv 0 max2M.funcs[11].body (fnPost 1 ((sParity mi ma mt fis).post s args)) s
      (Frame.forCall mi args max2M.funcs[11].locals) [] := by
  obtain ⟨hG, r, rfl⟩ := hpre
  wat_vc [max2M, fnPost, sParity, pureSpec, a64, par]

theorem fres_vc (hf : mi.funcs = List.range 29) (s : Store H) (args : List Val) (hpre : (sFres mi ma mt fis).pre s args) :
    wpc (Γ := ctxBelow mi ma mt fis 14) noInv 0 max2M.funcs[12].body (fnPost 0 ((sFres mi ma mt fis).post s args)) s
      (Frame.forCall mi args max2M.funcs[12].locals) [] := by
  obtain ⟨hG, r, cf, af, of, rfl⟩ := hpre
  wat_vc_calls [↓vc_call 14 9, ↓vc_call 14 11, ↓vc_call 14 13,
    max2M, fnPost, sFres, sFset6, sParity, sSbit, pureSpec, procSpec, a64, a32, fresEff, ctxBelow_specs, specOf, hf, hG]

theorem rd_vc (hf : mi.funcs = List.range 29) (s : Store H) (args : List Val) (hpre : (sRd mi ma mt fis).pre s args) :
    wpc (Γ := ctxBelow mi ma mt fis 15) noInv 0 max2M.funcs[13].body (fnPost 1 ((sRd mi ma mt fis).post s args)) s
      (Frame.forCall mi args max2M.funcs[13].locals) [] := by
  obtain ⟨hG, r, rfl, hr⟩ := hpre
  wat_vc_calls [↓vc_call 15 5, ↓vc_call 15 10,
    max2M, fnPost, sRd, sRget, sMask, pureSpec, a32, ctxBelow_specs, specOf, hf, hG]

theorem wr_vc (hf : mi.funcs = List.range 29) (s : Store H) (args : List Val) (hpre : (sWr mi ma mt fis).pre s args) :
    wpc (Γ := ctxBelow mi ma mt fis 16) noInv 0 max2M.funcs[14].body (fnPost 0 ((sWr mi ma mt fis).post s args)) s
      (Frame.forCall mi args max2M.funcs[14].locals) [] := by
  obtain ⟨hG, r, v, rfl, hr⟩ := hpre
  wat_vc_calls [↓vc_call 16 5, ↓vc_call 16 6, ↓vc_call 16 10,
    max2M, fnPost, sWr, sRget, sRset, sMask, pureSpec, procSpec, a32, a64, ctxBelow_specs, specOf, hf, hG]

theorem cond_vc (hf : mi.funcs = List.range 29) (s : Store H) (args : List Val) (hpre : (sCond mi ma mt fis).pre s args) :
    wpc (Γ := ctxBelow mi ma mt fis 17) noInv 0 max2M.funcs[15].body (fnPost 1 ((sCond mi ma mt fis).post s args)) s
      (Frame.forCall mi args max2M.funcs[15].locals) [] := by
  obtain ⟨hG, rfl⟩ := hpre
  wat_vc_calls [↓vc_call 17 7,
    max2M, fnPost, sCond, sFget, pureSpec, a32, ctxBelow_specs, specOf, hf, hG]

theorem alu_vc (hf : mi.funcs = List.range 29) (s : Store H) (args : List Val) (hpre : (sAlu mi ma mt fis).pre s args) :
    wpc (Γ := ctxBelow mi ma mt fis 18) noInv 0 max2M.funcs[16].body (fnPost 1 ((sAlu mi ma mt fis).post s args)) s
      (Frame.forCall mi args max2M.funcs[16].locals) [] := by
  obtain ⟨hG, a, b, rfl⟩ := hpre
  wat_vc_calls [↓vc_call 18 7, ↓vc_call 18 10, ↓vc_call 18 11, ↓vc_call 18 14,
    max2M, fnPost, sAlu, fnSpec, sFres, sMask, sSbit, pureSpec, procSpec, a32, a64, cmpEff, ctxBelow_specs, specOf, hf, hG]

theorem pop_vc (_hnd : mi.globals.Nodup) (hf : mi.funcs = List.range 29) (s : Store H) (args : List Val) (hpre : (sPop mi ma mt fis).pre s args) :
    wpc (Γ := ctxBelow mi ma mt fis 19) noInv 0 max2M.funcs[17].body (fnPost 1 ((sPop mi ma mt fis).post s args)) s
      (Frame.forCall mi args max2M.funcs[17].locals) [] := by
  obtain ⟨hG, rfl, hw⟩ := hpre
  wat_vc_calls [↓vc_call 19 3, ↓vc_call 19 5, ↓vc_call 19 6,
    max2M, fnPost, sPop, fnSpec, sLoad64, sRget, sRset, pureSpec, procSpec, a32, a64, ctxBelow_specs, specOf, hf, hG, InWin, hw,
    R_set_self hG, good_setR _hnd]

theorem get_vc (hf : mi.funcs = List.range 29) (s : Store H) (args : List Val) (hpre : (sGet mi ma mt fis).pre s args) :
    wpc (Γ := ctxBelow mi ma mt fis 20) noInv 0 max2M.funcs[18].body (fnPost 1 ((sGet mi ma mt fis).post s args)) s
      (Frame.forCall mi args max2M.funcs[18].locals) [] := by
  obtain ⟨hG, l, rfl, hl⟩ := hpre
  wat_vc_calls [↓vc_call 20 5, ↓vc_call 20 7,
    max2M, fnPost, sGet, sRget, pureSpec, a32, ctxBelow_specs, specOf, hf, hG]

theorem set_vc (hf : mi.funcs = List.range 29) (s : Store H) (args : List Val) (hpre : (sSet mi ma mt fis).pre s args) :
    wpc (Γ := ctxBelow mi ma mt fis 21) noInv 0 max2M.funcs[19].body (fnPost 0 ((sSet mi ma mt fis).post s args)) s
      (Frame.forCall mi args max2M.funcs[19].locals) [] := by
  obtain ⟨hG, l, v, rfl, hl⟩ := hpre
  wat_vc_calls [↓vc_call 21 6, ↓vc_call 21 8,
    max2M, fnPost, sSet, sRset, procSpec, a32, a64, ctxBelow_specs, specOf, hf, hG]

theorem next_vc (hf : mi.funcs = List.range 29) (s : Store H) (args : List Val) (hpre : (sNext mi ma mt fis).pre s args) :
    wpc (Γ := ctxBelow mi ma mt fis 22) noInv 0 max2M.funcs[20].body (fnPost 0 ((sNext mi ma mt fis).post s args)) s
      (Frame.forCall mi args max2M.funcs[20].locals) [] := by
  obtain ⟨hG, n, rfl⟩ := hpre
  wat_vc_calls [↓vc_call 22 5, ↓vc_call 22 6,
    max2M, fnPost, sNext, sRget, sRset, pureSpec, procSpec, a32, a64, ctxBelow_specs, specOf, hf, hG]

theorem mov_vc (hf : mi.funcs = List.range 29) (s : Store H) (args : List Val) (hpre : (sMovRR mi ma mt fis).pre s args) :
    wpc (Γ := ctxBelow mi ma mt fis 23) noInv 0 max2M.funcs[21].body (fnPost 0 ((sMovRR mi ma mt fis).post s args)) s
      (Frame.forCall mi args max2M.funcs[21].locals) [] := by
  obtain ⟨hG, d, r, rfl, hd, hr⟩ := hpre
  wat_vc_calls [↓vc_call 23 15, ↓vc_call 23 16,
    max2M, fnPost, sMovRR, sRd, sWr, pureSpec, procSpec, a32, a64, ctxBelow_specs, specOf, hf, hG]

theorem aluRR_vc (hf : mi.funcs = List.range 29) (s : Store H) (args : List Val) (hpre : (sAluRR mi ma mt fis).pre s args) :
    wpc (Γ := ctxBelow mi ma mt fis 24) noInv 0 max2M.funcs[22].body (fnPost 0 ((sAluRR mi ma mt fis).post s args)) s
      (Frame.forCall mi args max2M.funcs[22].locals) [] := by
  obtain ⟨hG, d, r, rfl, hd, hr⟩ := hpre
  wat_vc_calls [↓vc_call 24 15, ↓vc_call 24 16, ↓vc_call 24 18,
    max2M, fnPost, sAluRR, sAlu, fnSpec, sRd, sWr, pureSpec, procSpec, a32, a64, ctxBelow_specs, specOf, hf, hG]

theorem ret_vc (hnd : mi.globals.Nodup) (hf : mi.funcs = List.range 29) (s : Store H) (args : List Val)
    (hpre : (sRet mi ma mt fis).pre s args) :
    wpc (Γ := ctxBelow mi ma mt fis 25) noInv 0 max2M.funcs[23].body (fnPost 0 ((sRet mi ma mt fis).post s args)) s
      (Frame.forCall mi args max2M.funcs[23].locals) [] := by
  obtain ⟨hG, rfl, hw⟩ := hpre
  wat_vc_calls [↓vc_call 25 6, ↓vc_call 25 19,
    max2M, fnPost, sRet, sPop, fnSpec, sRset, pureSpec, procSpec, a32, a64, ctxBelow_specs, specOf, hf, hG, hw,
    good_setR hnd]

theorem cmov_vc (hf : mi.funcs = List.range 29) (s : Store H) (args : List Val) (hpre : (sCmovRR mi ma mt fis).pre s args) :
    wpc (Γ := ctxBelow mi ma mt fis 26) noInv 0 max2M.funcs[24].body (fnPost 0 ((sCmovRR mi ma mt fis).post s args)) s
      (Frame.forCall mi args max2M.funcs[24].locals) [] := by
  obtain ⟨hG, d, r, rfl, hd, hr⟩ := hpre
  wat_vc_calls [↓vc_call 26 15, ↓vc_call 26 16, ↓vc_call 26 17,
    max2M, fnPost, sCmovRR, sCond, sRd, sWr, pureSpec, procSpec, a32, a64, ctxBelow_specs, specOf, hf, hG]

set_option maxHeartbeats 1000000 in
theorem prog_vc (hnd : mi.globals.Nodup) (hf : mi.funcs = List.range 29) (s : Store H) (args : List Val)
    (hpre : (sProg mi ma mt fis).pre s args) :
    wpc (Γ := ctxBelow mi ma mt fis 27)
      (fun _ s' f' a => s' = s ∧ a = [] ∧ f' = { locals := [some (Val.i32 0), some (Val.i32 0)], module := mi })
      0 max2M.funcs[25].body (fnPost 1 ((sProg mi ma mt fis).post s args)) s
      (Frame.forCall mi args max2M.funcs[25].locals) [] := by
  obtain ⟨hG, rfl, hw⟩ := hpre
  wat_vc_calls [↓vc_call 27 22, ↓vc_call 27 23, ↓vc_call 27 24, ↓vc_call 27 25, ↓vc_call 27 26,
    max2M, fnPost, sProg, sMovRR, sNext, sAluRR, sCmovRR, sRet, fnSpec, procSpec, a32, a64,
    ctxBelow_specs, specOf, hf, hG, hw, good_setR hnd, good_cmpEff hnd, R_set_ne hnd, R_cmpEff hnd,
    Fl_cmpEff_21 hnd, Fl_cmpEff_22, R_set_self', Fl_set_ne hnd, good_isSome hG]
  all_goals (simp_all [msb_and, slt_flags])

end Silmaril.Sim.X86.Max2
