module

public import Silmaril.Wasm.Cfg.Bridge.Thms
public import Silmaril.Wasm.Cfg.MachineLProj.Defs
public import Silmaril.Wasm.Abstract.CallXP.Thms
public import Silmaril.Wasm.Abstract.CallXE.Thms
public import Silmaril.Wasm.Abstract.CallXT.Thms
public import Silmaril.Wasm.Interp.EHExt.Thms
import Silmaril.Proofs.Wasm.Cfg.MachineLClosed
import Silmaril.Proofs.Wasm.Cfg.MachineLBwd

@[expose] public section

/-!
# Logged straight-line code is a region run (proofs)

`seg_runC`: a logged native run of straight-line code (no terminators, no indirect or reference
calls) whose calls are answers of a sound oracle `C`, checked with exceptions on, is a region run
(`Region.RunC`) of the code with the same oracle, ending as `ResOut` says. It composes
`MachineLClosed.logged_closed`, `CallXP.evalOXP_iff_evalOXE`, `CallXE.evalOXE_iff_evalOX`,
`CallXT.evalOXT_iff_evalOX` and `Bridge.bridge_fwd`; the check moves from `ehExt` to `tExt`, as
the code has no exception forms (`chkE_flat_tExt`).
-/

namespace Silmaril.Wasm.Cfg.Proofs.MachineLProjS

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen Silmaril.Wasm.Interp
open Silmaril.Wasm.Abstract (SCall CallRel)

variable {H : Type}

theorem liftInstr_flat {i : Instr} (h : isTerminator i = false) : liftInstr i = .op i [] := by
  cases i <;> first | rfl | simp [isTerminator] at h

theorem xFreeL_flat : ∀ {is : List Instr}, Flat is → Abstract.CallX.xFreeL (liftInstrs is) = true
  | [], _ => rfl
  | i :: is, h => by
    have hi := h i (by simp)
    simp only [liftInstrs, Abstract.CallX.xFreeL, liftInstr_flat hi.1, Abstract.CallX.xFree, hi.2,
      Bool.not_false, Bool.true_and]
    exact xFreeL_flat (fun j hj => h j (List.mem_cons_of_mem _ hj))

theorem ehFreeL_flat : ∀ {is : List Instr}, Flat is → Abstract.CallXE.ehFreeL (liftInstrs is) = true
  | [], _ => rfl
  | i :: is, h => by
    have hi := h i (by simp)
    have heh : Abstract.CallXE.ehInstr i = false := by
      cases i <;> first | rfl | simp [isTerminator] at hi
    simp only [liftInstrs, Abstract.CallXE.ehFreeL, liftInstr_flat hi.1, Abstract.CallXE.ehFree, heh,
      Bool.not_false, Bool.true_and]
    exact ehFreeL_flat (fun j hj => h j (List.mem_cons_of_mem _ hj))

theorem irFreeL_flat : ∀ {is : List Instr}, Flat is → Abstract.CallXT.irFreeL (liftInstrs is) = true
  | [], _ => rfl
  | i :: is, h => by
    have hi := h i (by simp)
    have hir : Abstract.CallXT.irCall i = false := by
      cases i <;> first | rfl | simp [Abstract.CallX.isXCall] at hi
    simp only [liftInstrs, Abstract.CallXT.irFreeL, liftInstr_flat hi.1, Abstract.CallXT.irFree, hir,
      Bool.not_false, Bool.true_and]
    exact irFreeL_flat (fun j hj => h j (List.mem_cons_of_mem _ hj))

theorem flatChkE_eh {tags : List TagInst} {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
    {labels : List Nat} {h : Nat} {i : Instr} (hi : isTerminator i = false) :
    flatChkE (ehExt tags) F mi nl ret labels h i = flatChkE tExt F mi nl ret labels h i := by
  cases i <;> first | rfl | simp [isTerminator] at hi

/-- **Off the exception forms the check is `tExt`'s.** -/
theorem chkE_flat_tExt {tags : List TagInst} {F : List (FuncInst H)} {mi : ModuleInst}
    {nl ret : Nat} {labels : List Nat} :
    ∀ {is : List Instr} (oh : Option Nat), (∀ i ∈ is, isTerminator i = false) →
      chkE (ehExt tags) F mi nl ret labels oh (liftInstrs is) =
        chkE tExt F mi nl ret labels oh (liftInstrs is)
  | _, none, _ => by cases ‹List Instr› <;> rfl
  | [], some _, _ => rfl
  | i :: is, some k, h => by
    have hi := h i (by simp)
    simp only [liftInstrs, liftInstr_flat hi, chkE, chk1E, Option.bind_some]
    rw [flatChkE_eh hi]
    cases flatChkE tExt F mi nl ret labels k i with
    | none => rfl
    | some o =>
      simp only [Option.bind_some]
      exact chkE_flat_tExt o (fun j hj => h j (List.mem_cons_of_mem _ hj))

/-- **Logged straight-line code is a region run** with the same oracle, ending as `ResOut` says,
when its calls are answers of a sound oracle and it passes the check with exceptions on. -/
theorem seg_runC {P P₀ : Numerics.Profile} {host host₀ : HostSemantics H} {C : CallRel H}
    (hC : OracleSoundT P₀ host₀ C) {tags : List TagInst} {is : List Instr} (hflat : Flat is)
    {s : Store H} {f : Frame} {N : List Val} {l : List (SCall H)}
    {r : Store H × Frame × Abstract.CallXP.POut} (hr : Abstract.EvalLXPS s f N (liftInstrs is) l r)
    (hl : ∀ e ∈ l, CloseOk C e) (hS : StoreChkE tExt s.funcs) {labels : List Nat} {ret : Nat}
    {out : Option Nat}
    (hchk : chkE (ehExt tags) s.funcs f.module f.locals.length ret labels (some N.length)
      (liftInstrs is) = some out) :
    ∃ (s₂ : Store H) (f₂ : Frame) (fl : Flow), r = (s₂, f₂, .flow fl) ∧
      ∃ s' f' o, Region.RunC P host C s f N.reverse (expression is) s' f' o ∧
        Bridge.ResOut C s' f' o (s₂, f₂, fl) := by
  have d := Proofs.MachineLClosed.logged_closed hr hl
  have hx := xFreeL_flat hflat
  obtain ⟨s₂, f₂, o⟩ := r
  cases o with
  | tail a args n => exact absurd d (Abstract.CallXP.evalOXP_not_tail hx)
  | flow fl =>
    refine ⟨s₂, f₂, fl, rfl, ?_⟩
    have hox := (Abstract.CallXE.evalOXE_iff_evalOX (ehFreeL_flat hflat)).1
      ((Abstract.CallXP.evalOXP_iff_evalOXE hx).1 d)
    have hot := (Abstract.CallXT.evalOXT_iff_evalOX (irFreeL_flat hflat)).2 hox
    have hchk' := (chkE_flat_tExt _ (fun i hi => (hflat i hi).1)).symm.trans hchk
    obtain ⟨s', f', o, hrun, hres⟩ := Bridge.bridge_fwd (P := P) (host := host) hC hot hS hchk'
    rw [lowerList_liftInstrs] at hrun
    exact ⟨s', f', o, hrun, hres⟩

/-- **Segment bodies are straight-line code** when the body makes direct calls only. -/
theorem seg_flat {body : Expr} (hD : DirectCalls body) {p : List SeqStep} {c : List Instr}
    {i : Nat} {sg : Segment} (hc : seqAt body p = some c) (hsg : (segment c)[i]? = some sg) :
    Flat sg.body :=
  fun x hx => ⟨(MachineLBwd.seg_wf hsg).1 x hx, hD p c i sg hc hsg x hx⟩

end Silmaril.Wasm.Cfg.Proofs.MachineLProjS
