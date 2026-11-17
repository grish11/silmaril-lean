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

/-- **A plain instruction**: lifted to a single tree (not structured), not an exception form, not
an extended call form. Straight-line code is plain, and so are the terminators `br`, `br_if`,
`br_table`, `br_on_*`, `return` and `unreachable`. -/
def PlainI (i : Instr) : Prop :=
  liftInstr i = .op i [] ∧ Abstract.CallXE.ehInstr i = false ∧ Abstract.CallX.isXCall i = false

/-- Plain code. -/
def Plain (is : List Instr) : Prop := ∀ i ∈ is, PlainI i

theorem plainI_of_flat {i : Instr} (h₁ : isTerminator i = false)
    (h₂ : Abstract.CallX.isXCall i = false) : PlainI i := by
  refine ⟨liftInstr_flat h₁, ?_, h₂⟩
  cases i <;> first | rfl | simp [isTerminator] at h₁

theorem plain_of_flat {is : List Instr} (h : Flat is) : Plain is :=
  fun i hi => plainI_of_flat (h i hi).1 (h i hi).2

theorem plain_append {a b : List Instr} (ha : Plain a) (hb : Plain b) : Plain (a ++ b) := by
  intro i hi; rcases List.mem_append.mp hi with h | h
  · exact ha i h
  · exact hb i h

theorem xFreeL_plain : ∀ {is : List Instr}, Plain is → Abstract.CallX.xFreeL (liftInstrs is) = true
  | [], _ => rfl
  | i :: is, h => by
    have hi := h i (by simp)
    simp only [liftInstrs, Abstract.CallX.xFreeL, hi.1, Abstract.CallX.xFree, hi.2.2,
      Bool.not_false, Bool.true_and]
    exact xFreeL_plain (fun j hj => h j (List.mem_cons_of_mem _ hj))

theorem ehFreeL_plain : ∀ {is : List Instr}, Plain is → Abstract.CallXE.ehFreeL (liftInstrs is) = true
  | [], _ => rfl
  | i :: is, h => by
    have hi := h i (by simp)
    simp only [liftInstrs, Abstract.CallXE.ehFreeL, hi.1, Abstract.CallXE.ehFree, hi.2.1,
      Bool.not_false, Bool.true_and]
    exact ehFreeL_plain (fun j hj => h j (List.mem_cons_of_mem _ hj))

theorem irFreeL_plain : ∀ {is : List Instr}, Plain is → Abstract.CallXT.irFreeL (liftInstrs is) = true
  | [], _ => rfl
  | i :: is, h => by
    have hi := h i (by simp)
    have hir : Abstract.CallXT.irCall i = false := by
      have := hi.2.2
      cases i <;> first | rfl | simp [Abstract.CallX.isXCall] at this
    simp only [liftInstrs, Abstract.CallXT.irFreeL, hi.1, Abstract.CallXT.irFree, hir,
      Bool.not_false, Bool.true_and]
    exact irFreeL_plain (fun j hj => h j (List.mem_cons_of_mem _ hj))

theorem flatChkE_eh {tags : List TagInst} {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
    {labels : List Nat} {h : Nat} {i : Instr} (h₂ : Abstract.CallXE.ehInstr i = false) :
    flatChkE (ehExt tags) F mi nl ret labels h i = flatChkE tExt F mi nl ret labels h i := by
  cases i <;> first | rfl | simp [Abstract.CallXE.ehInstr] at h₂

/-- **Off the exception forms the check is `tExt`'s.** -/
theorem chkE_plain_tExt {tags : List TagInst} {F : List (FuncInst H)} {mi : ModuleInst}
    {nl ret : Nat} {labels : List Nat} :
    ∀ {is : List Instr} (oh : Option Nat),
      (∀ i ∈ is, liftInstr i = .op i [] ∧ Abstract.CallXE.ehInstr i = false) →
      chkE (ehExt tags) F mi nl ret labels oh (liftInstrs is) =
        chkE tExt F mi nl ret labels oh (liftInstrs is)
  | _, none, _ => by cases ‹List Instr› <;> rfl
  | [], some _, _ => rfl
  | i :: is, some k, h => by
    have hi := h i (by simp)
    simp only [liftInstrs, hi.1, chkE, chk1E, Option.bind_some]
    rw [flatChkE_eh hi.2]
    cases flatChkE tExt F mi nl ret labels k i with
    | none => rfl
    | some o =>
      simp only [Option.bind_some]
      exact chkE_plain_tExt o (fun j hj => h j (List.mem_cons_of_mem _ hj))

/-- **Off the exception forms the check is `tExt`'s**, on code without terminators. -/
theorem chkE_flat_tExt {tags : List TagInst} {F : List (FuncInst H)} {mi : ModuleInst}
    {nl ret : Nat} {labels : List Nat} {is : List Instr} (oh : Option Nat)
    (h : ∀ i ∈ is, isTerminator i = false) :
    chkE (ehExt tags) F mi nl ret labels oh (liftInstrs is) =
      chkE tExt F mi nl ret labels oh (liftInstrs is) :=
  chkE_plain_tExt oh fun i hi => ⟨liftInstr_flat (h i hi), by
    have := h i hi; cases i <;> first | rfl | simp [isTerminator] at this⟩

/-- **Logged plain code is a region run** with the same oracle, ending as `ResOut` says. -/
theorem plain_runC {P P₀ : Numerics.Profile} {host host₀ : HostSemantics H} {C : CallRel H}
    (hC : OracleSoundT P₀ host₀ C) {tags : List TagInst} {is : List Instr} (hp : Plain is)
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
  have hx := xFreeL_plain hp
  obtain ⟨s₂, f₂, o⟩ := r
  cases o with
  | tail a args n => exact absurd d (Abstract.CallXP.evalOXP_not_tail hx)
  | flow fl =>
    refine ⟨s₂, f₂, fl, rfl, ?_⟩
    have hox := (Abstract.CallXE.evalOXE_iff_evalOX (ehFreeL_plain hp)).1
      ((Abstract.CallXP.evalOXP_iff_evalOXE hx).1 d)
    have hot := (Abstract.CallXT.evalOXT_iff_evalOX (irFreeL_plain hp)).2 hox
    have hchk' := (chkE_plain_tExt _ (fun i hi => ⟨(hp i hi).1, (hp i hi).2.1⟩)).symm.trans hchk
    obtain ⟨s', f', o, hrun, hres⟩ := Bridge.bridge_fwd (P := P) (host := host) hC hot hS hchk'
    rw [lowerList_liftInstrs] at hrun
    exact ⟨s', f', o, hrun, hres⟩

/-- **Logged straight-line code is a region run** with the same oracle, ending as `ResOut`
says, when its calls are answers of a sound oracle and it passes the check with exceptions on. -/
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
        Bridge.ResOut C s' f' o (s₂, f₂, fl) :=
  plain_runC hC (plain_of_flat hflat) hr hl hS hchk

/-- **Segment bodies are straight-line code** when the body makes direct calls only. -/
theorem seg_flat {body : Expr} (hD : DirectCalls body) {p : List SeqStep} {c : List Instr}
    {i : Nat} {sg : Segment} (hc : seqAt body p = some c) (hsg : (segment c)[i]? = some sg) :
    Flat sg.body :=
  fun x hx => ⟨(MachineLBwd.seg_wf hsg).1 x hx, hD p c i sg hc hsg x hx⟩

end Silmaril.Wasm.Cfg.Proofs.MachineLProjS
