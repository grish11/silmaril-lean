module

public import Silmaril.Proofs.Wasm.Cfg.MachineLProjK
import Silmaril.Proofs.Wasm.Cfg.MachineLProjI
import Silmaril.Proofs.Wasm.Cfg.MachineLProjS
import Silmaril.Proofs.Wasm.Cfg.MachineLProjE
import Silmaril.Proofs.Wasm.Cfg.MachineLFwd
import Silmaril.Proofs.Wasm.Cfg.MachineLClosed
import Silmaril.Proofs.Wasm.Cfg.MachineLBwd
import Silmaril.Proofs.Wasm.Cfg.MachineComplete

@[expose] public section

/-!
# Pending tail calls of checked logged runs fit their callee (proofs)

A pending tail call at the end of a checked logged run passes the callee's parameter count:
the straight-line code making it is a region run (`MachineLProjE.flat_runP`), whose pending tail
call carries exactly the callee's `ps.length` arguments (`ResOutP`).
-/

namespace Silmaril.Wasm.Cfg.Proofs.MachineLProjF

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Cfg.Region Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Interp (ehExt chkE endsAt)

variable {H : Type} {C : Abstract.CallRel H}

open Silmaril.Wasm.Cfg.Proofs.MachineLProjI (chkE_append) in
open Silmaril.Wasm.Cfg.Proofs.Machine (restAt_cons) in
open Silmaril.Wasm.Abstract.ExposePTyped (ArityResp) in
/-- **A pending tail call at a checked state fits its callee**: the callee of the store the
call leaves has a function type `(ps, rs)`, the call passes `ps.length` arguments and its result
count is `rs.length`. -/
theorem tail_fit {Γ : Abstract.ExposePStruct.Ctx H} (hA : ArityResp Γ C) {mi : ModuleInst}
    {nl ret : Nat} {body : Expr} {st : MState H} {l : List (Abstract.SCall H)} {s₁ : Store H}
    {f₁ : Frame} {a n : Nat} {args : List Val}
    (ht : TailL body st l (s₁, f₁, .tail a args n)) (hl : ∀ e ∈ l, CloseOk C e)
    (hg : Γ.Good st.store) (hn : st.frame.locals.length = nl)
    (hI : CInv (ehExt Γ.tags) Γ.funcs mi nl ret body st) :
    ∃ (fi : FuncInst H) (ps rs : List Validation.CValType), s₁.funcs[a]? = some fi ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧ args.length = ps.length ∧
      n = rs.length := by
  cases ht with
  | @tail bb sg stk ls s _ f _ _ _ _ _ hb hns hr =>
  obtain ⟨hf, c, out, hc, hchk, hF⟩ := hI
  obtain ⟨c₀, hc₀, hsg⟩ := Proofs.Machine.seg_of_lookup hb
  simp only at hc hchk hf hg hn
  rw [hc] at hc₀; cases hc₀
  rw [restAt_cons hsg, Binaryen.liftInstrs_append, chkE_append] at hchk
  obtain ⟨oc, hoc, -⟩ := Option.bind_eq_some_iff.mp hchk
  have hoc' : Interp.chkE (Interp.ehExt Γ.tags) s.funcs f.module f.locals.length ret (labs ret ls)
      (some stk.reverse.length) (liftInstrs (codeOf sg)) = some oc := by
    rw [hg.1, hf, hn, List.length_reverse]; exact hoc
  have hbodyNT : ∀ i ∈ sg.body, isTerminator i = false := (MachineLBwd.seg_wf hsg).1
  have hflat : ∀ i ∈ codeOf sg, liftInstr i = .op i [] := by
    intro i hi
    simp only [MachineL.codeOf, List.mem_append] at hi
    rcases hi with hi | hi
    · exact MachineLProjS.liftInstr_flat (hbodyNT i hi)
    · cases htt : sg.term with
      | none => simp [htt] at hi
      | some t =>
        simp [htt] at hi; subst hi; exact MachineLProjT.liftInstr_of_not_struct (hns _ htt)
  obtain ⟨s', f', o, -, W, c', rfl, -, rfl, rfl, fi, ps, rs, W₀, hfi, hty, -, hlen, rfl⟩ :=
    MachineLProjE.flat_runP (P := .spec) (host := Binaryen.closedHost) hA hflat
      (Proofs.MachineLClosed.logged_closed hr hl) hg hoc'
  exact ⟨fi, ps, rs, hfi, hty, hlen, rfl⟩

open Silmaril.Wasm.Abstract.ExposePTyped (ArityResp) in
/-- **A logged run from the CFG entry ending in a pending tail call fits its callee**, for a body
passing the function's own check. -/
theorem tail_fit_initialK {Γ : Abstract.ExposePStruct.Ctx H} (hA : ArityResp Γ C) {ret : Nat}
    {body : Expr} {s : Store H} {f : Frame} (hg : Γ.Good s)
    (hchk : endsAt (chkE (ehExt Γ.tags) Γ.funcs f.module f.locals.length ret [ret] (some 0)
      (liftInstrs body)) ret = true)
    {l l' : List (Abstract.SCall H)} {st : MState H} {s₁ : Store H} {f₁ : Frame} {a n : Nat}
    {args : List Val} (h : MRunL body (initial body s f) l st)
    (ht : TailL body st l' (s₁, f₁, .tail a args n)) (hl : ∀ e ∈ l ++ l', CloseOk C e) :
    ∃ (fi : FuncInst H) (ps rs : List Validation.CValType), s₁.funcs[a]? = some fi ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧ args.length = ps.length ∧
      n = rs.length := by
  have hl₁ : ∀ e ∈ l, CloseOk C e := fun e he => hl e (List.mem_append_left _ he)
  have hl₂ : ∀ e ∈ l', CloseOk C e := fun e he => hl e (List.mem_append_right _ he)
  have hok := MachineLFwd.initial_ok body s f
  have hI₀ := MachineLProjI.cinv_initial (s := s) (f := f) rfl hchk
  obtain ⟨hg', hn', hI'⟩ := MachineLProjK.cinv_runE hA h hl₁ hok hg rfl hI₀
  exact tail_fit hA ht hl₂ hg' hn' hI'

end Silmaril.Wasm.Cfg.Proofs.MachineLProjF
