module

public import Silmaril.Wasm.Cfg.MachineLProj.Defs
public import Silmaril.Proofs.Wasm.Cfg.Bridge
public import Silmaril.Wasm.Abstract.ExposePTyped.Thms
public import Silmaril.Wasm.Interp.EHExt.Thms

@[expose] public section

/-!
# Straight-line code with pending tail calls is a region run (proofs)

`flat_runP`: a native run with pending tail calls (`CallXP.EvalOXP C`) of straight-line code
(every instruction lifts to a single tree: no `block`, `loop`, `if` or `try_table`; calls of every
form, tail calls, `throw`, `throw_ref`, branches, `return` and every other flat instruction are
allowed), checked with exceptions on (`chkE (ehExt Γ.tags)`), is a region run (`Region.RunC`)
of the code with the same oracle, ending as `ResOutP` says. A pending tail call is not answered:
it is the region's pending tail call over the whole Core stack below the callee.

The oracle respects arities (`ExposePTyped.ArityResp`) and the store agrees with `Γ`. Each
instruction's continuation is checked at the stack height the instruction leaves: that is
`ExposePTyped.evalOXP_goodO` on the instruction alone, and it needs the answer of a call to keep
the store's functions (so the rest of the code checks as before) and to return at least the
callee's result count (so the stack is at the checked height). The checker gives each call's
parameter count under the stack height (`callArity_eq`, `tExt_tail`, `flatChk_tailForm`), and a
flat instruction's step is `Bridge.flat_run`.
-/

namespace Silmaril.Wasm.Cfg.Proofs.MachineLProjE

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Region Silmaril.Wasm.Cfg.Bridge
  Silmaril.Wasm.Cfg.MachineL Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen
  Silmaril.Wasm.Interp Silmaril.Wasm.Numerics
open Silmaril.Wasm.Abstract.ExposePTyped Silmaril.Wasm.Abstract.ExposePStruct
open Silmaril.Wasm.Abstract.CallXP (EvalOXP POut)
open Silmaril.Wasm.Cfg.Proofs.Bridge

variable {H : Type} {P : Profile} {host : HostSemantics H} {C : Abstract.CallRel H}

/-! ## Checker facts at one instruction -/

section Chk

variable {Γ : Ctx H} {s : Store H} {f : Frame} {N : List Val} {i : Instr} {es : List BExpr}
  {labels : List Nat} {ret : Nat} {out : Option Nat}

/-- The operator of a checked sequence passes the flat check at the stack height. -/
theorem op_chk
    (hchk : chkE (ehExt Γ.tags) s.funcs f.module f.locals.length ret labels (some N.length)
      (.op i [] :: es) = some out) :
    ∃ o₀, flatChkE (ehExt Γ.tags) s.funcs f.module f.locals.length ret labels N.length i =
      some o₀ := by
  obtain ⟨o₀, h1, -⟩ := chk_consE.mp hchk
  obtain ⟨oa, ha, hk⟩ := chk1_opE h1
  rw [chk_nilE] at ha
  exact ⟨o₀, hk _ (Option.some.inj ha).symm⟩

/-- **The continuation is checked at the height the instruction leaves**, under an
arity-respecting oracle, and the store keeps agreeing with `Γ`. -/
theorem cont_chk (hA : ArityResp Γ C) (hg : Γ.Good s) {s₂ : Store H} {f₂ : Frame} {N₂ : List Val}
    (d₁ : EvalOXP C s f N [.op i []] (s₂, f₂, .flow (.normal N₂)))
    (hchk : chkE (ehExt Γ.tags) s.funcs f.module f.locals.length ret labels (some N.length)
      (.op i [] :: es) = some out) :
    Γ.Good s₂ ∧
      chkE (ehExt Γ.tags) s₂.funcs f₂.module f₂.locals.length ret labels (some N₂.length) es =
        some out := by
  obtain ⟨o₀, h1, h2⟩ := chk_consE.mp hchk
  have h1' : chkE (ehExt Γ.tags) s.funcs f.module f.locals.length ret labels (some N.length)
      [.op i []] = some o₀ :=
    chk_consE.mpr ⟨o₀, h1, by cases o₀ <;> rfl⟩
  obtain ⟨hg₂, hm, hl, hgo⟩ := evalOXP_goodO hA d₁ hg h1'
  simp only [GoodO] at hgo
  subst hgo
  refine ⟨hg₂, ?_⟩
  rw [hg₂.1, hm, hl, ← hg.1]
  exact h2

/-- A direct call's parameters are under the checked height. -/
theorem call_hp {x : FuncIdx} {a : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
    (hfi : s.func? f x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hchk : chkE (ehExt Γ.tags) s.funcs f.module f.locals.length ret labels (some N.length)
      (.op (.call x) [] :: es) = some out) :
    ps.length ≤ N.length := by
  obtain ⟨o₀, hf⟩ := op_chk hchk
  simp only [flatChkE, flatEff, callArity_eq hfi hty] at hf
  split at hf
  · assumption
  · cases hf

/-- An indirect or reference call's parameters are under the index or reference. -/
theorem ir_hp {i : Instr} {y : TypeIdx} {v : Val} {stk : List Val} {ps rs : List Validation.CValType}
    (hi : (∃ x, i = .callIndirect x y) ∨ i = .callRef y)
    (hy : Abstract.CallXT.typeArity f.module y = some (ps.length, rs.length))
    (hchk : chkE (ehExt Γ.tags) s.funcs f.module f.locals.length ret labels
      (some (v :: stk).length) (.op i [] :: es) = some out) :
    ps.length ≤ stk.length := by
  obtain ⟨o₀, hf⟩ := op_chk hchk
  rcases hi with ⟨x, rfl⟩ | rfl <;>
  · simp only [flatChkE, ehExt, tExt, hy, Option.map_some, extStep, List.length_cons] at hf
    split at hf
    · omega
    · cases hf

/-- A resolved tail call's parameters are under its popped operand. -/
theorem tail_hp {i : Instr} {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
    (hres : Abstract.CallX.TailRes s f i N (some (fa, N.drop (Abstract.CallX.tailPop i))))
    (hfi : s.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hy : ∀ y, Abstract.CallXT.tailAnn i = some y →
      Abstract.CallXT.typeArity f.module y = some (ps.length, rs.length))
    (hchk : chkE (ehExt Γ.tags) s.funcs f.module f.locals.length ret labels (some N.length)
      (.op i [] :: es) = some out) :
    ps.length ≤ (N.drop (Abstract.CallX.tailPop i)).length := by
  obtain ⟨o₀, hf⟩ := op_chk hchk
  have he : flatChkE (ehExt Γ.tags) s.funcs f.module f.locals.length ret labels N.length i =
      flatChkE tExt s.funcs f.module f.locals.length ret labels N.length i := by
    cases hres <;> rfl
  rw [he] at hf
  obtain ⟨hp, -, -⟩ := flatChk_tailForm (tExt_tail hres hfi hty hy) hf
  simp only [List.length_drop]
  omega

end Chk

/-! ## Region runs of one instruction -/

/-- **A resolved tail call ends the region in a pending tail call** of its callee, over the
stack under the popped operand, in a `return_call_ref` form. -/
theorem tail_runP {s : Store H} {f : Frame} {stk : List Val} {code : List Admin} {i : Instr}
    {fa : Nat}
    (hres : Abstract.CallX.TailRes s f i stk (some (fa, stk.drop (Abstract.CallX.tailPop i)))) :
    ∃ c : Admin, c.IsReturnCallRef ∧ RunC P host C s f stk.reverse (.plain i :: code) s f
      (.tail (stk.drop (Abstract.CallX.tailPop i)).reverse fa c) := by
  generalize ho : (some (fa, stk.drop (Abstract.CallX.tailPop i)) : Option (Nat × List Val)) = p
    at hres
  cases hres with
  | direct hfi =>
    simp only [Option.some.injEq, Prod.mk.injEq, Abstract.CallX.tailPop, List.drop_zero] at ho
    obtain ⟨rfl, -⟩ := ho
    exact ⟨.returnCallRefType _, trivial, .returnCall hfi⟩
  | @indirect x y ad i' fa' stk' hres' =>
    simp only [Option.some.injEq, Prod.mk.injEq, Abstract.CallX.tailPop, List.drop_succ_cons,
      List.drop_zero] at ho
    obtain ⟨rfl, -⟩ := ho
    cases hres' with
    | func ht hr hc =>
      refine ⟨.plain (.returnCallRef y), trivial, ?_⟩
      simp only [Abstract.CallX.tailPop, List.drop_succ_cons, List.drop_zero, List.reverse_cons]
      exact .returnCallIndirect (.simple (by simp [SingleThreaded.Det.famOf]) (tableGet_val ht hr)
        (.simple (by simp [SingleThreaded.Det.famOf]) (cast_val hc) (.returnCallRef trivial)))
  | @ref y fa' stk' =>
    simp only [Option.some.injEq, Prod.mk.injEq, Abstract.CallX.tailPop, List.drop_succ_cons,
      List.drop_zero] at ho
    obtain ⟨rfl, -⟩ := ho
    refine ⟨.plain (.returnCallRef y), trivial, ?_⟩
    simp only [Abstract.CallX.tailPop, List.drop_succ_cons, List.drop_zero, List.reverse_cons]
    exact .returnCallRef trivial
  | indirectTrap => cases ho
  | refNull => cases ho

theorem cons_code (i : Instr) (is : List Instr) :
    expression (i :: is) = [.plain i] ++ expression is := rfl

/-! ## The forward bridge on straight-line code -/

/-- **Straight-line code with pending tail calls is a region run**, ending as `ResOutP` says. -/
theorem flat_runP {Γ : Ctx H} (hA : ArityResp Γ C) :
    ∀ {is : List Instr}, (∀ i ∈ is, liftInstr i = .op i []) →
    ∀ {s : Store H} {f : Frame} {N : List Val} {r : Store H × Frame × POut},
    EvalOXP C s f N (liftInstrs is) r → Γ.Good s →
    ∀ {labels : List Nat} {ret : Nat} {out : Option Nat},
    chkE (ehExt Γ.tags) s.funcs f.module f.locals.length ret labels (some N.length)
      (liftInstrs is) = some out →
    ∃ s' f' o, RunC P host C s f N.reverse (expression is) s' f' o ∧ ResOutP s' f' o r
  | [], _, s, f, N, r, d, _, _, _, _, _ => by
    cases d
    exact ⟨s, f, .normal N.reverse, .nil, rfl, rfl, rfl⟩
  | i :: is, hflat, s, f, N, r, d, hg, labels, ret, out, hchk => by
    have hrest : ∀ j ∈ is, liftInstr j = .op j [] := fun j hj => hflat j (List.mem_cons_of_mem _ hj)
    have e : liftInstrs (i :: is) = .op i [] :: liftInstrs is := by
      simp only [liftInstrs, hflat i (by simp)]
    rw [e] at d hchk
    cases d with
    | argsAbort hargs ho =>
      cases hargs
      exact absurd trivial ho
    | @opOk _ _ s₂ _ _ f₂ _ _ stk₂ _ _ _ _ hi hargs hfl hk =>
      cases hargs
      obtain ⟨hg₂, hchk₂⟩ := cont_chk hA hg (.opOk hi .nil hfl .nil) hchk
      obtain ⟨o₀, hf⟩ := op_chk hchk
      obtain ⟨o', hr', hrel, -⟩ :=
        flat_run (P := P) (host := host) (C := C) hi (flatChk_of_evalFlat hfl hf) hfl
      obtain rfl := out_normal_of_rel hrel
      obtain ⟨s', f', o, hr, hres⟩ := flat_runP hA hrest hk hg₂ hchk₂
      exact ⟨s', f', o, by rw [cons_code]; exact Proofs.Region.run_append hr' hr, hres⟩
    | @opStop _ _ s₂ _ _ f₂ _ _ _ _ _ fl hi hargs hfl hn =>
      cases hargs
      obtain ⟨o₀, hf⟩ := op_chk hchk
      obtain ⟨o', hr', hrel, -⟩ :=
        flat_run (P := P) (host := host) (C := C) hi (flatChk_of_evalFlat hfl hf) hfl
      exact ⟨s₂, f₂, o', by
        rw [cons_code]
        exact Proofs.Region.run_append hr' (thenC_stop (not_normal_of_rel hrel hn)),
        rfl, rfl, hrel⟩
    | @callOk _ _ s₂ _ _ _ _ vs x _ _ a fi ps rs fl _ hargs hfi hty hcall hvs hk =>
      cases hargs
      have hp := call_hp hfi hty hchk
      obtain ⟨hg₂, hchk₂⟩ := cont_chk hA hg (.callOk .nil hfi hty hcall hvs .nil) hchk
      obtain ⟨s', f', o, hr, hres⟩ := flat_runP hA hrest hk hg₂ hchk₂
      refine ⟨s', f', o, ?_, hres⟩
      rw [rev_split N ps.length]
      exact RunC.call hfi hty (len_rev_take hp) hcall hvs (by simpa [List.reverse_append, expression] using hr)
    | @callTrap _ _ s₂ _ _ _ _ x _ _ a fi ps rs hargs hfi hty hcall =>
      cases hargs
      have hp := call_hp hfi hty hchk
      refine ⟨s₂, f, .trap, ?_, rfl, rfl, trivial⟩
      rw [rev_split N ps.length]
      exact RunC.callTrap hfi hty (len_rev_take hp) hcall
    | @callThrow _ _ s₂ _ _ _ _ x _ _ a fi ps rs t hargs hfi hty hcall =>
      cases hargs
      have hp := call_hp hfi hty hchk
      refine ⟨s₂, f, .throw t, ?_, rfl, rfl, rfl⟩
      rw [rev_split N ps.length]
      exact RunC.callThrow hfi hty (len_rev_take hp) hcall
    | @callIndOk _ _ s₂ _ _ _ stk₁ vs x y _ _ ad i' fa fi ps rs fl _ hargs hres hfi hty hy hcall
        hvs hk =>
      cases hargs
      have hp := ir_hp (.inl ⟨x, rfl⟩) hy hchk
      obtain ⟨hg₂, hchk₂⟩ := cont_chk hA hg (.callIndOk .nil hres hfi hty hy hcall hvs .nil) hchk
      obtain ⟨s', f', o, hr, hres'⟩ := flat_runP hA hrest hk hg₂ hchk₂
      refine ⟨s', f', o, ?_, hres'⟩
      rw [List.reverse_cons, rev_split stk₁ ps.length]
      exact RunC.callInd hres hfi hty (len_rev_take hp) hcall hvs
        (by simpa [List.reverse_append, expression] using hr)
    | @callIndRes _ _ _ _ _ stk₁ x y _ _ ad i' hargs hres =>
      cases hargs
      refine ⟨s, f, .trap, ?_, rfl, rfl, trivial⟩
      rw [List.reverse_cons]
      exact RunC.callIndRes hres
    | @callIndStop _ _ s₂ _ _ _ stk₁ x y _ _ ad i' fa fi ps rs fl hargs hres hfi hty hy hcall hfl =>
      cases hargs
      have hp := ir_hp (.inl ⟨x, rfl⟩) hy hchk
      rcases abrupt_cases hfl with rfl | ⟨t, rfl⟩
      · refine ⟨s₂, f, .trap, ?_, rfl, rfl, trivial⟩
        rw [List.reverse_cons, rev_split stk₁ ps.length]
        exact RunC.callIndTrap hres hfi hty (len_rev_take hp) hcall
      · refine ⟨s₂, f, .throw t, ?_, rfl, rfl, rfl⟩
        rw [List.reverse_cons, rev_split stk₁ ps.length]
        exact RunC.callIndThrow hres hfi hty (len_rev_take hp) hcall
    | @callRefOk _ _ s₂ _ _ _ stk₁ vs y _ _ fa fi ps rs fl _ hargs hfi hty hy hcall hvs hk =>
      cases hargs
      have hp := ir_hp (.inr rfl) hy hchk
      obtain ⟨hg₂, hchk₂⟩ := cont_chk hA hg (.callRefOk .nil hfi hty hy hcall hvs .nil) hchk
      obtain ⟨s', f', o, hr, hres'⟩ := flat_runP hA hrest hk hg₂ hchk₂
      refine ⟨s', f', o, ?_, hres'⟩
      rw [List.reverse_cons, rev_split stk₁ ps.length]
      exact RunC.callRef hfi hty (len_rev_take hp) hcall hvs (by simpa [List.reverse_append, expression] using hr)
    | @callRefNull _ _ _ _ _ stk₁ y _ _ hargs =>
      cases hargs
      refine ⟨s, f, .trap, ?_, rfl, rfl, trivial⟩
      rw [List.reverse_cons]
      exact RunC.callRefNull
    | @callRefStop _ _ s₂ _ _ _ stk₁ y _ _ fa fi ps rs fl hargs hfi hty hy hcall hfl =>
      cases hargs
      have hp := ir_hp (.inr rfl) hy hchk
      rcases abrupt_cases hfl with rfl | ⟨t, rfl⟩
      · refine ⟨s₂, f, .trap, ?_, rfl, rfl, trivial⟩
        rw [List.reverse_cons, rev_split stk₁ ps.length]
        exact RunC.callRefTrap hfi hty (len_rev_take hp) hcall
      · refine ⟨s₂, f, .throw t, ?_, rfl, rfl, rfl⟩
        rw [List.reverse_cons, rev_split stk₁ ps.length]
        exact RunC.callRefThrow hfi hty (len_rev_take hp) hcall
    | @tail _ _ _ _ _ _ _ _ _ fa fi ps rs hargs hres hfi hty hy =>
      cases hargs
      have hp := tail_hp hres hfi hty hy hchk
      obtain ⟨c, hc, hrt⟩ := tail_runP (P := P) (host := host) (C := C)
        (code := expression is) hres
      exact ⟨s, f, _, hrt, _, c, rfl, hc, rfl, rfl, fi, ps, rs,
        ((N.drop (Abstract.CallX.tailPop i)).drop ps.length).reverse, hfi, hty, rev_split _ _,
        len_rev_take hp, rfl⟩
    | tailRes hargs hres =>
      cases hargs
      obtain ⟨o', hr', hrel, -⟩ := tailRes_none_run (P := P) (host := host) (C := C)
        (code := expression is) hres
      exact ⟨s, f, o', hr', rfl, rfl, hrel⟩
    | @throw _ _ _ _ _ _ x _ _ ta ti ts hargs ht he hn =>
      cases hargs
      refine ⟨_, f, .throw s.exns.length, ?_, rfl, rfl, rfl⟩
      rw [rev_split N ts.length]
      exact RunC.throw ht he (len_rev_take hn)
    | @throwRefNull _ _ _ _ _ stk₁ _ _ hargs =>
      cases hargs
      refine ⟨s, f, .trap, ?_, rfl, rfl, trivial⟩
      rw [List.reverse_cons]
      exact RunC.throwRefNull
    | @throwRefExn _ _ _ _ _ stk₁ a _ _ hargs =>
      cases hargs
      refine ⟨s, f, .throw a, ?_, rfl, rfl, rfl⟩
      rw [List.reverse_cons]
      exact RunC.throwRefExn

end Silmaril.Wasm.Cfg.Proofs.MachineLProjE
