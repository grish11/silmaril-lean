module

public import Silmaril.Proofs.Wasm.Interp.Tail
public import Silmaril.Proofs.Wasm.Interp.OracleSimX

/-!
# Forward simulation with tail calls (proofs)

`tExt` extends `irExt` with the direct tail call `return_call x` (`.tail` with the callee's
counts). Every `EvalOXT C` run of `tExt`-checked code is a Core 3.0 run under the
tail-aware postcondition `MatchT` (`evalOXT_goodT`): a `return_call` ends the body in a
pending tail call whose callee, answered by the oracle, ends as the caller's `.ret` does
(`TailRun`), and that is the frame-level behaviour of Core 3.0 (`frame_tail_exit`).

**Scope.** `return_call_indirect` and `return_call_ref` stay rejected by `tExt`: their null
case (`return_call_ref` on `ref.null`) traps only after the frame exits, which no body-level
outcome describes yet (the shared `Outcome.tailNull` repair).
-/

@[expose] public section

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXT

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-- The arity checker extension with `call_indirect`, `call_ref` and the direct tail call
`return_call x` (its callee's counts; the result arity must be the function's). -/
def tExt : ExtArity H := fun F mi i =>
  match i with
  | .callIndirect _ y | .callRef y => (typeArity mi y).map fun p => .fall (p.1 + 1) p.2
  | .returnCall x => (callArity F mi x).map fun p => .tail p.1 p.2
  | _ => none

instance : ExtStable (tExt (H := H)) := ⟨fun {F F' mi i e} hF h => by
  cases i <;> simp only [tExt] at h ⊢ <;> first
    | exact h
    | (obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 h
       exact Option.map_eq_some_iff.2 ⟨p, callArity_ext hF hp, rfl⟩)⟩

/-- **A sound call oracle, for every `call_ref` form**, with the tail-call checker `tExt`. -/
def OracleSoundT (P : Numerics.Profile) (host : HostSemantics H) (C : Abstract.CallRel H) : Prop :=
  ∀ (s s₂ : Store H) (f : Frame) (a : Nat) (fi : FuncInst H) (ps rs : List Validation.CValType)
    (us : List Val) (fl : Binaryen.Flow) (c : Admin),
    StoreChkE tExt s.funcs → s.funcs[a]? = some fi → Validation.DefType.funcType? fi.type = some (ps, rs) →
    us.length = ps.length → c.IsCallRef → C s a us (s₂, fl) →
    (∃ ob, (ob = none ∨ ob = some rs.length) ∧ FlowOk [rs.length] rs.length ob fl ∧
        FuncsGoodE tExt s.funcs s₂.funcs) ∧
      (∀ vs, fl.retVals = some vs → Steps P host
        ⟨s, f, vals us ++ [.ref (.func a), c]⟩ ⟨s₂, f, vals (vs.take rs.length).reverse⟩) ∧
      (fl = .trap → Steps P host ⟨s, f, vals us ++ [.ref (.func a), c]⟩ ⟨s₂, f, [.trap]⟩)

theorem OracleSoundT.soundE {C : Abstract.CallRel H} (hC : OracleSoundT P host C) :
    OracleSoundE tExt P host C :=
  fun s s₂ f a fi ps rs us fl hS hfi hty hn hcall =>
    hC s s₂ f a fi ps rs us fl (.callRefType fi.type) hS hfi hty hn trivial hcall

section TCases

set_option linter.unusedSectionVars false

variable {C : Abstract.CallRel H} {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ vs : List Val}
  {es args : List Binaryen.BExpr} {r : Store H × Frame × Binaryen.Flow} {fl : Binaryen.Flow}
  {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType} {y : TypeIdx}

/-- The check of an extended call form whose type has the callee's counts. -/
theorem flatChk_irT {i : Instr} {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
    {labels : List Nat} {h : Nat} {o : Option Nat}
    (hi : (∃ x, i = .callIndirect x y) ∨ i = .callRef y) (hy : typeArity mi y = some (ps.length, rs.length))
    (hc : flatChkE tExt F mi nl ret labels h i = some o) :
    ps.length + 1 ≤ h ∧ o = some (h - (ps.length + 1) + rs.length) := by
  rcases hi with ⟨x, rfl⟩ | rfl <;>
  · simp only [flatChkE, tExt, hy, Option.map_some, extStep] at hc
    split at hc
    · exact ⟨by assumption, (Option.some.inj hc).symm⟩
    · cases hc

/-- The pre-call facts of an indirect or reference call. -/
theorem arity_ir_preT {i : Instr} {top : Val} {labels : List Nat} {ret : Nat} {out : Option Nat}
    (hS : StoreChkE tExt s.funcs) (iha : ArityGoodE tExt s f stk args (s₁, f₁, .normal (top :: stk₁)))
    (hi : (∃ x, i = .callIndirect x y) ∨ i = .callRef y)
    (hy : typeArity f₁.module y = some (ps.length, rs.length))
    (hc : chkE tExt s.funcs f.module f.locals.length ret labels (some stk.length)
      (.op i args :: es) = some out) :
    EvalInvE tExt s f (s₁, f₁, .normal (top :: stk₁)) ∧ ps.length ≤ stk₁.length ∧
      chkE tExt s.funcs f.module f.locals.length ret labels
        (some (stk₁.length - ps.length + rs.length)) es = some out := by
  obtain ⟨o, h1, h2⟩ := chk_consE.mp hc
  obtain ⟨hf, inv1⟩ := arity_args hS iha h1
  obtain ⟨hp, rfl⟩ := flatChk_irT hi hy hf
  simp only [List.length_cons] at hp h2
  refine ⟨inv1, by omega, ?_⟩
  have : stk₁.length + 1 - (ps.length + 1) + rs.length = stk₁.length - ps.length + rs.length := by
    omega
  rwa [this] at h2

/-- The oracle's facts at an indirect or reference call. -/
theorem oracleX_atT (hC : OracleSoundT P host C) (hS : StoreChkE tExt s.funcs) {top : Val}
    (inv1 : EvalInvE tExt s f (s₁, f₁, .normal (top :: stk₁))) (hfi : s₁.funcs[fa]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hp : ps.length ≤ stk₁.length)
    (hcall : C s₁ fa (stk₁.take ps.length).reverse (s₂, fl)) (f' : Frame) {c : Admin}
    (hcr : c.IsCallRef) :
    (∃ ob, (ob = none ∨ ob = some rs.length) ∧ FlowOk [rs.length] rs.length ob fl ∧
        FuncsGoodE tExt s₁.funcs s₂.funcs) ∧
      (∀ vs, fl.retVals = some vs → Steps P host
        ⟨s₁, f', vals (stk₁.take ps.length).reverse ++ [.ref (.func fa), c]⟩
        ⟨s₂, f', vals (vs.take rs.length).reverse⟩) ∧
      (fl = .trap → Steps P host
        ⟨s₁, f', vals (stk₁.take ps.length).reverse ++ [.ref (.func fa), c]⟩ ⟨s₂, f', [.trap]⟩) :=
  hC s₁ s₂ f' fa fi ps rs _ fl c (storeChk_inv inv1 hS) hfi hty (take_rev_length hp) hcr hcall

theorem arityX_irOkT {i : Instr} {top : Val} (hC : OracleSoundT P host C)
    (hi : (∃ x, i = .callIndirect x y) ∨ i = .callRef y)
    (iha : ArityGoodE tExt s f stk args (s₁, f₁, .normal (top :: stk₁)))
    (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hy : typeArity f₁.module y = some (ps.length, rs.length))
    (hcall : C s₁ fa (stk₁.take ps.length).reverse (s₂, fl)) (hvs : fl.retVals = some vs)
    (ihk : ArityGoodE tExt s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es r) :
    ArityGoodE tExt s f stk (.op i args :: es) r := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, h2⟩ := arity_ir_preT hS iha hi hy hc
  obtain ⟨⟨ob, hob, hok, hfuncs⟩, -, -⟩ :=
    oracleX_atT hC hS inv1 hfi hty hp hcall f₁ (c := .callRefType fi.type) trivial
  have hrs : rs.length ≤ vs.length := retVals_length hok hob hvs
  have inv2 : EvalInvE tExt s f (s₂, f₁, .normal (vs.take rs.length ++ stk₁.drop ps.length)) :=
    ⟨inv1.1.trans hfuncs, inv1.2.1, inv1.2.2⟩
  have hlen : (vs.take rs.length ++ stk₁.drop ps.length).length =
      stk₁.length - ps.length + rs.length := by
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  have h2' : chkE tExt s₂.funcs f₁.module f₁.locals.length ret labels
      (some (vs.take rs.length ++ stk₁.drop ps.length).length) es = some out := by
    rw [hlen]
    exact chk_inv inv2 h2
  obtain ⟨hok', inv3⟩ := ihk (storeChk_inv inv2 hS) h2'
  exact ⟨hok', inv2.trans inv3⟩

theorem arityX_irStopT {i : Instr} {top : Val} (hC : OracleSoundT P host C)
    (hi : (∃ x, i = .callIndirect x y) ∨ i = .callRef y)
    (iha : ArityGoodE tExt s f stk args (s₁, f₁, .normal (top :: stk₁)))
    (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hy : typeArity f₁.module y = some (ps.length, rs.length))
    (hcall : C s₁ fa (stk₁.take ps.length).reverse (s₂, fl)) (hfl : fl.Abrupt) :
    ArityGoodE tExt s f stk (.op i args :: es) (s₂, f₁, fl) := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, -⟩ := arity_ir_preT hS iha hi hy hc
  obtain ⟨⟨_, _, hok, hfuncs⟩, -, -⟩ :=
    oracleX_atT hC hS inv1 hfi hty hp hcall f₁ (c := .callRefType fi.type) trivial
  cases fl with
  | trap => exact ⟨trivial, inv1.1.trans hfuncs, inv1.2.1, inv1.2.2⟩
  | throw t => exact absurd hok id
  | _ => exact absurd hfl id

/-- A trap reached from the arguments' checked height, with the invariants. -/
theorem arityX_irTrapT {i : Instr} {top : Val}
    (iha : ArityGoodE tExt s f stk args (s₁, f₁, .normal (top :: stk₁))) :
    ArityGoodE tExt s f stk (.op i args :: es) (s₁, f₁, .trap) := by
  intro labels ret out hS hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨-, inv1⟩ := arity_args hS iha h1
  exact ⟨trivial, inv1⟩

/-- A tail call is not checked by `tExt`. -/
theorem flatChk_tailT {i : Instr} {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
    {labels : List Nat} {h : Nat} {stk' : List Val} {o' : Option (Nat × List Val)}
    (hres : TailRes s₁ f₁ i stk' o') (hnd : ∀ x, i ≠ .returnCall x) :
    flatChkE tExt F mi nl ret labels h i = none := by
  cases hres with
  | direct => exact absurd rfl (hnd _)
  | _ => rfl

theorem arityX_tailT {i : Instr} {r' : Store H × Frame × Binaryen.Flow}
    {o' : Option (Nat × List Val)}
    (iha : ArityGoodE tExt s f stk args (s₁, f₁, .normal stk₁)) (hres : TailRes s₁ f₁ i stk₁ o')
    (hnd : ∀ x, i ≠ .returnCall x) :
    ArityGoodE tExt s f stk (.op i args :: es) r' := by
  intro labels ret out hS hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨hf, -⟩ := arity_args hS iha h1
  rw [flatChk_tailT hres hnd] at hf
  cases hf

theorem coreX_tailT {i : Instr} {r' : Store H × Frame × Binaryen.Flow}
    {o' : Option (Nat × List Val)}
    (iha : ArityGoodE tExt s f stk args (s₁, f₁, .normal stk₁)) (hres : TailRes s₁ f₁ i stk₁ o')
    (hnd : ∀ x, i ≠ .returnCall x) :
    CoreGoodE tExt P host s f stk (.op i args :: es) r' := by
  intro labels ret out hS hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨hf, -⟩ := arity_args hS iha h1
  rw [flatChk_tailT hres hnd] at hf
  cases hf

/-- The Core run of an indirect or reference call answered by the oracle, from the
callee reference and call form on top of the arguments, in context. -/
theorem steps_oracle_irT {rest : List Admin} {fin : List Admin} {c : Admin}
    (hst : Steps P host
      ⟨s₁, f₁, vals (stk₁.take ps.length).reverse ++ [.ref (.func fa), c]⟩ ⟨s₂, f₁, fin⟩) :
    Steps P host ⟨s₁, f₁, vals stk₁.reverse ++ [.ref (.func fa), c] ++ rest⟩
      ⟨s₂, f₁, vals (stk₁.drop ps.length).reverse ++ fin ++ rest⟩ := by
  have hsplit : vals stk₁.reverse =
      vals (stk₁.drop ps.length).reverse ++ vals (stk₁.take ps.length).reverse := by
    conv_lhs => rw [← List.take_append_drop ps.length stk₁]
    simp [vals]
  have h₂ := Steps.ctx (P := P) (host := host) (stk₁.drop ps.length).reverse rest hst
  rw [hsplit]
  simpa only [List.append_assoc] using h₂

/-- An indirect or reference call: the callee answered, the continuation runs. -/
theorem coreX_irOkT {i : Instr} {top : Val} (hC : OracleSoundT P host C)
    (hi : (∃ x, i = .callIndirect x y) ∨ i = .callRef y)
    (aha : ArityGoodE tExt s f stk args (s₁, f₁, .normal (top :: stk₁)))
    (iha : CoreGoodE tExt P host s f stk args (s₁, f₁, .normal (top :: stk₁)))
    (hpre : Steps P host ⟨s₁, f₁, vals [top] ++ [.plain i]⟩
      ⟨s₁, f₁, [.ref (.func fa), .plain (.callRef y)]⟩)
    (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hy : typeArity f₁.module y = some (ps.length, rs.length))
    (hcall : C s₁ fa (stk₁.take ps.length).reverse (s₂, fl)) (hvs : fl.retVals = some vs)
    {M : Nat → Store H × Frame × Binaryen.Flow → Post H}
    (ihk : CoreGoodQ tExt P host M s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es r) :
    CoreGoodQ tExt P host M s f stk (.op i args :: es) r := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, h2⟩ := arity_ir_preT hS aha hi hy hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  obtain ⟨⟨ob, hob, hok, hfuncs⟩, hret, -⟩ :=
    oracleX_atT hC hS inv1 hfi hty hp hcall f₁ (c := .plain (.callRef y)) trivial
  have hrs : rs.length ≤ vs.length := retVals_length hok hob hvs
  have inv2 : EvalInvE tExt s f (s₂, f₁, .normal (vs.take rs.length ++ stk₁.drop ps.length)) :=
    ⟨inv1.1.trans hfuncs, inv1.2.1, inv1.2.2⟩
  have hlen : (vs.take rs.length ++ stk₁.drop ps.length).length =
      stk₁.length - ps.length + rs.length := by
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  have h2' : chkE tExt s₂.funcs f₁.module f₁.locals.length ret labels
      (some (vs.take rs.length ++ stk₁.drop ps.length).length) es = some out := by
    rw [hlen]
    exact chk_inv inv2 h2
  have hk := ihk (storeChk_inv inv2 hS) h2'
  let E := expression (Binaryen.BExpr.lowerList es)
  have st₁ := Steps.ctx (P := P) (host := host) stk₁.reverse E hpre
  have st₂ := steps_oracle_irT (rest := E) (hret vs hvs)
  have e : vals (top :: stk₁).reverse ++ .plain i :: E =
      vals stk₁.reverse ++ (vals [top] ++ [.plain i]) ++ E := by simp [vals]
  rw [code_op]
  refine wp_append_normal (iha hS ha) ?_
  rw [e]
  refine WP.steps (st₁.trans st₂) ?_
  simpa [vals, List.reverse_append, List.append_assoc] using hk

/-- An indirect or reference call that traps before any call (unresolved
callee, null reference). -/
theorem coreX_irTrapT {i : Instr} {top : Val}
    (iha : CoreGoodE tExt P host s f stk args (s₁, f₁, .normal (top :: stk₁)))
    (hpre : Steps P host ⟨s₁, f₁, vals [top] ++ [.plain i]⟩ ⟨s₁, f₁, [.trap]⟩) :
    CoreGoodE tExt P host s f stk (.op i args :: es) (s₁, f₁, .trap) := by
  intro labels ret out hS hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  let E := expression (Binaryen.BExpr.lowerList es)
  have st₁ := Steps.ctx (P := P) (host := host) stk₁.reverse E hpre
  have e : vals (top :: stk₁).reverse ++ .plain i :: E =
      vals stk₁.reverse ++ (vals [top] ++ [.plain i]) ++ E := by simp [vals]
  rw [code_op]
  refine wp_append_normal (iha hS ha) ?_
  rw [e]
  refine ⟨s₁, f₁, [.trap], .trap, st₁.trans ?_, rfl, rfl, rfl, trivial⟩
  simpa using steps_trap (P := P) (host := host) s₁ f₁ stk₁.reverse E

/-- An indirect or reference call whose callee traps or throws. -/
theorem coreX_irStopT {i : Instr} {top : Val} (hC : OracleSoundT P host C)
    (hi : (∃ x, i = .callIndirect x y) ∨ i = .callRef y)
    (aha : ArityGoodE tExt s f stk args (s₁, f₁, .normal (top :: stk₁)))
    (iha : CoreGoodE tExt P host s f stk args (s₁, f₁, .normal (top :: stk₁)))
    (hpre : Steps P host ⟨s₁, f₁, vals [top] ++ [.plain i]⟩
      ⟨s₁, f₁, [.ref (.func fa), .plain (.callRef y)]⟩)
    (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hy : typeArity f₁.module y = some (ps.length, rs.length))
    (hcall : C s₁ fa (stk₁.take ps.length).reverse (s₂, fl)) (hfl : fl.Abrupt) :
    CoreGoodE tExt P host s f stk (.op i args :: es) (s₂, f₁, fl) := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, -⟩ := arity_ir_preT hS aha hi hy hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  obtain ⟨⟨_, _, hok, _⟩, -, htr⟩ :=
    oracleX_atT hC hS inv1 hfi hty hp hcall f₁ (c := .plain (.callRef y)) trivial
  cases fl with
  | throw t => exact absurd hok id
  | trap =>
    let E := expression (Binaryen.BExpr.lowerList es)
    have st₁ := Steps.ctx (P := P) (host := host) stk₁.reverse E hpre
    have st₂ := steps_oracle_irT (rest := E) (htr rfl)
    have e : vals (top :: stk₁).reverse ++ .plain i :: E =
        vals stk₁.reverse ++ (vals [top] ++ [.plain i]) ++ E := by simp [vals]
    rw [code_op]
    refine wp_append_normal (iha hS ha) ?_
    rw [e]
    refine ⟨s₂, f₁, [.trap], .trap, (st₁.trans st₂).trans ?_, rfl, rfl, rfl, trivial⟩
    simpa using steps_trap (P := P) (host := host) s₂ f₁ (stk₁.drop ps.length).reverse E
  | _ => exact absurd hfl id

end TCases
section TailCall

set_option linter.unusedSectionVars false

variable {C : Abstract.CallRel H} {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ vs : List Val}
  {es args : List Binaryen.BExpr} {fl : Binaryen.Flow} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
  {ps rs : List Validation.CValType} {r : Store H × Frame × Binaryen.Flow}

theorem tailFlow_of_retValsT {n : Nat} {fl : Binaryen.Flow} {vs : List Val}
    (h : fl.retVals = some vs) : tailFlow n fl = .ret (vs.take n) := by
  rcases fl with w | ⟨_ | k, w⟩ | w | _ | _ <;> simp_all [Binaryen.Flow.retVals, tailFlow]

/-- The check of `return_call x`. -/
theorem flatChk_returnCall {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
    {labels : List Nat} {h : Nat} {o : Option Nat}
    (hca : callArity F mi x = some (ps.length, rs.length))
    (hc : flatChkE tExt F mi nl ret labels h (.returnCall x) = some o) :
    ps.length ≤ h ∧ rs.length = ret ∧ o = none := by
  simp only [flatChkE, tExt, hca, Option.map_some, extStep] at hc
  split at hc
  · rename_i hh
    exact ⟨hh.1, hh.2, (Option.some.inj hc).symm⟩
  · cases hc

/-- The pre-call facts of `return_call x`. -/
theorem returnCall_pre {labels : List Nat} {ret : Nat} {out : Option Nat}
    (hS : StoreChkE tExt s.funcs) (iha : ArityGoodE tExt s f stk args (s₁, f₁, .normal stk₁))
    (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hc : chkE tExt s.funcs f.module f.locals.length ret labels (some stk.length)
      (.op (.returnCall x) args :: es) = some out) :
    EvalInvE tExt s f (s₁, f₁, .normal stk₁) ∧ ps.length ≤ stk₁.length ∧ rs.length = ret := by
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨hf, inv1⟩ := arity_args hS iha h1
  obtain ⟨hp, hr, -⟩ := flatChk_returnCall (callArity_eq hfi hty) hf
  exact ⟨inv1, hp, hr⟩

theorem arityT_returnCall (hC : OracleSoundT P host C)
    (iha : ArityGoodE tExt s f stk args (s₁, f₁, .normal stk₁))
    (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hcall : C s₁ a (stk₁.take ps.length).reverse (s₂, fl))
    (hfl : (∃ vs, fl.retVals = some vs) ∨ fl.Abrupt) :
    ArityGoodE tExt s f stk (.op (.returnCall x) args :: es) (s₂, f₁, tailFlow rs.length fl) := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, hret⟩ := returnCall_pre hS iha hfi hty hc
  obtain ⟨⟨ob, hob, hok, hfuncs⟩, -, -⟩ := oracle_at hC.soundE hS inv1 hfi hty hp hcall f₁
  have inv2 : EvalInvE tExt s f (s₂, f₁, tailFlow rs.length fl) :=
    ⟨inv1.1.trans hfuncs, inv1.2.1, inv1.2.2⟩
  refine ⟨?_, inv2⟩
  rcases hfl with ⟨vs, hvs⟩ | hab
  · rw [tailFlow_of_retValsT hvs]
    have hrs : rs.length ≤ vs.length := retVals_length hok hob hvs
    show ret ≤ (vs.take rs.length).length
    simp only [List.length_take]; omega
  · cases fl with
    | trap => trivial
    | throw t => exact absurd hok id
    | _ => exact absurd hab id

/-- **A direct tail call ends the body in a pending tail call** whose callee, answered by
the oracle, ends as the caller does. -/
theorem coreT_returnCall (hC : OracleSoundT P host C)
    (aha : ArityGoodE tExt s f stk args (s₁, f₁, .normal stk₁))
    (iha : CoreGoodE tExt P host s f stk args (s₁, f₁, .normal stk₁))
    (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hcall : C s₁ a (stk₁.take ps.length).reverse (s₂, fl))
    (hfl : (∃ vs, fl.retVals = some vs) ∨ fl.Abrupt) :
    CoreGoodT tExt P host s f stk (.op (.returnCall x) args :: es)
      (s₂, f₁, tailFlow rs.length fl) := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, hret⟩ := returnCall_pre hS aha hfi hty hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  have hS₁ : StoreChkE tExt s₁.funcs := storeChk_inv inv1 hS
  obtain ⟨ps', rs', hex, hpl, -⟩ := expand_of_funcType hty
  have hpp : ps.length = ps'.length := by rw [← hpl]
  have hlen : (stk₁.take ps.length).reverse.length = ps.length := by
    simp only [List.length_reverse, List.length_take]; omega
  have hT : TailRun P host ret (s₂, f₁, tailFlow rs.length fl) s₁ f₁ stk₁.reverse a
      (.returnCallRefType fi.type) := by
    refine ⟨trivial, rfl, (stk₁.drop ps.length).reverse, (stk₁.take ps.length).reverse, fi, ps', rs',
      rev_take_drop stk₁ ps.length, funcs_of_func? hfi, hex, by rw [hlen, hpp], fun g => ?_⟩
    obtain ⟨⟨_, _, hok, _⟩, hretS, htr⟩ :=
      hC s₁ s₂ g a fi ps rs _ fl (.callRefType fi.type) hS₁ (funcs_of_func? hfi) hty hlen trivial hcall
    rcases hfl with ⟨vs, hvs⟩ | hab
    · refine .inl ⟨vs.take rs.length, tailFlow_of_retValsT hvs, ?_⟩
      rw [← hret, List.take_take, Nat.min_self]
      exact hretS vs hvs
    · cases fl with
      | trap => exact .inr ⟨rfl, htr rfl⟩
      | throw t => exact absurd hok id
      | _ => exact absurd hab id
  have hw := wp_tail (P := P) (host := host) (n := ret) hT []
    (expression (Binaryen.BExpr.lowerList es)) []
  have st := Step.ctx (P := P) (host := host) stk₁.reverse (expression (Binaryen.BExpr.lowerList es))
    (Step.returnCall (s := s₁) (f := f₁) (module_of_func? hfi) (funcs_of_func? hfi))
  rw [code_op]
  refine wp_append_normal (iha hS ha) (WP.step (by simpa using st) ?_)
  simpa using hw

/-- **An oracle call under any postcondition.** -/
theorem coreOQ_callOk {M : Nat → Store H × Frame × Binaryen.Flow → Post H}
    (hC : OracleSoundE tExt P host C)
    (aha : ArityGoodE tExt s f stk args (s₁, f₁, .normal stk₁))
    (iha : CoreGoodE tExt P host s f stk args (s₁, f₁, .normal stk₁))
    (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hcall : C s₁ a (stk₁.take ps.length).reverse (s₂, fl)) (hvs : fl.retVals = some vs)
    (ihk : CoreGoodQ tExt P host M s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es r) :
    CoreGoodQ tExt P host M s f stk (.op (.call x) args :: es) r := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, h2⟩ := arity_call_pre hS aha hfi hty hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  obtain ⟨⟨ob, hob, hok, hfuncs⟩, hret, -⟩ := oracle_at hC hS inv1 hfi hty hp hcall f₁
  have hrs : rs.length ≤ vs.length := retVals_length hok hob hvs
  have inv2 : EvalInvE tExt s f (s₂, f₁, .normal (vs.take rs.length ++ stk₁.drop ps.length)) :=
    ⟨inv1.1.trans hfuncs, inv1.2.1, inv1.2.2⟩
  have hlen : (vs.take rs.length ++ stk₁.drop ps.length).length =
      stk₁.length - ps.length + rs.length := by
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  have h2' : chkE tExt s₂.funcs f₁.module f₁.locals.length ret labels
      (some (vs.take rs.length ++ stk₁.drop ps.length).length) es = some out := by
    rw [hlen]
    exact chk_inv inv2 h2
  have hk := ihk (storeChk_inv inv2 hS) h2'
  have st := steps_oracle_call (rest := expression (Binaryen.BExpr.lowerList es)) hfi (hret vs hvs)
  rw [code_op]
  refine wp_append_normal (iha hS ha) (WP.steps st ?_)
  simpa [vals, List.reverse_append, List.append_assoc] using hk

end TailCall

/-- **Forward simulation with direct tail calls**: every `EvalOXT C` run of `tExt`-checked
code is a Core 3.0 run under the tail-aware postcondition, with the arity invariants. -/
theorem evalOXT_goodT {C : Abstract.CallRel H} (hC : OracleSoundT P host C) {s : Store H}
    {f : Frame} {stk : List Val} {es : List Binaryen.BExpr} {r : Store H × Frame × Binaryen.Flow}
    (h : EvalOXT C s f stk es r) :
    ArityGoodE tExt s f stk es r ∧ CoreGoodT tExt P host s f stk es r := by
  have hE := hC.soundE
  induction h with
  | nil => exact ⟨arity_nil, coreT_of_core core_nil⟩
  | argsAbort _ hfl iha => exact ⟨arity_argsAbort iha.1 hfl, coreT_argsAbort iha.2 hfl⟩
  | callOk _ hfi hty hcall hvs _ iha ihk =>
    exact ⟨arityO_callOk hE iha.1 hfi hty hcall hvs ihk.1,
      coreOQ_callOk hE iha.1 (core_of_coreT_normal iha.2) hfi hty hcall hvs ihk.2⟩
  | callTrap _ hfi hty hcall iha =>
    exact ⟨arityO_callTrap hE iha.1 hfi hty hcall,
      coreT_of_core (coreO_callTrap hE iha.1 (core_of_coreT_normal iha.2) hfi hty hcall)⟩
  | callThrow _ hfi hty hcall iha =>
    exact ⟨arityO_callThrow hE iha.1 hfi hty hcall,
      coreT_of_core (coreO_callThrow hE iha.1 hfi hty hcall)⟩
  | opOk hi _ hflat _ iha ihk =>
    exact ⟨arity_opOk iha.1 hflat ihk.1, core_opOk iha.1 (core_of_coreT_normal iha.2) hi hflat ihk.2⟩
  | opStop _ _ hflat hfl iha =>
    exact ⟨arity_opStop iha.1 hflat hfl,
      coreT_of_core (core_opStop iha.1 (core_of_coreT_normal iha.2) hflat hfl)⟩
  | blockOk har _ hvs _ ihb ihk =>
    exact ⟨arity_blockOk har ihb.1 hvs ihk.1,
      core_blockOk har ihb.1 (core_of_coreT_blockVals hvs ihb.2) hvs ihk.2⟩
  | blockBrk har _ ihb =>
    exact ⟨arity_blockBrk har ihb.1, coreT_blockAbrupt har ihb.1 ihb.2 (.inl ⟨_, _, rfl, rfl⟩)⟩
  | blockEsc har _ hfl ihb =>
    exact ⟨arity_blockEsc har ihb.1 hfl, coreT_blockAbrupt har ihb.1 ihb.2 (.inr ⟨hfl, rfl⟩)⟩
  | loopOk har _ _ ihb ihk =>
    exact ⟨arity_loopOk har ihb.1 ihk.1, core_loopOk har ihb.1 (core_of_coreT_normal ihb.2) ihk.2⟩
  | loopBack har _ _ ihb ihk =>
    exact ⟨arity_loopBack har ihb.1 ihk.1,
      core_loopBack har ihb.1 (core_of_coreT (fun _ h => by cases h) (by simp) ihb.2) ihk.2⟩
  | loopBrk har _ ihb =>
    exact ⟨arity_loopBrk har ihb.1, coreT_loopAbrupt har ihb.1 ihb.2 (.inl ⟨_, _, rfl, rfl⟩)⟩
  | loopEsc har _ hfl ihb =>
    exact ⟨arity_loopEsc har ihb.1 hfl, coreT_loopAbrupt har ihb.1 ihb.2 (.inr ⟨hfl, rfl⟩)⟩
  | ifOk _ hb har _ hvs _ ihc iharm ihk =>
    exact ⟨arity_ifOk ihc.1 har iharm.1 hvs ihk.1,
      core_ifOk ihc.1 (core_of_coreT_normal ihc.2) hb har iharm.1
        (core_of_coreT_blockVals hvs iharm.2) hvs ihk.2⟩
  | ifBrk _ hb har _ ihc iharm =>
    exact ⟨arity_ifBrk ihc.1 har iharm.1,
      coreT_ifAbrupt ihc.1 (core_of_coreT_normal ihc.2) hb har iharm.1 iharm.2 (.inl ⟨_, _, rfl, rfl⟩)⟩
  | ifEsc _ hb har _ hfl ihc iharm =>
    exact ⟨arity_ifEsc ihc.1 har iharm.1 hfl,
      coreT_ifAbrupt ihc.1 (core_of_coreT_normal ihc.2) hb har iharm.1 iharm.2 (.inr ⟨hfl, rfl⟩)⟩
  | ifAbort _ hfl ihc => exact ⟨arity_ifAbort ihc.1 hfl, coreT_ifAbort ihc.2 hfl⟩
  | callIndOk _ hres hfi hty hy hcall hvs _ iha ihk =>
    exact ⟨arityX_irOkT hC (.inl ⟨_, rfl⟩) iha.1 hfi hty hy hcall hvs ihk.1,
      coreX_irOkT hC (.inl ⟨_, rfl⟩) iha.1 (core_of_coreT_normal iha.2)
        (Silmaril.Wasm.Abstract.CallRes.steps_callIndirect_func hres) hfi hty hy hcall hvs ihk.2⟩
  | callIndRes _ hres iha =>
    exact ⟨arityX_irTrapT iha.1, coreT_of_core (coreX_irTrapT (core_of_coreT_normal iha.2)
      (Silmaril.Wasm.Abstract.CallRes.steps_callIndirect_trap hres))⟩
  | callIndStop _ hres hfi hty hy hcall hfl iha =>
    exact ⟨arityX_irStopT hC (.inl ⟨_, rfl⟩) iha.1 hfi hty hy hcall hfl,
      coreT_of_core (coreX_irStopT hC (.inl ⟨_, rfl⟩) iha.1 (core_of_coreT_normal iha.2)
        (Silmaril.Wasm.Abstract.CallRes.steps_callIndirect_func hres) hfi hty hy hcall hfl)⟩
  | callRefOk _ hfi hty hy hcall hvs _ iha ihk =>
    exact ⟨arityX_irOkT hC (.inr rfl) iha.1 hfi hty hy hcall hvs ihk.1,
      coreX_irOkT hC (.inr rfl) iha.1 (core_of_coreT_normal iha.2) .refl hfi hty hy hcall hvs ihk.2⟩
  | callRefNull _ iha =>
    exact ⟨arityX_irTrapT iha.1, coreT_of_core (coreX_irTrapT (core_of_coreT_normal iha.2)
      (.single (Step.callRefNull (c := .plain (.callRef _)) trivial)))⟩
  | callRefStop _ hfi hty hy hcall hfl iha =>
    exact ⟨arityX_irStopT hC (.inr rfl) iha.1 hfi hty hy hcall hfl,
      coreT_of_core (coreX_irStopT hC (.inr rfl) iha.1 (core_of_coreT_normal iha.2) .refl
        hfi hty hy hcall hfl)⟩
  | @tail s s₁ s₂ f f₁ stk stk₁ i args es fa fi ps rs fl _ hres hfi hty hcall hfl iha =>
    cases hres with
    | @direct x _ fi₀ _ hfi₀ =>
      obtain rfl : fi₀ = fi := Option.some.inj ((funcs_of_func? hfi₀).symm.trans hfi)
      exact ⟨arityT_returnCall hC iha.1 hfi₀ hty hcall hfl,
        coreT_returnCall hC iha.1 (core_of_coreT_normal iha.2) hfi₀ hty hcall hfl⟩
    | indirect hres' =>
      exact ⟨arityX_tailT iha.1 (.indirect hres') (fun _ h => by cases h),
        coreT_of_core (coreX_tailT iha.1 (.indirect hres') (fun _ h => by cases h))⟩
    | ref =>
      exact ⟨arityX_tailT iha.1 .ref (fun _ h => by cases h),
        coreT_of_core (coreX_tailT iha.1 .ref (fun _ h => by cases h))⟩
  | @tailRes s s₁ f f₁ stk stk₁ i args es _ hres iha =>
    have hnd : ∀ x, i ≠ Instr.returnCall x := fun x h => by subst h; cases hres
    exact ⟨arityX_tailT iha.1 hres hnd, coreT_of_core (coreX_tailT iha.1 hres hnd)⟩

end Silmaril.Wasm.Interp
