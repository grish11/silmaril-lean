module

public import Silmaril.Proofs.Wasm.Abstract.ExposeP.Expose
public import Silmaril.Proofs.Wasm.Abstract.ExposeE.Answer

/-!
Proofs for `Silmaril.Wasm.Abstract.ExposeP.Thms`: every finished path of the exposed body
`denListXP` whose call events are answered by `C` is an `EvalOXP C` derivation (`list_ansXP`).
With `evalOXP_path` this makes the exposure of the relation with pending tail calls exact.

The structural cases are `ExposeE`'s, read for body results `ResP`; the operator case reuses
`ExposeE`'s inverted heads (`HeadXE`, `headXE_ans`) through `liftP`, adds the typed indirect and
reference calls, and inverts a pending tail call (`tailPendEv`) to its resolution.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.ExposeP

open Silmaril.Wasm Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract
  Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Abstract.BodyTrace Silmaril.Wasm.Binaryen
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
  Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXP Silmaril.Wasm.Abstract.ExposeE
  Silmaril.Wasm.Abstract.ExposeP
  Silmaril.Elgot.ITree Silmaril.Proofs.Wasm.Abstract.StoreBody
  Silmaril.Proofs.Wasm.Abstract.BodyTrace Silmaril.Proofs.Wasm.Abstract.StoreCall
  Silmaril.Proofs.Wasm.Abstract.CallX Silmaril.Proofs.Wasm.Abstract.ExposeE
open Silmaril.Wasm.Abstract.CallXT (typeArity tailAnn)

variable {H : Type}

/-! ## Body results, inverted -/

theorem endRP_ok_inv {s₁ : Store H} {f₁ : Frame} {o : POut} {a : ResP} {t : St H}
    (h : endRP (s₁, f₁, o) = .val (.ok (a, t))) :
    o ≠ .flow .trap ∧ a = ⟨(f₁, o)⟩ ∧ t = ⟨s₁⟩ := by
  cases o with
  | flow fl => cases fl <;> simp_all [endRP]
  | tail => simp_all [endRP]

theorem endRP_err_inv {s₁ : Store H} {f₁ : Frame} {o : POut}
    (h : endRP (s₁, f₁, o) = .val (.error ⟨⟩)) : o = .flow .trap := by
  cases o with
  | flow fl => cases fl <;> simp_all [endRP]
  | tail => simp_all [endRP]

theorem endRP_ok {s₁ : Store H} {f₁ : Frame} {o : POut} (h : o ≠ .flow .trap) :
    endRP (s₁, f₁, o) = .val (.ok (⟨(f₁, o)⟩, ⟨s₁⟩)) := by
  cases o with
  | flow fl => cases fl <;> first | exact absurd rfl h | rfl
  | tail => rfl

theorem blockFlowP_trap {np nr : Nat} {stk : List Val} {o : POut} :
    blockFlowP np nr stk o = .flow .trap ↔ o = .flow .trap := by
  cases o with
  | flow fl =>
    simp only [blockFlowP, POut.flow.injEq]
    exact blockFlow_trap
  | tail => simp [blockFlowP]

theorem thenKP_pass_eq {K : Frame → List Val → M (CallSig H) H ResP} {f₁ : Frame} {o : POut}
    (h : ¬ o.IsNormal) : thenKP K ⟨(f₁, o)⟩ = pure ⟨(f₁, o)⟩ := by
  cases o with
  | flow fl =>
    cases fl
    case normal => exact absurd trivial h
    all_goals rfl
  | tail => rfl

theorem blockKP_eq (np nr : Nat) (stk : List Val) (f₁ : Frame) (o : POut) :
    (blockKP np nr stk ⟨(f₁, o)⟩ : M (CallSig H) H ResP) =
      pure ⟨(f₁, blockFlowP np nr stk o)⟩ := by
  cases o with
  | flow fl =>
    cases fl with
    | brk k vs => cases k <;> rfl
    | _ => rfl
  | tail => rfl

/-- The outcome of a loop body's exits. -/
def loopOutP (np nr : Nat) (stk : List Val) (f₁ : Frame) :
    POut → ResP ⊕ ULift.{1} (Frame × List Val)
  | .flow (.normal vs) => .inl ⟨(f₁, .flow (.normal (vs.take nr ++ stk.drop np)))⟩
  | .flow (.brk 0 vs) => .inr ⟨(f₁, vs.take np ++ stk.drop np)⟩
  | .flow (.brk (k + 1) vs) => .inl ⟨(f₁, .flow (.brk k vs))⟩
  | o => .inl ⟨(f₁, o)⟩

theorem loopKP_eq (np nr : Nat) (stk : List Val) (f₁ : Frame) (o : POut) :
    (loopKP np nr stk ⟨(f₁, o)⟩ : M (CallSig H) H _) = pure (loopOutP np nr stk f₁ o) := by
  cases o with
  | flow fl =>
    cases fl with
    | brk k vs => cases k <;> rfl
    | _ => rfl
  | tail => rfl

theorem loopOutP_inl {np nr : Nat} {stk : List Val} {f₁ : Frame} {o : POut} {b : ResP}
    (h : loopOutP np nr stk f₁ o = .inl b) :
    (∃ vs, o = .flow (.normal vs) ∧ b = ⟨(f₁, .flow (.normal (vs.take nr ++ stk.drop np)))⟩) ∨
      (∃ k vs, o = .flow (.brk (k + 1) vs) ∧ b = ⟨(f₁, .flow (.brk k vs))⟩) ∨
      (o.Escapes ∧ b = ⟨(f₁, o)⟩) := by
  cases o with
  | flow fl =>
    cases fl with
    | normal vs => cases h; exact .inl ⟨vs, rfl, rfl⟩
    | brk k vs =>
      cases k with
      | zero => cases h
      | succ k => cases h; exact .inr (.inl ⟨k, vs, rfl, rfl⟩)
    | ret vs => cases h; exact .inr (.inr ⟨trivial, rfl⟩)
    | trap => cases h; exact .inr (.inr ⟨trivial, rfl⟩)
    | throw a => cases h; exact .inr (.inr ⟨trivial, rfl⟩)
  | tail => cases h; exact .inr (.inr ⟨trivial, rfl⟩)

theorem loopOutP_inr {np nr : Nat} {stk : List Val} {f₁ : Frame} {o : POut}
    {c : ULift.{1} (Frame × List Val)} (h : loopOutP np nr stk f₁ o = .inr c) :
    ∃ vs, o = .flow (.brk 0 vs) ∧ c = ⟨(f₁, vs.take np ++ stk.drop np)⟩ := by
  cases o with
  | flow fl =>
    cases fl with
    | brk k vs =>
      cases k with
      | zero => cases h; exact ⟨vs, rfl, rfl⟩
      | succ k => cases h
    | _ => cases h
  | tail => cases h

/-! ## Operators, inverted -/

theorem path_callAtT_inv {y : TypeIdx} {fa : Nat} {f : Frame} {stk : List Val} {s : Store H}
    {cs : List (Call (CallSig H))} {e : PathEnd (Except PUnit.{2} (Res × St H))}
    (h : Path (run' (callAtT y fa f stk) ⟨s⟩) cs e) (he : e ≠ .div) :
    calleeTyped s f y fa ∧ Path (run' (callAt fa f stk) ⟨s⟩) cs e := by
  rw [callAtT, run_getState_bind] at h
  by_cases ht : calleeTyped s f y fa
  · simp only [ht, ↓reduceIte] at h
    exact ⟨ht, h⟩
  · simp only [ht, ↓reduceIte] at h
    exact absurd (path_stuck_inv h) he

theorem path_indEvT_inv {x : TableIdx} {y : TypeIdx} {f : Frame} {stk : List Val} {s : Store H}
    {cs : List (Call (CallSig H))} {e : PathEnd (Except PUnit.{2} (Res × St H))}
    (h : Path (run' (indEvT x y f stk) ⟨s⟩) cs e) (he : e ≠ .div) :
    (∃ fa stk₁, IndResS s f x y stk (some fa, stk₁) ∧ calleeTyped s f y fa ∧
        Path (run' (callAt fa f stk₁) ⟨s⟩) cs e) ∨
      (∃ stk₁, IndResS s f x y stk (none, stk₁) ∧ cs = [] ∧ e = .val (.error ⟨⟩)) := by
  rw [indEvT, run_getState_bind] at h
  cases hr : resolveInd s f x y stk with
  | none =>
    simp only [hr] at h
    exact absurd (path_stuck_inv h) he
  | some p =>
    obtain ⟨o, stk₁⟩ := p
    have hs := resolveInd_spec hr
    cases o with
    | some fa =>
      simp only [hr] at h
      obtain ⟨ht, hp⟩ := path_callAtT_inv h he
      exact .inl ⟨fa, stk₁, hs, ht, hp⟩
    | none =>
      simp only [hr] at h
      obtain ⟨rfl, rfl⟩ := path_ret_inv (run_trapS _) h
      exact .inr ⟨stk₁, hs, rfl, rfl⟩

theorem path_refEvT_inv {y : TypeIdx} {f : Frame} {stk : List Val} {s : Store H}
    {cs : List (Call (CallSig H))} {e : PathEnd (Except PUnit.{2} (Res × St H))}
    (h : Path (run' (refEvT y f stk) ⟨s⟩) cs e) (he : e ≠ .div) :
    (∃ fa stk₁, stk = .ref (.func fa) :: stk₁ ∧ calleeTyped s f y fa ∧
        Path (run' (callAt fa f stk₁) ⟨s⟩) cs e) ∨
      (∃ stk₁, stk = .ref .null :: stk₁ ∧ cs = [] ∧ e = .val (.error ⟨⟩)) := by
  unfold refEvT at h
  split at h
  · obtain ⟨ht, hp⟩ := path_callAtT_inv h he
    exact .inl ⟨_, _, rfl, ht, hp⟩
  · obtain ⟨rfl, rfl⟩ := path_ret_inv (run_trapS _) h
    exact .inr ⟨_, rfl, rfl, rfl⟩
  · exact absurd (path_stuck_inv h) he

theorem path_tailPendEv_inv {i : Instr} {f : Frame} {stk : List Val} {s : Store H}
    {cs : List (Call (CallSig H))} {v : Except PUnit.{2} (ResP × St H)}
    (h : Path (run' (tailPendEv i f stk) ⟨s⟩) cs (.val v)) :
    cs = [] ∧
      ((∃ fa stk₁ fi ps rs, TailRes s f i stk (some (fa, stk₁)) ∧ s.funcs[fa]? = some fi ∧
          Validation.DefType.funcType? fi.type = some (ps, rs) ∧ tailTyped i f ps rs ∧
          v = .ok (⟨(f, .tail fa (stk₁.take ps.length).reverse rs.length)⟩, ⟨s⟩)) ∨
        (TailRes s f i stk none ∧ v = .error ⟨⟩)) := by
  rw [tailPendEv, run_getState_bind] at h
  cases hr : resolveTail s f i stk with
  | none =>
    simp only [hr] at h
    exact absurd (path_stuck_inv h) (by simp)
  | some o =>
    have hs := resolveTail_spec hr
    cases o with
    | none =>
      simp only [hr] at h
      obtain ⟨rfl, hv⟩ := path_ret_inv (run_trapS _) h
      cases hv
      exact ⟨rfl, .inr ⟨hs, rfl⟩⟩
    | some p =>
      obtain ⟨fa, stk₁⟩ := p
      simp only [hr] at h
      cases hfi : s.funcs[fa]? with
      | none =>
        simp only [hfi] at h
        exact absurd (path_stuck_inv h) (by simp)
      | some fi =>
        simp only [hfi] at h
        cases hty : Validation.DefType.funcType? fi.type with
        | none =>
          simp only [hty] at h
          exact absurd (path_stuck_inv h) (by simp)
        | some q =>
          obtain ⟨ps, rs⟩ := q
          simp only [hty] at h
          by_cases ht : tailTyped i f ps rs
          · simp only [ht, ↓reduceIte] at h
            obtain ⟨rfl, hv⟩ := path_pure_inv h
            cases hv
            exact ⟨rfl, .inl ⟨fa, stk₁, fi, ps, rs, hs, hfi, hty, ht, rfl⟩⟩
          · simp only [ht, ↓reduceIte] at h
            exact absurd (path_stuck_inv h) (by simp)

section
variable {C : CallRel H}

/-- A lifted computation's finished path is its flow computation's, read as a body result. -/
theorem liftP_ans {x : M (CallSig H) H Res} {s : St H} {cs : List (Call (CallSig H))}
    {v : Except PUnit.{2} (ResP × St H)} {P : Store H × Frame × Flow → Prop}
    (hA : Answered C cs) (h : Path (run' (liftP x) s) cs (.val v))
    (hx : ∀ cs₁ v', Answered C cs₁ → Path (run' x s) cs₁ (.val v') →
      ∃ r₀, P r₀ ∧ endR r₀ = .val v') :
    ∃ r₀, P r₀ ∧ endRP (r₀.1, r₀.2.1, .flow r₀.2.2) = .val v := by
  rcases path_run_bind_inv h (by simp) with ⟨c₁, c₂, a, s₁, rfl, h₁, h₂⟩ | ⟨h₁, hv⟩
  · obtain ⟨-, hv⟩ := path_pure_inv h₂
    cases hv
    obtain ⟨⟨s₀, f₀, fl⟩, hP, hend⟩ := hx c₁ _ (answered_left hA) h₁
    obtain ⟨hnt, rfl, rfl⟩ := endR_ok_inv hend
    exact ⟨_, hP, endRP_ok (fun h => hnt (POut.flow.inj h))⟩
  · obtain ⟨⟨s₀, f₀, fl⟩, hP, hend⟩ := hx cs _ hA h₁
    obtain rfl := endR_err_inv hend
    cases hv
    exact ⟨_, hP, rfl⟩

/-- Finished, answered paths of the exposed body of `es` are `EvalOXP C` derivations. -/
def LAnsXP (C : CallRel H) (es : List BExpr) : Prop :=
  ∀ s f stk cs e, Answered C cs →
    Path (run' (denListXP es f stk : M (CallSig H) H ResP) ⟨s⟩) cs e → e ≠ .div →
    ∃ r, EvalOXP C s f stk es r ∧ endRP r = e

/-- A head computation followed by the continuation `es`. -/
theorem cont_ansXP {es : List BExpr} (hes : LAnsXP C es) {x : M (CallSig H) H ResP} {s : St H}
    {cs : List (Call (CallSig H))} {ee : PathEnd (Except PUnit.{2} (ResP × St H))}
    {Q : Store H × Frame × POut → Prop} (hA : Answered C cs)
    (h : Path (run' (x >>= thenKP (denListXP es)) s) cs ee) (he : ee ≠ .div)
    (hx : ∀ cs₁ v, Answered C cs₁ → Path (run' x s) cs₁ (.val v) →
      ∃ r₀, Q r₀ ∧ endRP r₀ = .val v) :
    ∃ r₀, Q r₀ ∧ (∀ stk', r₀.2.2 = .flow (.normal stk') →
        ∃ r, EvalOXP C r₀.1 r₀.2.1 stk' es r ∧ endRP r = ee) ∧
      (¬ r₀.2.2.IsNormal → ee = endRP r₀) := by
  rcases path_run_bind_inv h he with ⟨cs₁, cs₂, a, s₁, rfl, h₁, h₂⟩ | ⟨h₁, rfl⟩
  · obtain ⟨⟨s₀, f₀, o⟩, hQ, hend⟩ := hx cs₁ _ (answered_left hA) h₁
    obtain ⟨-, rfl, rfl⟩ := endRP_ok_inv hend
    refine ⟨_, hQ, fun stk' hn => ?_, fun hn => ?_⟩
    · simp only at hn; subst hn
      exact hes s₀ f₀ stk' cs₂ ee (answered_right hA) h₂ he
    · rw [thenKP_pass_eq hn] at h₂
      obtain ⟨-, rfl⟩ := path_pure_inv h₂
      exact hend.symm
  · obtain ⟨⟨s₀, f₀, o⟩, hQ, hend⟩ := hx cs _ hA h₁
    obtain rfl := endRP_err_inv hend
    exact ⟨_, hQ, fun _ hn => (by cases hn), fun _ => hend.symm⟩

/-- The outcome of an operator on the stack `stk₁` its arguments left, every call answered by
`C`: `ExposeE`'s heads for the operators without extended call forms, the typed indirect and
reference calls, and a pending tail call. -/
inductive HeadXP (C : CallRel H) (s₁ : Store H) (f₁ : Frame) (stk₁ : List Val) :
    Instr → Store H × Frame × POut → Prop
  | ofE {i : Instr} {r₀ : Store H × Frame × Flow} (hx : isXCall i = false)
      (h : HeadXE C s₁ f₁ stk₁ i r₀) : HeadXP C s₁ f₁ stk₁ i (r₀.1, r₀.2.1, .flow r₀.2.2)
  | indRet {x : TableIdx} {y : TypeIdx} {fa : Nat} {stk' : List Val} {fi : FuncInst H}
      {ps rs : List Validation.CValType} {s₂ : Store H} {fl : Flow} {vs : List Val}
      (hres : IndResS s₁ f₁ x y stk₁ (some fa, stk')) (hfi : s₁.funcs[fa]? = some fi)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length))
      (hC : C s₁ fa (stk'.take ps.length).reverse (s₂, fl)) (hvs : fl.retVals = some vs) :
      HeadXP C s₁ f₁ stk₁ (.callIndirect x y)
        (s₂, f₁, .flow (.normal (vs.take rs.length ++ stk'.drop ps.length)))
  | indStop {x : TableIdx} {y : TypeIdx} {fa : Nat} {stk' : List Val} {fi : FuncInst H}
      {ps rs : List Validation.CValType} {s₂ : Store H} {fl : Flow}
      (hres : IndResS s₁ f₁ x y stk₁ (some fa, stk')) (hfi : s₁.funcs[fa]? = some fi)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length))
      (hC : C s₁ fa (stk'.take ps.length).reverse (s₂, fl)) (hfl : fl.Abrupt) :
      HeadXP C s₁ f₁ stk₁ (.callIndirect x y) (s₂, f₁, .flow fl)
  | indRes {x : TableIdx} {y : TypeIdx} {stk' : List Val}
      (hres : IndResS s₁ f₁ x y stk₁ (none, stk')) :
      HeadXP C s₁ f₁ stk₁ (.callIndirect x y) (s₁, f₁, .flow .trap)
  | refRet {y : TypeIdx} {fa : Nat} {stk' : List Val} {fi : FuncInst H}
      {ps rs : List Validation.CValType} {s₂ : Store H} {fl : Flow} {vs : List Val}
      (hstk : stk₁ = .ref (.func fa) :: stk') (hfi : s₁.funcs[fa]? = some fi)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length))
      (hC : C s₁ fa (stk'.take ps.length).reverse (s₂, fl)) (hvs : fl.retVals = some vs) :
      HeadXP C s₁ f₁ stk₁ (.callRef y)
        (s₂, f₁, .flow (.normal (vs.take rs.length ++ stk'.drop ps.length)))
  | refStop {y : TypeIdx} {fa : Nat} {stk' : List Val} {fi : FuncInst H}
      {ps rs : List Validation.CValType} {s₂ : Store H} {fl : Flow}
      (hstk : stk₁ = .ref (.func fa) :: stk') (hfi : s₁.funcs[fa]? = some fi)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : typeArity f₁.module y = some (ps.length, rs.length))
      (hC : C s₁ fa (stk'.take ps.length).reverse (s₂, fl)) (hfl : fl.Abrupt) :
      HeadXP C s₁ f₁ stk₁ (.callRef y) (s₂, f₁, .flow fl)
  | refNull {y : TypeIdx} {stk' : List Val} (hstk : stk₁ = .ref .null :: stk') :
      HeadXP C s₁ f₁ stk₁ (.callRef y) (s₁, f₁, .flow .trap)
  | tail {i : Instr} {fa : Nat} {stk' : List Val} {fi : FuncInst H}
      {ps rs : List Validation.CValType}
      (hres : TailRes s₁ f₁ i stk₁ (some (fa, stk'))) (hfi : s₁.funcs[fa]? = some fi)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hy : ∀ y, tailAnn i = some y → typeArity f₁.module y = some (ps.length, rs.length)) :
      HeadXP C s₁ f₁ stk₁ i (s₁, f₁, .tail fa (stk'.take ps.length).reverse rs.length)
  | tailRes {i : Instr} (hres : TailRes s₁ f₁ i stk₁ none) :
      HeadXP C s₁ f₁ stk₁ i (s₁, f₁, .flow .trap)

/-- The outcomes of an operator node's head. -/
def OpHeadXP (C : CallRel H) (s : Store H) (f : Frame) (stk : List Val) (i : Instr)
    (args : List BExpr) (r₀ : Store H × Frame × POut) : Prop :=
  (¬ r₀.2.2.IsNormal ∧ EvalOXP C s f stk args r₀) ∨
  ∃ s₁ f₁ stk₁, EvalOXP C s f stk args (s₁, f₁, .flow (.normal stk₁)) ∧
    HeadXP C s₁ f₁ stk₁ i r₀

/-- The head of an operator node, on the stack its arguments left. -/
theorem headXP_ans {i : Instr} {s₀ : Store H} {f₀ : Frame} {stk₁ : List Val}
    {c₂ : List (Call (CallSig H))} {v : Except PUnit.{2} (ResP × St H)} (hA : Answered C c₂)
    (h : Path (run' (opCXP i f₀ stk₁ : M (CallSig H) H ResP) ⟨s₀⟩) c₂ (.val v)) :
    ∃ r₀, HeadXP C s₀ f₀ stk₁ i r₀ ∧ endRP r₀ = .val v := by
  cases hx : isXCall i with
  | false =>
    rw [opCXP_notX hx] at h
    obtain ⟨r₀, hh, hr⟩ := liftP_ans (P := HeadXE C s₀ f₀ stk₁ i) hA h
      fun cs₁ v' hA₁ h₁ => headXE_ans hA₁ h₁
    exact ⟨_, .ofE hx hh, hr⟩
  | true =>
    obtain ⟨x, y, rfl⟩ | ⟨y, rfl⟩ | htail :
        (∃ x y, i = .callIndirect x y) ∨ (∃ y, i = .callRef y) ∨ isXTail i := by
      cases i <;> simp_all [isXCall, isXTail]
    · change Path (run' (liftP (indEvT x y f₀ stk₁)) ⟨s₀⟩) c₂ (.val v) at h
      obtain ⟨r₀, hh, hr⟩ := liftP_ans
        (P := fun r₀ => HeadXP C s₀ f₀ stk₁ (.callIndirect x y) (r₀.1, r₀.2.1, .flow r₀.2.2))
        hA h fun cs₁ v' hA₁ h₁ => by
          rcases path_indEvT_inv h₁ (by simp) with ⟨fa, stk', hres, ht, hp⟩ | ⟨stk', hres, -, hv⟩
          · obtain ⟨fi, ps, rs, hfi, hty, s₂, fl, hC, ⟨vs, hvs, hv⟩ | ⟨hfl, hv⟩⟩ :=
              callAt_ans hA₁ hp
            · exact ⟨_, .indRet hres hfi hty (ht fi ps rs hfi hty) hC hvs, hv.symm⟩
            · exact ⟨_, .indStop hres hfi hty (ht fi ps rs hfi hty) hC hfl, hv.symm⟩
          · cases hv
            exact ⟨(s₀, f₀, .trap), .indRes hres, rfl⟩
      exact ⟨_, hh, hr⟩
    · change Path (run' (liftP (refEvT y f₀ stk₁)) ⟨s₀⟩) c₂ (.val v) at h
      obtain ⟨r₀, hh, hr⟩ := liftP_ans
        (P := fun r₀ => HeadXP C s₀ f₀ stk₁ (.callRef y) (r₀.1, r₀.2.1, .flow r₀.2.2))
        hA h fun cs₁ v' hA₁ h₁ => by
          rcases path_refEvT_inv h₁ (by simp) with ⟨fa, stk', hstk, ht, hp⟩ | ⟨stk', hstk, -, hv⟩
          · obtain ⟨fi, ps, rs, hfi, hty, s₂, fl, hC, ⟨vs, hvs, hv⟩ | ⟨hfl, hv⟩⟩ :=
              callAt_ans hA₁ hp
            · exact ⟨_, .refRet hstk hfi hty (ht fi ps rs hfi hty) hC hvs, hv.symm⟩
            · exact ⟨_, .refStop hstk hfi hty (ht fi ps rs hfi hty) hC hfl, hv.symm⟩
          · cases hv
            exact ⟨(s₀, f₀, .trap), .refNull hstk, rfl⟩
      exact ⟨_, hh, hr⟩
    · rw [opCXP_tail htail] at h
      obtain ⟨-, ⟨fa, stk', fi, ps, rs, hres, hfi, hty, ht, rfl⟩ | ⟨hres, rfl⟩⟩ :=
        path_tailPendEv_inv h
      · exact ⟨_, .tail hres hfi hty ht, rfl⟩
      · exact ⟨_, .tailRes hres, rfl⟩

theorem opHeadXP_ans {i : Instr} {args : List BExpr} (hargs : LAnsXP C args) {s : Store H}
    {f : Frame} {stk : List Val} (cs₁ : List (Call (CallSig H)))
    (v : Except PUnit.{2} (ResP × St H)) (hA : Answered C cs₁)
    (h : Path (run' (denListXP args f stk >>= thenKP (opCXP i) : M (CallSig H) H ResP)
      ⟨s⟩) cs₁ (.val v)) :
    ∃ r₀, OpHeadXP C s f stk i args r₀ ∧ endRP r₀ = .val v := by
  rcases path_run_bind_inv h (by simp) with ⟨c₁, c₂, a, s₁, rfl, h₁, h₂⟩ | ⟨h₁, hv⟩
  · obtain ⟨⟨s₀, f₀, o⟩, hev, hend⟩ := hargs s f stk c₁ _ (answered_left hA) h₁ (by simp)
    obtain ⟨hnt, rfl, rfl⟩ := endRP_ok_inv hend
    by_cases hn : o.IsNormal
    · obtain ⟨stk₁, rfl⟩ : ∃ stk₁, o = .flow (.normal stk₁) := by
        rcases o with fl | _
        · cases fl <;> first | exact ⟨_, rfl⟩ | exact absurd hn id
        · exact absurd hn id
      have h₂' : Path (run' (opCXP i f₀ stk₁ : M (CallSig H) H ResP) ⟨s₀⟩) c₂ (.val v) := h₂
      obtain ⟨r₀, hhead, hr₀⟩ := headXP_ans (answered_right hA) h₂'
      exact ⟨r₀, .inr ⟨s₀, f₀, stk₁, hev, hhead⟩, hr₀⟩
    · rw [thenKP_pass_eq hn] at h₂
      obtain ⟨-, hv⟩ := path_pure_inv h₂
      cases hv
      exact ⟨_, .inl ⟨hn, hev⟩, hend⟩
  · obtain ⟨⟨s₀, f₀, o⟩, hev, hend⟩ := hargs s f stk cs₁ _ hA h₁ (by simp)
    obtain rfl := endRP_err_inv hend
    cases hv
    exact ⟨_, .inl ⟨notNormal_flowP Flow.notNormal_trap, hev⟩, hend⟩

/-- An operator head of `ExposeE`'s (no extended call form) with its continuation. -/
theorem ofE_ansXP {i : Instr} {args es : List BExpr} {s s₁ : Store H} {f f₁ : Frame}
    {stk stk₁ : List Val} {ee : PathEnd (Except PUnit.{2} (ResP × St H))}
    {r₀ : Store H × Frame × Flow} (hx : isXCall i = false) (hh : HeadXE C s₁ f₁ stk₁ i r₀)
    (hev : EvalOXP C s f stk args (s₁, f₁, .flow (.normal stk₁)))
    (hnorm : ∀ stk', r₀.2.2 = .normal stk' →
      ∃ r, EvalOXP C r₀.1 r₀.2.1 stk' es r ∧ endRP r = ee)
    (hnon : ¬ r₀.2.2.IsNormal → ee = endRP (r₀.1, r₀.2.1, .flow r₀.2.2)) :
    ∃ r, EvalOXP C s f stk (.op i args :: es) r ∧ endRP r = ee := by
  cases hh with
  | throw ht he hn =>
    exact ⟨_, .throw hev ht he hn, (hnon Flow.notNormal_throw).symm⟩
  | throwRefNull hstk =>
    subst hstk
    exact ⟨_, .throwRefNull hev, (hnon Flow.notNormal_trap).symm⟩
  | throwRefExn hstk =>
    subst hstk
    exact ⟨_, .throwRefExn hev, (hnon Flow.notNormal_throw).symm⟩
  | ofX hh =>
    cases hh with
    | @flat i r₀ hi hflat =>
      obtain ⟨s₂, f₂, fl₂⟩ := r₀
      by_cases hn : fl₂.IsNormal
      · obtain ⟨stk₂, rfl⟩ : ∃ stk₂, fl₂ = .normal stk₂ := by
          cases fl₂ <;> first | exact ⟨_, rfl⟩ | exact absurd hn id
        obtain ⟨r, hk, hr⟩ := hnorm stk₂ rfl
        exact ⟨r, .opOk hi hev hflat hk, hr⟩
      · exact ⟨_, .opStop hi hev hflat hn, (hnon hn).symm⟩
    | callRet hfi hty hC hvs =>
      obtain ⟨r, hk, hr⟩ := hnorm _ rfl
      exact ⟨r, .callOk hev hfi hty hC hvs hk, hr⟩
    | callTrap hfi hty hC =>
      exact ⟨_, .callTrap hev hfi hty hC, (hnon Flow.notNormal_trap).symm⟩
    | callThrow hfi hty hC =>
      exact ⟨_, .callThrow hev hfi hty hC, (hnon Flow.notNormal_throw).symm⟩
    | indRet => simp [isXCall] at hx
    | indStop => simp [isXCall] at hx
    | indRes => simp [isXCall] at hx
    | refRet => simp [isXCall] at hx
    | refStop => simp [isXCall] at hx
    | refNull => simp [isXCall] at hx
    | tail hres => cases hres <;> simp [isXCall] at hx
    | tailRes hres => cases hres <;> simp [isXCall] at hx

/-- An `op` tree with its continuation. -/
theorem op_ansXP {i : Instr} {args es : List BExpr} (hargs : LAnsXP C args) (hes : LAnsXP C es)
    {s : Store H} {f : Frame} {stk : List Val} {cs : List (Call (CallSig H))}
    {ee : PathEnd (Except PUnit.{2} (ResP × St H))} (hA : Answered C cs)
    (h : Path (run' (denXP (.op i args) f stk >>= thenKP (denListXP es)) ⟨s⟩) cs ee)
    (he : ee ≠ .div) : ∃ r, EvalOXP C s f stk (.op i args :: es) r ∧ endRP r = ee := by
  rw [denXP_op] at h
  obtain ⟨r₀, hQ, hnorm, hnon⟩ := cont_ansXP hes hA h he (opHeadXP_ans hargs)
  rcases hQ with ⟨hn, hev⟩ | ⟨s₁, f₁, stk₁, hev, hhead⟩
  · exact ⟨r₀, .argsAbort hev hn, (hnon hn).symm⟩
  cases hhead with
  | ofE hx hh =>
    exact ofE_ansXP hx hh hev (fun stk' h => hnorm stk' (congrArg POut.flow h)) hnon
  | indRet hres hfi hty hy hC hvs =>
    obtain ⟨ad, j, rfl, hres⟩ := hres
    obtain ⟨r, hk, hr⟩ := hnorm _ rfl
    exact ⟨r, .callIndOk hev hres hfi hty hy hC hvs hk, hr⟩
  | @indStop x y fa stk' fi ps rs s₂ fl hres hfi hty hy hC hfl =>
    obtain ⟨ad, j, rfl, hres⟩ := hres
    exact ⟨_, .callIndStop hev hres hfi hty hy hC hfl,
      (hnon (notNormal_flowP (abrupt_notNormal hfl))).symm⟩
  | indRes hres =>
    obtain ⟨ad, j, rfl, hres⟩ := hres
    exact ⟨_, .callIndRes hev hres, (hnon (notNormal_flowP Flow.notNormal_trap)).symm⟩
  | refRet hstk hfi hty hy hC hvs =>
    subst hstk
    obtain ⟨r, hk, hr⟩ := hnorm _ rfl
    exact ⟨r, .callRefOk hev hfi hty hy hC hvs hk, hr⟩
  | @refStop y fa stk' fi ps rs s₂ fl hstk hfi hty hy hC hfl =>
    subst hstk
    exact ⟨_, .callRefStop hev hfi hty hy hC hfl,
      (hnon (notNormal_flowP (abrupt_notNormal hfl))).symm⟩
  | refNull hstk =>
    subst hstk
    exact ⟨_, .callRefNull hev, (hnon (notNormal_flowP Flow.notNormal_trap)).symm⟩
  | tail hres hfi hty hy =>
    obtain rfl := tailRes_drop hres
    exact ⟨_, .tail hev hres hfi hty hy, (hnon notNormal_tailP).symm⟩
  | tailRes hres =>
    exact ⟨_, .tailRes hev hres, (hnon (notNormal_flowP Flow.notNormal_trap)).symm⟩

end

section
variable {C : CallRel H}

def BlockHeadXP (C : CallRel H) (s : Store H) (f : Frame) (stk : List Val) (bt : BlockType)
    (body : List BExpr) (r₀ : Store H × Frame × POut) : Prop :=
  ∃ np nr s₁ f₁ o, arity f bt = some (np, nr) ∧ EvalOXP C s f (stk.take np) body (s₁, f₁, o) ∧
    r₀ = (s₁, f₁, blockFlowP np nr stk o)

theorem blockArm_ansXP {L : List BExpr} (hL : LAnsXP C L) {np nr : Nat} {stk : List Val}
    {s : Store H} {f : Frame} {stk' : List Val} (cs₁ : List (Call (CallSig H)))
    (v : Except PUnit.{2} (ResP × St H)) (hA : Answered C cs₁)
    (h : Path (run' (denListXP L f stk' >>= blockKP np nr stk : M (CallSig H) H ResP) ⟨s⟩)
      cs₁ (.val v)) :
    ∃ s₁ f₁ o, EvalOXP C s f stk' L (s₁, f₁, o) ∧
      endRP (s₁, f₁, blockFlowP np nr stk o) = .val v := by
  rcases path_run_bind_inv h (by simp) with ⟨c₁, c₂, a, t, rfl, h₁, h₂⟩ | ⟨h₁, hv⟩
  · obtain ⟨⟨s₁, f₁, o⟩, hev, hend⟩ := hL s f stk' c₁ _ (answered_left hA) h₁ (by simp)
    obtain ⟨hnt, rfl, rfl⟩ := endRP_ok_inv hend
    rw [blockKP_eq] at h₂
    obtain ⟨-, hv⟩ := path_pure_inv h₂
    cases hv
    exact ⟨s₁, f₁, o, hev, endRP_ok (fun h => hnt (blockFlowP_trap.1 h))⟩
  · obtain ⟨⟨s₁, f₁, o⟩, hev, hend⟩ := hL s f stk' cs₁ _ hA h₁ (by simp)
    obtain rfl := endRP_err_inv hend
    cases hv
    exact ⟨s₁, f₁, .flow .trap, hev, rfl⟩

theorem block_ansXP {bt : BlockType} {body es : List BExpr} (hbody : LAnsXP C body)
    (hes : LAnsXP C es) {s : Store H} {f : Frame} {stk : List Val}
    {cs : List (Call (CallSig H))} {ee : PathEnd (Except PUnit.{2} (ResP × St H))}
    (hA : Answered C cs)
    (h : Path (run' (denXP (.block bt body) f stk >>= thenKP (denListXP es)) ⟨s⟩) cs ee)
    (he : ee ≠ .div) : ∃ r, EvalOXP C s f stk (.block bt body :: es) r ∧ endRP r = ee := by
  rw [denXP_block] at h
  cases har : arity f bt with
  | none =>
    simp only [har] at h
    rcases path_run_bind_inv h he with ⟨_, _, _, _, _, h₁, _⟩ | ⟨h₁, _⟩
    · exact absurd (path_stuck_inv h₁) (by simp)
    · exact absurd (path_stuck_inv h₁) (by simp)
  | some p =>
    obtain ⟨np, nr⟩ := p
    simp only [har] at h
    obtain ⟨r₀, ⟨np', nr', s₁, f₁, o, har', hev, rfl⟩, hnorm, hnon⟩ :=
      cont_ansXP (Q := BlockHeadXP C s f stk bt body) hes hA h he fun cs₁ v hA₁ h₁ => by
        obtain ⟨s₁, f₁, o, hev, hend⟩ := blockArm_ansXP hbody cs₁ v hA₁ h₁
        exact ⟨_, ⟨np, nr, s₁, f₁, o, har, hev, rfl⟩, hend⟩
    rw [har] at har'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj har')
    cases o with
    | flow fl =>
      cases fl with
      | normal vs =>
        obtain ⟨r, hk, hr⟩ := hnorm _ rfl
        exact ⟨r, .blockOk har hev rfl hk, hr⟩
      | brk k vs =>
        cases k with
        | zero =>
          obtain ⟨r, hk, hr⟩ := hnorm _ rfl
          exact ⟨r, .blockOk har hev rfl hk, hr⟩
        | succ k =>
          exact ⟨_, .blockBrk har hev, (hnon (notNormal_flowP Flow.notNormal_brk)).symm⟩
      | ret vs =>
        exact ⟨_, .blockEsc har hev trivial, (hnon (notNormal_flowP Flow.notNormal_ret)).symm⟩
      | trap =>
        exact ⟨_, .blockEsc har hev trivial, (hnon (notNormal_flowP Flow.notNormal_trap)).symm⟩
      | throw t =>
        exact ⟨_, .blockEsc har hev trivial, (hnon (notNormal_flowP Flow.notNormal_throw)).symm⟩
    | tail => exact ⟨_, .blockEsc har hev trivial, (hnon notNormal_tailP).symm⟩

end

section
variable {C : CallRel H}

/-- The outcomes of an `if`'s head. -/
def IfHeadXP (C : CallRel H) (s : Store H) (f : Frame) (stk : List Val) (bt : BlockType)
    (c t el : List BExpr) (r₀ : Store H × Frame × POut) : Prop :=
  (¬ r₀.2.2.IsNormal ∧ EvalOXP C s f stk c r₀) ∨
  ∃ s₁ f₁ cv stk₁ b np nr s₂ f₂ o,
    EvalOXP C s f stk c (s₁, f₁, .flow (.normal (cv :: stk₁))) ∧
    truthy cv = some b ∧ arity f₁ bt = some (np, nr) ∧
    EvalOXP C s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, o) ∧
    r₀ = (s₂, f₂, blockFlowP np nr stk₁ o)

theorem ifHead_ansXP {bt : BlockType} {c t el : List BExpr} (hc : LAnsXP C c)
    (ht : LAnsXP C t) (hel : LAnsXP C el) {s : Store H} {f : Frame} {stk : List Val}
    (cs₁ : List (Call (CallSig H))) (v : Except PUnit.{2} (ResP × St H)) (hA₁ : Answered C cs₁)
    (h₁ : Path (run' (denListXP c f stk >>= fun r =>
        match r with
        | ⟨(f₁, .flow (.normal (cv :: stk₁)))⟩ =>
          match truthy cv, arity f₁ bt with
          | some b, some (np, nr) =>
            (if b then denListXP t f₁ (stk₁.take np) else
              denListXP el f₁ (stk₁.take np)) >>= blockKP np nr stk₁
          | _, _ => stuck
        | ⟨(_, .flow (.normal []))⟩ => stuck
        | r => pure r : M (CallSig H) H ResP) ⟨s⟩) cs₁ (.val v)) :
    ∃ r₀, IfHeadXP C s f stk bt c t el r₀ ∧ endRP r₀ = .val v := by
  rcases path_run_bind_inv h₁ (by simp) with ⟨c₁, c₂, a, t', rfl, h₁, h₂⟩ | ⟨h₁, hv⟩
  · obtain ⟨⟨s₁, f₁, o⟩, hev, hend⟩ := hc s f stk c₁ _ (answered_left hA₁) h₁ (by simp)
    obtain ⟨hnt, rfl, rfl⟩ := endRP_ok_inv hend
    by_cases hn : o.IsNormal
    · obtain ⟨stk₁, rfl⟩ : ∃ stk₁, o = .flow (.normal stk₁) := by
        rcases o with fl | _
        · cases fl <;> first | exact ⟨_, rfl⟩ | exact absurd hn id
        · exact absurd hn id
      rcases stk₁ with _ | ⟨cv, stk₁⟩
      · exact absurd (path_stuck_inv h₂) (by simp)
      cases hb : truthy cv with
      | none => simp only [hb] at h₂; exact absurd (path_stuck_inv h₂) (by simp)
      | some b =>
        cases har : arity f₁ bt with
        | none => simp only [hb, har] at h₂; exact absurd (path_stuck_inv h₂) (by simp)
        | some p =>
          obtain ⟨np, nr⟩ := p
          simp only [hb, har] at h₂
          have hL : LAnsXP C (if b then t else el) := by cases b <;> assumption
          have h₂' : Path (run' (denListXP (if b then t else el) f₁ (stk₁.take np) >>=
              blockKP np nr stk₁ : M (CallSig H) H ResP) ⟨s₁⟩) c₂ (.val v) := by
            cases b <;> exact h₂
          obtain ⟨s₂, f₂, o, hev₂, hend₂⟩ := blockArm_ansXP hL c₂ v (answered_right hA₁) h₂'
          exact ⟨_, .inr ⟨s₁, f₁, cv, stk₁, b, np, nr, s₂, f₂, o, hev, hb, har, hev₂, rfl⟩,
            hend₂⟩
    · have h₂' : Path (run' (pure ⟨(f₁, o)⟩ : M (CallSig H) H ResP) ⟨s₁⟩) c₂ (.val v) := by
        rcases o with fl | _
        · cases fl <;> first | exact absurd trivial hn | exact h₂
        · exact h₂
      obtain ⟨-, hv⟩ := path_pure_inv h₂'
      cases hv
      exact ⟨_, .inl ⟨hn, hev⟩, hend⟩
  · obtain ⟨⟨s₁, f₁, o⟩, hev, hend⟩ := hc s f stk cs₁ _ hA₁ h₁ (by simp)
    obtain rfl := endRP_err_inv hend
    cases hv
    exact ⟨_, .inl ⟨notNormal_flowP Flow.notNormal_trap, hev⟩, hend⟩

theorem if_ansXP {bt : BlockType} {c t el es : List BExpr} (hc : LAnsXP C c) (ht : LAnsXP C t)
    (hel : LAnsXP C el) (hes : LAnsXP C es)
    {s : Store H} {f : Frame} {stk : List Val} {cs : List (Call (CallSig H))}
    {ee : PathEnd (Except PUnit.{2} (ResP × St H))} (hA : Answered C cs)
    (h : Path (run' (denXP (.if_ bt c t el) f stk >>= thenKP (denListXP es)) ⟨s⟩) cs ee)
    (he : ee ≠ .div) : ∃ r, EvalOXP C s f stk (.if_ bt c t el :: es) r ∧ endRP r = ee := by
  rw [denXP_if] at h
  obtain ⟨r₀, hQ, hnorm, hnon⟩ := cont_ansXP (Q := IfHeadXP C s f stk bt c t el) hes hA h he
    (ifHead_ansXP hc ht hel)
  rcases hQ with ⟨hn, hev⟩ | ⟨s₁, f₁, cv, stk₁, b, np, nr, s₂, f₂, o, hev, hb, har, hev₂, rfl⟩
  · exact ⟨r₀, .ifAbort hev hn, (hnon hn).symm⟩
  · cases o with
    | flow fl =>
      cases fl with
      | normal vs =>
        obtain ⟨r, hk, hr⟩ := hnorm _ rfl
        exact ⟨r, .ifOk hev hb har hev₂ rfl hk, hr⟩
      | brk k vs =>
        cases k with
        | zero =>
          obtain ⟨r, hk, hr⟩ := hnorm _ rfl
          exact ⟨r, .ifOk hev hb har hev₂ rfl hk, hr⟩
        | succ k =>
          exact ⟨_, .ifBrk hev hb har hev₂, (hnon (notNormal_flowP Flow.notNormal_brk)).symm⟩
      | ret vs =>
        exact ⟨_, .ifEsc hev hb har hev₂ trivial,
          (hnon (notNormal_flowP Flow.notNormal_ret)).symm⟩
      | trap =>
        exact ⟨_, .ifEsc hev hb har hev₂ trivial,
          (hnon (notNormal_flowP Flow.notNormal_trap)).symm⟩
      | throw a =>
        exact ⟨_, .ifEsc hev hb har hev₂ trivial,
          (hnon (notNormal_flowP Flow.notNormal_throw)).symm⟩
    | tail => exact ⟨_, .ifEsc hev hb har hev₂ trivial, (hnon notNormal_tailP).symm⟩

end

section
variable {C : CallRel H}

/-- One loop iteration's path, inverted: the body runs to an `EvalOXP` outcome. -/
theorem loopIter_ansXP {bt : BlockType} {body : List BExpr} (hbody : LAnsXP C body)
    {p : ULift.{1} (Frame × List Val) × St H} {cs : List (Call (CallSig H))}
    {r' : PathEnd (Except PUnit.{2} ((ResP ⊕ ULift.{1} (Frame × List Val)) × St H))}
    (hA : Answered C cs) (h : Path (run' (loopBodyXP bt body p.1) p.2) cs r')
    (hr : r' ≠ .div) :
    ∃ np nr s₁ f₁ o, arity p.1.down.1 bt = some (np, nr) ∧
      EvalOXP C p.2.down p.1.down.1 (p.1.down.2.take np) body (s₁, f₁, o) ∧
      ((o = .flow .trap ∧ r' = .val (.error ⟨⟩)) ∨
       (o ≠ .flow .trap ∧ r' = .val (.ok (loopOutP np nr p.1.down.2 f₁ o, ⟨s₁⟩)))) := by
  obtain ⟨⟨f, stk⟩, ⟨s⟩⟩ := p
  simp only [loopBodyXP] at h
  cases har : arity f bt with
  | none => simp only [har] at h; exact absurd (path_stuck_inv h) hr
  | some q =>
    obtain ⟨np, nr⟩ := q
    simp only [har] at h
    rcases path_run_bind_inv h hr with ⟨c₁, c₂, a, t, rfl, h₁, h₂⟩ | ⟨h₁, hv⟩
    · obtain ⟨⟨s₁, f₁, o⟩, hev, hend⟩ := hbody s f (stk.take np) c₁ _ (answered_left hA) h₁
        (by simp)
      obtain ⟨hnt, rfl, rfl⟩ := endRP_ok_inv hend
      rw [loopKP_eq] at h₂
      obtain ⟨-, rfl⟩ := path_pure_inv h₂
      exact ⟨np, nr, s₁, f₁, o, rfl, hev, .inr ⟨hnt, rfl⟩⟩
    · obtain ⟨⟨s₁, f₁, o⟩, hev, hend⟩ := hbody s f (stk.take np) cs _ hA h₁ (by simp)
      obtain rfl := endRP_err_inv hend
      exact ⟨np, nr, s₁, f₁, .flow .trap, rfl, hev, .inl ⟨rfl, hv⟩⟩

/-- A loop with its continuation. -/
theorem loop_ansXP {bt : BlockType} {body es : List BExpr} (hbody : LAnsXP C body)
    (hes : LAnsXP C es) {s : Store H} {f : Frame} {stk : List Val}
    {cs : List (Call (CallSig H))} {ee : PathEnd (Except PUnit.{2} (ResP × St H))}
    (hA : Answered C cs)
    (h : Path (run' (denXP (.loop bt body) f stk >>= thenKP (denListXP es)) ⟨s⟩) cs ee)
    (he : ee ≠ .div) : ∃ r, EvalOXP C s f stk (.loop bt body :: es) r ∧ endRP r = ee := by
  let G := loopTree (loopBodyXP (H := H) bt body)
  let kk : Except PUnit.{2} (ResP × St H) →
      Tree (SigEv (CallSig H)) (Except PUnit.{2} (ResP × St H)) :=
    fun r => match r with
      | .ok (a, s') => run' (thenKP (denListXP es) a) s'
      | .error e => pure (.error e)
  have key : ∀ (p : ULift.{1} (Frame × List Val) × St H) cs₁
      (r : PathEnd (Except PUnit.{2} (ResP × St H))),
      IterPath G p cs₁ r → ∀ v, r = .val v → ∀ cs₂ ee, Answered C (cs₁ ++ cs₂) →
      Path (kk v) cs₂ ee → ee ≠ .div →
      ∃ r', EvalOXP C p.2.down p.1.down.1 p.1.down.2 (.loop bt body :: es) r' ∧
        endRP r' = ee := by
    intro p cs₁ r hit
    induction hit with
    | @exit p cs y hp =>
      intro v hv cs₂ ee hA h₂ he
      cases hv
      obtain ⟨r', hp', hm⟩ := path_map_inv hp
      rcases loopEnd_inl hm.symm with ⟨e, rfl, rfl⟩ | ⟨b, s', rfl, rfl⟩
      · obtain ⟨np, nr, s₁, f₁, o, har, hev, ⟨rfl, -⟩ | ⟨-, hr'⟩⟩ :=
          loopIter_ansXP hbody (answered_left hA) hp' (by simp)
        · obtain ⟨-, rfl⟩ := path_ret_inv rfl h₂
          exact ⟨_, .loopEsc har hev trivial, rfl⟩
        · cases hr'
      · obtain ⟨np, nr, s₁, f₁, o, har, hev, ⟨-, hr'⟩ | ⟨hnt, hr'⟩⟩ :=
          loopIter_ansXP hbody (answered_left hA) hp' (by simp)
        · cases hr'
        · simp only [PathEnd.val.injEq, Except.ok.injEq, Prod.mk.injEq] at hr'
          obtain ⟨hlo, rfl⟩ := hr'
          rcases loopOutP_inl hlo.symm with ⟨vs, rfl, rfl⟩ | ⟨k, vs, rfl, rfl⟩ | ⟨hesc, rfl⟩
          · obtain ⟨r, hk, hr⟩ := hes s₁ f₁ _ cs₂ ee (answered_right hA) h₂ he
            exact ⟨r, .loopOk har hev hk, hr⟩
          · have h₂' : Path (run' (pure ⟨(f₁, .flow (.brk k vs))⟩ : M (CallSig H) H ResP)
                ⟨s₁⟩) cs₂ ee := h₂
            obtain ⟨-, rfl⟩ := path_pure_inv h₂'
            exact ⟨_, .loopBrk har hev, rfl⟩
          · rw [show kk (.ok (⟨(f₁, o)⟩, ⟨s₁⟩)) =
                run' (pure ⟨(f₁, o)⟩ : M (CallSig H) H ResP) ⟨s₁⟩
              from congrArg (fun x => run' x ⟨s₁⟩)
                (thenKP_pass_eq (notNormal_of_escapesP hesc))] at h₂
            obtain ⟨-, rfl⟩ := path_pure_inv h₂
            exact ⟨_, .loopEsc har hev hesc, endRP_ok hnt⟩
    | div _ => intro v hv; cases hv
    | @step p cs₁ p' cs₂' r hp _ ih =>
      intro v hv cs₂ ee hA h₂ he
      obtain ⟨r', hp', hm⟩ := path_map_inv hp
      have hr'' := loopEnd_inr hm.symm
      obtain ⟨np, nr, s₁, f₁, o, har, hev, ⟨-, hr'⟩ | ⟨hnt, hr'⟩⟩ :=
        loopIter_ansXP hbody
          (answered_left (answered_left (by rw [List.append_assoc] at hA ⊢; exact hA)))
          hp' (by rw [hr'']; simp)
      · rw [hr''] at hr'; cases hr'
      · rw [hr''] at hr'
        simp only [PathEnd.val.injEq, Except.ok.injEq, Prod.mk.injEq] at hr'
        obtain ⟨hlo, hs⟩ := hr'
        obtain ⟨vs, rfl, hc⟩ := loopOutP_inr hlo.symm
        obtain ⟨r₁, hk, hr₁⟩ := ih v hv cs₂ ee
          (by rw [List.append_assoc] at hA; exact answered_right hA) h₂ he
        rw [hc, hs] at hk
        exact ⟨r₁, .loopBack har hev hk, hr₁⟩
    | spin _ _ _ => intro v hv; cases hv
  rw [denXP_loop, StoreBody.run_bind] at h
  rcases path_bind_inv h with ⟨cs₁, cs₂, v, rfl, h₁, h₂⟩ | ⟨rfl, -⟩
  · have h₁' := h₁
    change Path ((((Silmaril.Elgot.iter (loopBodyXP bt body) ⟨(f, stk)⟩ :
      M (CallSig H) H _).run ⟨s⟩).run)) cs₁ (.val v) at h₁'
    rw [Silmaril.Wasm.Abstract.BodyTrace.run_iter] at h₁'
    rcases v with e | ⟨a, s'⟩ <;> exact key _ _ _ (path_iter_iff.1 h₁') _ rfl cs₂ ee hA h₂ he
  · exact absurd rfl he

end

section
variable {C : CallRel H}

/-- The outcomes of a `try_table`'s head: the body's exit read as a block's, or a thrown
exception resolved by the clauses. -/
def TryHeadXP (C : CallRel H) (s : Store H) (f : Frame) (stk : List Val) (bt : BlockType)
    (cs : List Catch) (body : List BExpr) (r₀ : Store H × Frame × POut) : Prop :=
  ∃ np nr s₁ f₁ o, arity f bt = some (np, nr) ∧ EvalOXP C s f (stk.take np) body (s₁, f₁, o) ∧
    ((o.NotThrow ∧ r₀ = (s₁, f₁, blockFlowP np nr stk o)) ∨
     (∃ a us l, o = .flow (.throw a) ∧ Cfg.Region.Catches s₁ f₁ a cs (some (us, l)) ∧
        r₀ = (s₁, f₁, .flow (.brk l.toNat (us.reverse ++ stk.drop np)))) ∨
     (∃ a, o = .flow (.throw a) ∧ Cfg.Region.Catches s₁ f₁ a cs none ∧
        r₀ = (s₁, f₁, .flow (.throw a))))

theorem tryArm_ansXP {body : List BExpr} (hL : LAnsXP C body) {np nr : Nat} {stk : List Val}
    {cs : List Catch} {s : Store H} {f : Frame} (cl : List (Call (CallSig H)))
    (v : Except PUnit.{2} (ResP × St H)) (hA : Answered C cl)
    (h : Path (run' (denListXP body f (stk.take np) >>= tryKP np nr stk cs :
      M (CallSig H) H ResP) ⟨s⟩) cl (.val v)) :
    ∃ s₁ f₁ o r₀, EvalOXP C s f (stk.take np) body (s₁, f₁, o) ∧ endRP r₀ = .val v ∧
      ((o.NotThrow ∧ r₀ = (s₁, f₁, blockFlowP np nr stk o)) ∨
       (∃ a us l, o = .flow (.throw a) ∧ Cfg.Region.Catches s₁ f₁ a cs (some (us, l)) ∧
          r₀ = (s₁, f₁, .flow (.brk l.toNat (us.reverse ++ stk.drop np)))) ∨
       (∃ a, o = .flow (.throw a) ∧ Cfg.Region.Catches s₁ f₁ a cs none ∧
          r₀ = (s₁, f₁, .flow (.throw a)))) := by
  rcases path_run_bind_inv h (by simp) with ⟨c₁, c₂, a, t, rfl, h₁, h₂⟩ | ⟨h₁, hv⟩
  · obtain ⟨⟨s₁, f₁, o⟩, hev, hend⟩ := hL s f (stk.take np) c₁ _ (answered_left hA) h₁ (by simp)
    obtain ⟨hnt, rfl, rfl⟩ := endRP_ok_inv hend
    by_cases hth : ∃ a, o = .flow (.throw a)
    · obtain ⟨a, rfl⟩ := hth
      rw [run_tryKP_throw] at h₂
      cases hr : resolveCatch s₁ f₁ a cs with
      | none =>
        simp only [hr] at h₂
        exact absurd (path_stuck_inv h₂) (by simp)
      | some o =>
        have hc := resolveCatch_spec hr
        cases o with
        | some p =>
          obtain ⟨us, l⟩ := p
          simp only [hr] at h₂
          obtain ⟨-, hv⟩ := path_pure_inv h₂
          cases hv
          exact ⟨s₁, f₁, _, (s₁, f₁, .flow (.brk l.toNat (us.reverse ++ stk.drop np))), hev, rfl,
            .inr (.inl ⟨a, us, l, rfl, hc, rfl⟩)⟩
        | none =>
          simp only [hr] at h₂
          obtain ⟨-, hv⟩ := path_pure_inv h₂
          cases hv
          exact ⟨s₁, f₁, _, (s₁, f₁, .flow (.throw a)), hev, rfl, .inr (.inr ⟨a, rfl, hc, rfl⟩)⟩
    · have hnt' : o.NotThrow := by
        rcases o with fl | _
        · cases fl <;> first | trivial | exact hth ⟨_, rfl⟩
        · trivial
      rw [tryKP_ne hnt', blockKP_eq] at h₂
      obtain ⟨-, hv⟩ := path_pure_inv h₂
      cases hv
      exact ⟨s₁, f₁, o, (s₁, f₁, blockFlowP np nr stk o), hev,
        endRP_ok (fun h => hnt (blockFlowP_trap.1 h)), .inl ⟨hnt', rfl⟩⟩
  · obtain ⟨⟨s₁, f₁, o⟩, hev, hend⟩ := hL s f (stk.take np) cl _ hA h₁ (by simp)
    obtain rfl := endRP_err_inv hend
    cases hv
    exact ⟨s₁, f₁, .flow .trap, (s₁, f₁, .flow .trap), hev, rfl, .inl ⟨trivial, rfl⟩⟩

theorem try_ansXP {bt : BlockType} {cs : List Catch} {body es : List BExpr}
    (hbody : LAnsXP C body) (hes : LAnsXP C es)
    {s : Store H} {f : Frame} {stk : List Val} {cl : List (Call (CallSig H))}
    {ee : PathEnd (Except PUnit.{2} (ResP × St H))} (hA : Answered C cl)
    (h : Path (run' (denXP (.tryTable bt cs body) f stk >>= thenKP (denListXP es)) ⟨s⟩) cl ee)
    (he : ee ≠ .div) : ∃ r, EvalOXP C s f stk (.tryTable bt cs body :: es) r ∧ endRP r = ee := by
  rw [denXP_try] at h
  cases har : arity f bt with
  | none =>
    simp only [har] at h
    rcases path_run_bind_inv h he with ⟨_, _, _, _, _, h₁, _⟩ | ⟨h₁, _⟩
    · exact absurd (path_stuck_inv h₁) (by simp)
    · exact absurd (path_stuck_inv h₁) (by simp)
  | some p =>
    obtain ⟨np, nr⟩ := p
    simp only [har] at h
    obtain ⟨r₀, ⟨np', nr', s₁, f₁, o, har', hev, hcase⟩, hnorm, hnon⟩ :=
      cont_ansXP (Q := TryHeadXP C s f stk bt cs body) hes hA h he fun cs₁ v hA₁ h₁ => by
        obtain ⟨s₁, f₁, o, r₀, hev, hend, hcase⟩ := tryArm_ansXP hbody cs₁ v hA₁ h₁
        exact ⟨r₀, ⟨np, nr, s₁, f₁, o, har, hev, hcase⟩, hend⟩
    rw [har] at har'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj har')
    rcases hcase with ⟨hnt, rfl⟩ | ⟨a, us, l, rfl, hc, rfl⟩ | ⟨a, rfl, hc, rfl⟩
    · cases o with
      | flow fl =>
        cases fl with
        | normal vs =>
          obtain ⟨r, hk, hr⟩ := hnorm _ rfl
          exact ⟨r, .tryOk har hev rfl hk, hr⟩
        | brk k vs =>
          cases k with
          | zero =>
            obtain ⟨r, hk, hr⟩ := hnorm _ rfl
            exact ⟨r, .tryOk har hev rfl hk, hr⟩
          | succ k =>
            exact ⟨_, .tryBrk har hev, (hnon (notNormal_flowP Flow.notNormal_brk)).symm⟩
        | ret vs =>
          exact ⟨_, .tryEsc har hev trivial hnt,
            (hnon (notNormal_flowP Flow.notNormal_ret)).symm⟩
        | trap =>
          exact ⟨_, .tryEsc har hev trivial hnt,
            (hnon (notNormal_flowP Flow.notNormal_trap)).symm⟩
        | throw a => exact absurd hnt id
      | tail => exact ⟨_, .tryEsc har hev trivial hnt, (hnon notNormal_tailP).symm⟩
    · exact ⟨_, .tryCatch har hev hc, (hnon (notNormal_flowP Flow.notNormal_brk)).symm⟩
    · exact ⟨_, .tryRethrow har hev hc, (hnon (notNormal_flowP Flow.notNormal_throw)).symm⟩

end

section
variable {C : CallRel H}

mutual

theorem tree_ansXP : ∀ (e : BExpr) (es : List BExpr), LAnsXP C es →
    ∀ (s : Store H) (f : Frame) (stk : List Val) (cs : List (Call (CallSig H)))
      (ee : PathEnd (Except PUnit.{2} (ResP × St H))), Answered C cs →
    Path (run' (denXP e f stk >>= thenKP (denListXP es)) ⟨s⟩) cs ee → ee ≠ .div →
    ∃ r, EvalOXP C s f stk (e :: es) r ∧ endRP r = ee
  | .op _ args, _, hes, _, _, _, _, _, hA, h, he => op_ansXP (list_ansXP args) hes hA h he
  | .block _ body, _, hes, _, _, _, _, _, hA, h, he => block_ansXP (list_ansXP body) hes hA h he
  | .loop _ body, _, hes, _, _, _, _, _, hA, h, he => loop_ansXP (list_ansXP body) hes hA h he
  | .if_ _ c t el, _, hes, _, _, _, _, _, hA, h, he =>
    if_ansXP (list_ansXP c) (list_ansXP t) (list_ansXP el) hes hA h he
  | .tryTable _ _ body, _, hes, _, _, _, _, _, hA, h, he =>
    try_ansXP (list_ansXP body) hes hA h he

theorem list_ansXP : ∀ (es : List BExpr), LAnsXP C es
  | [] => fun s f stk cs e _ h _ => by
    obtain ⟨rfl, rfl⟩ := path_pure_inv h
    exact ⟨(s, f, .flow (.normal stk)), .nil, rfl⟩
  | e :: es => fun s f stk cs ee hA h he => by
    rw [denListXP_cons] at h
    exact tree_ansXP e es (list_ansXP es) s f stk cs ee hA h he

end
end

/-! ## Exactness -/

section
variable {C : CallRel H}

theorem evalOXP_iff {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {s' : Store H} {f' : Frame} {o : POut} (ho : o ≠ .flow .trap) :
    EvalOXP C s f stk es (s', f', o) ↔
      ∃ cs, Answered C cs ∧ Path (run' (denListXP es f stk : M (CallSig H) H ResP) ⟨s⟩) cs
        (.val (.ok (⟨(f', o)⟩, ⟨s'⟩))) := by
  have hend : endRP (s', f', o) = .val (.ok (⟨(f', o)⟩, ⟨s'⟩)) := endRP_ok ho
  constructor
  · intro h
    obtain ⟨cs, hA, hp⟩ := evalOXP_path h
    exact ⟨cs, hA, hend ▸ hp⟩
  · rintro ⟨cs, hA, hp⟩
    obtain ⟨⟨s₁, f₁, o₁⟩, hev, he⟩ := list_ansXP es s f stk cs _ hA hp (by simp)
    obtain ⟨-, h1, h2⟩ := endRP_ok_inv he
    simp only [ULift.up.injEq, Prod.mk.injEq] at h1 h2
    obtain ⟨rfl, rfl⟩ := h1
    subst h2
    exact hev

theorem evalOXP_trap_iff {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr} :
    (∃ s' f', EvalOXP C s f stk es (s', f', .flow .trap)) ↔
      ∃ cs, Answered C cs ∧ Path (run' (denListXP es f stk : M (CallSig H) H ResP) ⟨s⟩) cs
        (.val (.error ⟨⟩)) := by
  constructor
  · rintro ⟨s', f', h⟩
    exact evalOXP_path h
  · rintro ⟨cs, hA, hp⟩
    obtain ⟨⟨s₁, f₁, o₁⟩, hev, he⟩ := list_ansXP es s f stk cs _ hA hp (by simp)
    obtain rfl := endRP_err_inv he
    exact ⟨s₁, f₁, hev⟩

end

end Silmaril.Proofs.Wasm.Abstract.ExposeP
