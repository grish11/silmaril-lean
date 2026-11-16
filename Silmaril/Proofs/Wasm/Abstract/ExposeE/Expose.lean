module

public import Silmaril.Wasm.Abstract.ExposeE.Defs
public import Silmaril.Wasm.Cfg.Region.Thms
public import Silmaril.Proofs.Wasm.Abstract.CallX.Expose

/-!
Proofs for `Silmaril.Wasm.Abstract.ExposeE.Thms`: every `EvalOXE C` derivation is a path of
the exposed body `denListXE` with every call event answered by `C` (`evalOXE_path`), and on
exception-free code `denListXE` is `CallX`'s `denListX` (`denListXE_eq_denListX`).

The cases of `EvalOX` are `CallX`'s, read for `denListXE`; the exception cases resolve their
tag (`resolveThrow`) or handler (`resolveCatch`) as the derivation does.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.ExposeE

open Silmaril.Wasm Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract
  Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Abstract.BodyTrace Silmaril.Wasm.Binaryen
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
  Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXE Silmaril.Wasm.Abstract.ExposeE
  Silmaril.Elgot.ITree Silmaril.Proofs.Wasm.Abstract.StoreBody
  Silmaril.Proofs.Wasm.Abstract.StoreCall Silmaril.Proofs.Wasm.Abstract.CallX

variable {H : Type}

/-! ## Resolutions are functions -/

theorem throwResS_unique {s : Store H} {f : Frame} {x : TagIdx} {stk : List Val}
    {p₁ p₂ : Nat × Nat} (h₁ : ThrowResS s f x stk p₁) (h₂ : ThrowResS s f x stk p₂) :
    p₁ = p₂ := by
  obtain ⟨ti₁, ts₁, ht₁, he₁, hl₁, -⟩ := h₁
  obtain ⟨ti₂, ts₂, ht₂, he₂, hl₂, -⟩ := h₂
  rw [ht₁] at ht₂
  obtain ⟨h1, rfl⟩ := Prod.mk.inj (Option.some.inj ht₂)
  have hc := (Validation.Expand.iff.1 he₁).symm.trans (Validation.Expand.iff.1 he₂)
  have hts : ts₁ = ts₂ := by simpa using hc
  subst hts
  exact Prod.ext h1 (hl₁.symm.trans hl₂)

theorem resolveThrow_eq {s : Store H} {f : Frame} {x : TagIdx} {stk : List Val}
    {p : Nat × Nat} (h : ThrowResS s f x stk p) : resolveThrow s f x stk = some p := by
  have hex : ∃ p, ThrowResS s f x stk p := ⟨p, h⟩
  rw [resolveThrow, dite_eq_left_of_eq_true (eq_true hex)]
  exact congrArg some (throwResS_unique (Classical.choose_spec hex) h)

theorem resolveCatch_eq {s : Store H} {f : Frame} {a : Nat} {cs : List Catch}
    {r : Option (List Val × LabelIdx)} (h : Cfg.Region.Catches s f a cs r) :
    resolveCatch s f a cs = some r := by
  have hex : ∃ r, Cfg.Region.Catches s f a cs r := ⟨r, h⟩
  rw [resolveCatch, dite_eq_left_of_eq_true (eq_true hex)]
  exact congrArg some (Cfg.Region.catches_unique (Classical.choose_spec hex) h)

/-! ## Equations of the exposed body -/

theorem denListXE_cons (e : BExpr) (es : List BExpr) (f : Frame) (stk : List Val) :
    (denListXE (H := H) (e :: es) f stk) = denXE e f stk >>= thenK (denListXE es) := by
  rw [denListXE.eq_def]

theorem denXE_op (i : Instr) (args : List BExpr) (f : Frame) (stk : List Val) :
    (denXE (H := H) (.op i args) f stk) = denListXE args f stk >>= thenK (opCXE i) := by
  rw [denXE.eq_def]

theorem denXE_block (bt : BlockType) (body : List BExpr) (f : Frame) (stk : List Val) :
    (denXE (H := H) (.block bt body) f stk) =
      match arity f bt with
      | some (np, nr) => denListXE body f (stk.take np) >>= blockK np nr stk
      | none => stuck := by
  rw [denXE.eq_def]; rfl

theorem denXE_loop (bt : BlockType) (body : List BExpr) (f : Frame) (stk : List Val) :
    (denXE (H := H) (.loop bt body) f stk) =
      Silmaril.Elgot.iter (loopBodyXE bt body) ⟨(f, stk)⟩ := by
  rw [denXE.eq_def]; rfl

theorem denXE_if (bt : BlockType) (c t el : List BExpr) (f : Frame) (stk : List Val) :
    (denXE (H := H) (.if_ bt c t el) f stk) =
      denListXE c f stk >>= fun r =>
        match r with
        | ⟨(f₁, .normal (cv :: stk₁))⟩ =>
          match truthy cv, arity f₁ bt with
          | some b, some (np, nr) =>
            (if b then denListXE t f₁ (stk₁.take np) else denListXE el f₁ (stk₁.take np)) >>=
              blockK np nr stk₁
          | _, _ => stuck
        | ⟨(_, .normal [])⟩ => stuck
        | r => pure r := by
  rw [denXE.eq_def]; rfl

theorem denXE_try (bt : BlockType) (cs : List Catch) (body : List BExpr) (f : Frame)
    (stk : List Val) :
    (denXE (H := H) (.tryTable bt cs body) f stk) =
      match arity f bt with
      | some (np, nr) => denListXE body f (stk.take np) >>= tryK np nr stk cs
      | none => stuck := by
  rw [denXE.eq_def]; rfl

theorem denXE_loop_unfold (bt : BlockType) (body : List BExpr) (f : Frame) (stk : List Val) :
    (denXE (H := H) (.loop bt body) f stk) =
      (loopBodyXE bt body ⟨(f, stk)⟩ >>= Sum.elim pure
        fun c : ULift.{1} (Frame × List Val) => denXE (.loop bt body) c.down.1 c.down.2) := by
  rw [denXE_loop]
  exact (congrFun (Silmaril.Elgot.LawfulElgotMonad.fixpoint (m := M (CallSig H) H)
    (loopBodyXE bt body)) ⟨(f, stk)⟩).trans rfl

/-! ## Operators -/

theorem notEH_of_flat {s : Store H} {f : Frame} {stk : List Val} {i : Instr}
    {r : Store H × Frame × Flow} (h : evalFlat s f stk i = some r) : ehInstr i = false := by
  cases i <;> simp_all [ehInstr, evalFlat]

theorem opCXE_eq_opCX {i : Instr} (he : ehInstr i = false) : opCXE (H := H) i = opCX i := by
  funext f stk
  unfold opCXE
  split <;> simp_all [ehInstr]

theorem opCXE_flat {i : Instr} (hi : ∀ x, i ≠ .call x) (hx : isXCall i = false)
    (he : ehInstr i = false) : opCXE (H := H) i = flatK i := by
  rw [opCXE_eq_opCX he, opCX_flat hi hx]

theorem opCXE_tail {i : Instr} (h : isXTail i) : opCXE (H := H) i = tailEv i := by
  funext f stk
  cases i <;> first | exact absurd h id | rfl

/-! ## `try_table` exits -/

theorem tryK_ne {np nr : Nat} {stk : List Val} {cs : List Catch} {f : Frame} {fl : Flow}
    (h : ∀ a, fl ≠ .throw a) :
    (tryK (H := H) np nr stk cs ⟨(f, fl)⟩) = blockK np nr stk ⟨(f, fl)⟩ := by
  cases fl <;> first | rfl | exact absurd rfl (h _)

theorem path_tryK_ne {np nr : Nat} {stk : List Val} {cs : List Catch} {x : M (CallSig H) H Res}
    {s : St H} {cl : List (Call (CallSig H))} {s₁ : Store H} {f₁ : Frame} {fl : Flow}
    (h : Path (run' x s) cl (endR (s₁, f₁, fl))) (hnt : ∀ a, fl ≠ .throw a) :
    Path (run' (x >>= tryK np nr stk cs) s) cl (endR (s₁, f₁, blockFlow np nr stk fl)) := by
  cases fl with
  | trap => exact path_bind_err h
  | throw a => exact absurd rfl (hnt a)
  | brk k vs => cases k <;> exact path_bind_pure h rfl
  | _ => exact path_bind_pure h rfl

theorem run_tryK_throw {np nr : Nat} {stk : List Val} {cs : List Catch} {f₁ : Frame} {a : Nat}
    (s₁ : Store H) :
    run' (tryK np nr stk cs ⟨(f₁, .throw a)⟩ : M (CallSig H) H Res) ⟨s₁⟩ =
      run' (match resolveCatch s₁ f₁ a cs with
        | some (some (us, l)) => pure ⟨(f₁, .brk l.toNat (us.reverse ++ stk.drop np))⟩
        | some none => pure ⟨(f₁, .throw a)⟩
        | none => stuck : M (CallSig H) H Res) ⟨s₁⟩ :=
  run_getState_bind _ _

theorem path_tryK_catch {np nr : Nat} {stk : List Val} {cs : List Catch}
    {x : M (CallSig H) H Res} {s : St H} {cl : List (Call (CallSig H))} {s₁ : Store H}
    {f₁ : Frame} {a : Nat} {us : List Val} {l : LabelIdx}
    (h : Path (run' x s) cl (endR (s₁, f₁, .throw a)))
    (hc : Cfg.Region.Catches s₁ f₁ a cs (some (us, l))) :
    Path (run' (x >>= tryK np nr stk cs) s) cl
      (endR (s₁, f₁, .brk l.toNat (us.reverse ++ stk.drop np))) := by
  have h₂ : Path (run' (tryK np nr stk cs ⟨(f₁, .throw a)⟩ : M (CallSig H) H Res) ⟨s₁⟩) []
      (endR (s₁, f₁, .brk l.toNat (us.reverse ++ stk.drop np))) := by
    rw [run_tryK_throw, resolveCatch_eq hc]
    exact .ret rfl
  have := path_bind_ok h h₂
  rwa [List.append_nil] at this

theorem path_tryK_rethrow {np nr : Nat} {stk : List Val} {cs : List Catch}
    {x : M (CallSig H) H Res} {s : St H} {cl : List (Call (CallSig H))} {s₁ : Store H}
    {f₁ : Frame} {a : Nat}
    (h : Path (run' x s) cl (endR (s₁, f₁, .throw a)))
    (hc : Cfg.Region.Catches s₁ f₁ a cs none) :
    Path (run' (x >>= tryK np nr stk cs) s) cl (endR (s₁, f₁, .throw a)) := by
  have h₂ : Path (run' (tryK np nr stk cs ⟨(f₁, .throw a)⟩ : M (CallSig H) H Res) ⟨s₁⟩) []
      (endR (s₁, f₁, .throw a)) := by
    rw [run_tryK_throw, resolveCatch_eq hc]
    exact .ret rfl
  have := path_bind_ok h h₂
  rwa [List.append_nil] at this

/-- **Every `EvalOXE C` derivation is a path of the exposed abstract body**, with
every call event answered as `C` allows, ending as the derivation does. -/
theorem evalOXE_path {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × Flow} (h : EvalOXE C s f stk es r) :
    ∃ cs, Answered C cs ∧ Path (run' (denListXE es f stk : M (CallSig H) H Res) ⟨s⟩) cs (endR r) := by
  induction h with
  | nil => exact ⟨[], answered_nil, .ret rfl⟩
  | argsAbort _ hfl ih =>
    obtain ⟨cs, hA, hp⟩ := ih
    refine ⟨cs, hA, ?_⟩
    rw [denListXE_cons, denXE_op]
    exact path_thenK_pass (path_thenK_pass hp hfl) hfl
  | @callOk s s₁ s₂ f f₁ stk stk₁ vs x args es a fi ps rs fl r _ hfi hty hcall hvs _ ih₁ ih₂ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    refine ⟨cs₁ ++ [⟨(a, (stk₁.take ps.length).reverse, s₁), (s₂, fl)⟩] ++ cs₂,
      answered_append (answered_append hA₁ (answered_single hcall)) hA₂, ?_⟩
    rw [denListXE_cons, denXE_op]
    exact path_thenK_normal (path_thenK_normal hp₁
      (path_callEv hfi hty (s₂, fl) (path_callAns_vals hvs _))) hp₂
  | @callTrap s s₁ s₂ f f₁ stk stk₁ x args es a fi ps rs _ hfi hty hcall ih₁ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    refine ⟨cs₁ ++ [⟨(a, (stk₁.take ps.length).reverse, s₁), (s₂, .trap)⟩],
      answered_append hA₁ (answered_single hcall), ?_⟩
    rw [denListXE_cons, denXE_op]
    have := path_thenK_normal hp₁ (path_callEv hfi hty (s₂, .trap) (path_callAns_trap _))
    exact path_thenK_pass this Flow.notNormal_trap
  | @callThrow s s₁ s₂ f f₁ stk stk₁ x args es a fi ps rs t _ hfi hty hcall ih₁ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    refine ⟨cs₁ ++ [⟨(a, (stk₁.take ps.length).reverse, s₁), (s₂, .throw t)⟩],
      answered_append hA₁ (answered_single hcall), ?_⟩
    rw [denListXE_cons, denXE_op]
    have := path_thenK_normal hp₁ (path_callEv hfi hty (s₂, .throw t) (path_callAns_throw _))
    exact path_thenK_pass this Flow.notNormal_throw
  | @opOk s s₁ s₂ f f₁ f₂ stk stk₁ stk₂ i args es r hi _ hflat _ ih₁ ih₂ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    refine ⟨cs₁ ++ [] ++ cs₂, answered_append (answered_append hA₁ answered_nil) hA₂, ?_⟩
    rw [denListXE_cons, denXE_op]
    have hop : opCXE i f₁ stk₁ = (flatK i f₁ stk₁ : M (CallSig H) H Res) :=
      congrFun (congrFun (opCXE_flat hi (notX_of_flat hflat) (notEH_of_flat hflat)) f₁) stk₁
    exact path_thenK_normal (path_thenK_normal hp₁ (hop ▸ path_flatK hflat)) hp₂
  | @opStop s s₁ s₂ f f₁ f₂ stk stk₁ i args es fl hi _ hflat hfl ih₁ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    refine ⟨cs₁ ++ [], answered_append hA₁ answered_nil, ?_⟩
    rw [denListXE_cons, denXE_op]
    have hop : opCXE i f₁ stk₁ = (flatK i f₁ stk₁ : M (CallSig H) H Res) :=
      congrFun (congrFun (opCXE_flat hi (notX_of_flat hflat) (notEH_of_flat hflat)) f₁) stk₁
    exact path_thenK_pass (path_thenK_normal hp₁ (hop ▸ path_flatK hflat)) hfl
  | @blockOk s s₁ f f₁ stk vs bt body es np nr fl r har _ hvs _ ih₁ ih₂ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    refine ⟨cs₁ ++ cs₂, answered_append hA₁ hA₂, ?_⟩
    rw [denListXE_cons, denXE_block]
    simp only [har]
    have hb := path_blockK (np := np) (nr := nr) (stk := stk) hp₁
    rw [blockFlow_of_vals hvs] at hb
    exact path_thenK_normal hb hp₂
  | @blockBrk s s₁ f f₁ stk vs bt body es np nr k har _ ih =>
    obtain ⟨cs, hA, hp⟩ := ih
    refine ⟨cs, hA, ?_⟩
    rw [denListXE_cons, denXE_block]
    simp only [har]
    exact path_thenK_pass (path_blockK (np := np) (nr := nr) (stk := stk) hp) Flow.notNormal_brk
  | @blockEsc s s₁ f f₁ stk bt body es np nr fl har _ hfl ih =>
    obtain ⟨cs, hA, hp⟩ := ih
    refine ⟨cs, hA, ?_⟩
    rw [denListXE_cons, denXE_block]
    simp only [har]
    have hb := path_blockK (np := np) (nr := nr) (stk := stk) hp
    rw [blockFlow_esc hfl] at hb
    exact path_thenK_pass hb (Flow.not_normal_of_escapes hfl)
  | @loopOk s s₁ f f₁ stk vs bt body es np nr r har _ _ ih₁ ih₂ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    refine ⟨cs₁ ++ cs₂, answered_append hA₁ hA₂, ?_⟩
    rw [denListXE_cons, denXE_loop_unfold]
    have h1 : Path (run' (loopBodyXE bt body ⟨(f, stk)⟩) ⟨s⟩) cs₁
        (.val (.ok (.inl ⟨(f₁, .normal (vs.take nr ++ stk.drop np))⟩, ⟨s₁⟩))) := by
      simp only [loopBodyXE, har]; exact path_bind_pure hp₁ rfl
    exact path_thenK_normal (path_bind_pure h1 rfl) hp₂
  | @loopBack s s₁ f f₁ stk vs bt body es np nr r har _ _ ih₁ ih₂ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    refine ⟨cs₁ ++ cs₂, answered_append hA₁ hA₂, ?_⟩
    rw [denListXE_cons, denXE_loop_unfold, bind_assoc]
    have h1 : Path (run' (loopBodyXE bt body ⟨(f, stk)⟩) ⟨s⟩) cs₁
        (.val (.ok (.inr ⟨(f₁, vs.take np ++ stk.drop np)⟩, ⟨s₁⟩))) := by
      simp only [loopBodyXE, har]; exact path_bind_pure hp₁ rfl
    rw [denListXE_cons] at hp₂
    exact path_bind_ok h1 hp₂
  | @loopBrk s s₁ f f₁ stk vs bt body es np nr k har _ ih =>
    obtain ⟨cs, hA, hp⟩ := ih
    refine ⟨cs, hA, ?_⟩
    rw [denListXE_cons, denXE_loop_unfold]
    have h1 : Path (run' (loopBodyXE bt body ⟨(f, stk)⟩) ⟨s⟩) cs
        (.val (.ok (.inl ⟨(f₁, .brk k vs)⟩, ⟨s₁⟩))) := by
      simp only [loopBodyXE, har]; exact path_bind_pure hp rfl
    exact path_thenK_pass (path_bind_pure h1 rfl) Flow.notNormal_brk
  | @loopEsc s s₁ f f₁ stk bt body es np nr fl har _ hfl ih =>
    obtain ⟨cs, hA, hp⟩ := ih
    refine ⟨cs, hA, ?_⟩
    rw [denListXE_cons, denXE_loop_unfold]
    refine path_thenK_pass ?_ (Flow.not_normal_of_escapes hfl)
    cases fl
    case trap =>
      refine path_bind_err ?_
      simp only [loopBodyXE, har]; exact path_bind_err hp
    all_goals first
      | exact absurd hfl id
      | (refine path_bind_pure (a := .inl ⟨(f₁, _)⟩) ?_ rfl
         simp only [loopBodyXE, har]; exact path_bind_pure hp rfl)
  | @ifOk s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c t el es np nr fl r _ hb har _ hvs _ ih₁ ih₂ ih₃ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    obtain ⟨cs₃, hA₃, hp₃⟩ := ih₃
    refine ⟨cs₁ ++ (cs₂ ++ cs₃), answered_append hA₁ (answered_append hA₂ hA₃), ?_⟩
    rw [denListXE_cons, denXE_if, bind_assoc]
    refine path_bind_ok hp₁ ?_
    simp only [hb, har]
    have harm : Path (run' ((if b then denListXE t f₁ (stk₁.take np) else
        denListXE el f₁ (stk₁.take np)) : M (CallSig H) H Res) ⟨s₁⟩) cs₂ (endR (s₂, f₂, fl)) := by
      cases b <;> exact hp₂
    have hbk := path_blockK (np := np) (nr := nr) (stk := stk₁) harm
    rw [blockFlow_of_vals hvs] at hbk
    exact path_thenK_normal hbk hp₃
  | @ifBrk s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c t el es np nr k _ hb har _ ih₁ ih₂ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    refine ⟨cs₁ ++ cs₂, answered_append hA₁ hA₂, ?_⟩
    rw [denListXE_cons, denXE_if, bind_assoc]
    refine path_bind_ok hp₁ ?_
    simp only [hb, har]
    have harm : Path (run' ((if b then denListXE t f₁ (stk₁.take np) else
        denListXE el f₁ (stk₁.take np)) : M (CallSig H) H Res) ⟨s₁⟩) cs₂
        (endR (s₂, f₂, .brk (k + 1) vs)) := by
      cases b <;> exact hp₂
    exact path_thenK_pass (path_blockK (np := np) (nr := nr) (stk := stk₁) harm) Flow.notNormal_brk
  | @ifEsc s s₁ s₂ f f₁ f₂ stk stk₁ cv b bt c t el es np nr fl _ hb har _ hfl ih₁ ih₂ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    refine ⟨cs₁ ++ cs₂, answered_append hA₁ hA₂, ?_⟩
    rw [denListXE_cons, denXE_if, bind_assoc]
    refine path_bind_ok hp₁ ?_
    simp only [hb, har]
    have harm : Path (run' ((if b then denListXE t f₁ (stk₁.take np) else
        denListXE el f₁ (stk₁.take np)) : M (CallSig H) H Res) ⟨s₁⟩) cs₂ (endR (s₂, f₂, fl)) := by
      cases b <;> exact hp₂
    have hbk := path_blockK (np := np) (nr := nr) (stk := stk₁) harm
    rw [blockFlow_esc hfl] at hbk
    exact path_thenK_pass hbk (Flow.not_normal_of_escapes hfl)
  | @callIndOk s s₁ s₂ f f₁ stk stk₁ vs x y args es ad i fa fi ps rs fl r _ hres hfi hty hcall hvs _ ih₁ ih₂ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    refine ⟨cs₁ ++ [⟨(fa, (stk₁.take ps.length).reverse, s₁), (s₂, fl)⟩] ++ cs₂,
      answered_append (answered_append hA₁ (answered_single hcall)) hA₂, ?_⟩
    rw [denListXE_cons, denXE_op]
    refine path_thenK_normal (path_thenK_normal hp₁ ?_) hp₂
    show Path (run' (indEv x y f₁ _) ⟨s₁⟩) _ _
    rw [indEv, run_getState_bind]
    simp only [resolveInd_eq (p := (some fa, stk₁)) ⟨ad, i, rfl, hres⟩]
    exact path_callAt hfi hty (s₂, fl) (path_callAns_vals hvs _)
  | @callIndRes s s₁ f f₁ stk stk₁ x y args es ad i _ hres ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih
    refine ⟨cs₁ ++ [], answered_append hA₁ answered_nil, ?_⟩
    rw [denListXE_cons, denXE_op]
    refine path_thenK_pass (path_thenK_normal hp₁ ?_) Flow.notNormal_trap
    show Path (run' (indEv x y f₁ _) ⟨s₁⟩) _ _
    rw [indEv, run_getState_bind]
    simp only [resolveInd_eq (p := (none, stk₁)) ⟨ad, i, rfl, hres⟩]
    exact .ret (run_trapS _)
  | @callIndStop s s₁ s₂ f f₁ stk stk₁ x y args es ad i fa fi ps rs fl _ hres hfi hty hcall hfl ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih
    refine ⟨cs₁ ++ [⟨(fa, (stk₁.take ps.length).reverse, s₁), (s₂, fl)⟩],
      answered_append hA₁ (answered_single hcall), ?_⟩
    rw [denListXE_cons, denXE_op]
    have hab : ¬ fl.IsNormal := by cases fl <;> simp_all [Flow.Abrupt, Flow.IsNormal]
    refine path_thenK_pass (path_thenK_normal hp₁ ?_) hab
    show Path (run' (indEv x y f₁ _) ⟨s₁⟩) _ _
    rw [indEv, run_getState_bind]
    simp only [resolveInd_eq (p := (some fa, stk₁)) ⟨ad, i, rfl, hres⟩]
    refine path_callAt hfi hty (s₂, fl) ?_
    cases fl with
    | trap => exact path_callAns_trap _
    | throw t => exact path_callAns_throw _
    | _ => exact absurd hfl id
  | @callRefOk s s₁ s₂ f f₁ stk stk₁ vs y args es fa fi ps rs fl r _ hfi hty hcall hvs _ ih₁ ih₂ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    refine ⟨cs₁ ++ [⟨(fa, (stk₁.take ps.length).reverse, s₁), (s₂, fl)⟩] ++ cs₂,
      answered_append (answered_append hA₁ (answered_single hcall)) hA₂, ?_⟩
    rw [denListXE_cons, denXE_op]
    exact path_thenK_normal (path_thenK_normal hp₁
      (path_callAt hfi hty (s₂, fl) (path_callAns_vals hvs _))) hp₂
  | @callRefNull s s₁ f f₁ stk stk₁ y args es _ ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih
    refine ⟨cs₁ ++ [], answered_append hA₁ answered_nil, ?_⟩
    rw [denListXE_cons, denXE_op]
    exact path_thenK_pass (path_thenK_normal hp₁ (.ret (run_trapS _))) Flow.notNormal_trap
  | @callRefStop s s₁ s₂ f f₁ stk stk₁ y args es fa fi ps rs fl _ hfi hty hcall hfl ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih
    refine ⟨cs₁ ++ [⟨(fa, (stk₁.take ps.length).reverse, s₁), (s₂, fl)⟩],
      answered_append hA₁ (answered_single hcall), ?_⟩
    rw [denListXE_cons, denXE_op]
    have hab : ¬ fl.IsNormal := by cases fl <;> simp_all [Flow.Abrupt, Flow.IsNormal]
    refine path_thenK_pass (path_thenK_normal hp₁ (path_callAt hfi hty (s₂, fl) ?_)) hab
    cases fl with
    | trap => exact path_callAns_trap _
    | throw t => exact path_callAns_throw _
    | _ => exact absurd hfl id
  | @tail s s₁ s₂ f f₁ stk stk₁ i args es fa fi ps rs fl _ hres hfi hty hcall hfl ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih
    refine ⟨cs₁ ++ [⟨(fa, ((stk₁.drop (tailPop i)).take ps.length).reverse, s₁), (s₂, fl)⟩],
      answered_append hA₁ (answered_single hcall), ?_⟩
    rw [denListXE_cons, denXE_op]
    have hab : ¬ (tailFlow rs.length fl).IsNormal := by
      rcases hfl with ⟨vs, hvs⟩ | hfl
      · cases fl with
        | brk k vs' => cases k <;> simp_all [tailFlow, Flow.IsNormal, Flow.retVals]
        | _ => simp_all [tailFlow, Flow.IsNormal, Flow.retVals]
      · cases fl <;> simp_all [Flow.Abrupt, tailFlow, Flow.IsNormal]
    refine path_thenK_pass (path_thenK_normal hp₁ ?_) hab
    rw [opCXE_tail (isXTail_of_tailRes hres)]
    show Path (run' (tailEv i f₁ _) ⟨s₁⟩) _ _
    rw [tailEv, run_getState_bind]
    simp only [resolveTail_eq hres]
    exact path_tailAt hfi hty (s₂, fl) (path_tailAns hfl _)
  | @tailRes s s₁ f f₁ stk stk₁ i args es _ hres ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih
    refine ⟨cs₁ ++ [], answered_append hA₁ answered_nil, ?_⟩
    rw [denListXE_cons, denXE_op]
    refine path_thenK_pass (path_thenK_normal hp₁ ?_) Flow.notNormal_trap
    rw [opCXE_tail (isXTail_of_tailRes hres)]
    show Path (run' (tailEv i f₁ _) ⟨s₁⟩) _ _
    rw [tailEv, run_getState_bind]
    simp only [resolveTail_eq hres]
    exact .ret (run_trapS _)
  | @ifAbort s s₁ f f₁ stk bt c t el es fl _ hfl ih =>
    obtain ⟨cs, hA, hp⟩ := ih
    refine ⟨cs, hA, ?_⟩
    rw [denListXE_cons, denXE_if]
    refine path_thenK_pass ?_ hfl
    cases fl
    case normal => exact absurd trivial hfl
    case trap => exact path_bind_err hp
    all_goals exact path_bind_pure hp rfl
  | @throw s s₁ f f₁ stk stk₁ x args es ta ti ts _ ht he hn ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih
    refine ⟨cs₁ ++ [], answered_append hA₁ answered_nil, ?_⟩
    rw [denListXE_cons, denXE_op]
    refine path_thenK_pass (path_thenK_normal hp₁ ?_) Flow.notNormal_throw
    show Path (run' (throwEv x f₁ _) ⟨s₁⟩) _ _
    rw [throwEv, run_getState_bind]
    simp only [resolveThrow_eq (p := (ta, ts.length)) ⟨ti, ts, ht, he, rfl, hn⟩]
    exact .ret (run_set_pure _ _ _)
  | @throwRefNull s s₁ f f₁ stk stk₁ args es _ ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih
    refine ⟨cs₁ ++ [], answered_append hA₁ answered_nil, ?_⟩
    rw [denListXE_cons, denXE_op]
    exact path_thenK_pass (path_thenK_normal hp₁ (.ret (run_trapS _))) Flow.notNormal_trap
  | @throwRefExn s s₁ f f₁ stk stk₁ a args es _ ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih
    refine ⟨cs₁ ++ [], answered_append hA₁ answered_nil, ?_⟩
    rw [denListXE_cons, denXE_op]
    exact path_thenK_pass (path_thenK_normal hp₁ (.ret rfl)) Flow.notNormal_throw
  | @tryOk s s₁ f f₁ stk vs bt cs body es np nr fl r har _ hvs _ ih₁ ih₂ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    refine ⟨cs₁ ++ cs₂, answered_append hA₁ hA₂, ?_⟩
    rw [denListXE_cons, denXE_try]
    simp only [har]
    have hnt : ∀ a, fl ≠ .throw a := by rintro a rfl; simp [Flow.blockVals] at hvs
    have hb := path_tryK_ne (np := np) (nr := nr) (stk := stk) (cs := cs) hp₁ hnt
    rw [blockFlow_of_vals hvs] at hb
    exact path_thenK_normal hb hp₂
  | @tryBrk s s₁ f f₁ stk vs bt cs body es np nr k har _ ih =>
    obtain ⟨cl, hA, hp⟩ := ih
    refine ⟨cl, hA, ?_⟩
    rw [denListXE_cons, denXE_try]
    simp only [har]
    exact path_thenK_pass (path_tryK_ne (np := np) (nr := nr) (stk := stk) (cs := cs) hp
      (fun _ h => Flow.noConfusion h)) Flow.notNormal_brk
  | @tryEsc s s₁ f f₁ stk bt cs body es np nr fl har _ hfl hnt ih =>
    obtain ⟨cl, hA, hp⟩ := ih
    refine ⟨cl, hA, ?_⟩
    rw [denListXE_cons, denXE_try]
    simp only [har]
    have hb := path_tryK_ne (np := np) (nr := nr) (stk := stk) (cs := cs) hp hnt
    rw [blockFlow_esc hfl] at hb
    exact path_thenK_pass hb (Flow.not_normal_of_escapes hfl)
  | @tryCatch s s₁ f f₁ stk us bt cs body es np nr a l har _ hc ih =>
    obtain ⟨cl, hA, hp⟩ := ih
    refine ⟨cl, hA, ?_⟩
    rw [denListXE_cons, denXE_try]
    simp only [har]
    exact path_thenK_pass (path_tryK_catch hp hc) Flow.notNormal_brk
  | @tryRethrow s s₁ f f₁ stk bt cs body es np nr a har _ hc ih =>
    obtain ⟨cl, hA, hp⟩ := ih
    refine ⟨cl, hA, ?_⟩
    rw [denListXE_cons, denXE_try]
    simp only [har]
    exact path_thenK_pass (path_tryK_rethrow hp hc) Flow.notNormal_throw

/-! ## On exception-free code the exposed body is `CallX`'s -/

mutual

theorem denXE_eq_denX : ∀ (e : BExpr), ehFree e = true →
    (denXE (H := H) e : Frame → List Val → M (CallSig H) H Res) = denX e
  | .op i args, h => by
    simp only [ehFree, Bool.and_eq_true, Bool.not_eq_true'] at h
    funext f stk
    rw [denXE_op, denX_op, denListXE_eq_denListX args h.2, opCXE_eq_opCX h.1]
  | .block bt body, h => by
    simp only [ehFree] at h
    funext f stk
    rw [denXE_block, denX_block, denListXE_eq_denListX body h]
    cases arity f bt <;> rfl
  | .loop bt body, h => by
    simp only [ehFree] at h
    funext f stk
    rw [denXE_loop, denX_loop]
    congr 1
    funext c
    simp only [loopBodyXE, loopBodyX, denListXE_eq_denListX body h]
    cases arity c.down.1 bt <;> rfl
  | .if_ bt c t el, h => by
    simp only [ehFree, Bool.and_eq_true] at h
    funext f stk
    rw [denXE_if, denX_if, denListXE_eq_denListX c h.1.1, denListXE_eq_denListX t h.1.2,
      denListXE_eq_denListX el h.2]
    congr 1
  | .tryTable bt cs body, h => by simp [ehFree] at h

theorem denListXE_eq_denListX : ∀ (es : List BExpr), ehFreeL es = true →
    (denListXE (H := H) es : Frame → List Val → M (CallSig H) H Res) = denListX es
  | [], _ => by funext f stk; rw [denListXE.eq_def, denListX.eq_def]
  | e :: es, h => by
    simp only [ehFreeL, Bool.and_eq_true] at h
    funext f stk
    rw [denListXE_cons, denListX_cons, denXE_eq_denX e h.1, denListXE_eq_denListX es h.2]

end

end Silmaril.Proofs.Wasm.Abstract.ExposeE
