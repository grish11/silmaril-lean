module

public import Silmaril.Proofs.Wasm.Abstract.ExposeP.Expose

/-!
Proofs for `Silmaril.Wasm.Abstract.ExposeP.Thms`: on code without the extended call forms
(`CallX.xFreeL`) the exposed body with pending tail calls is `ExposeE`'s, read with body results
(`denListXP_eq_liftP`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.ExposeP

open Silmaril.Wasm Silmaril.Games Silmaril.Wasm.Abstract
  Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Binaryen
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
  Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXP Silmaril.Wasm.Abstract.ExposeE
  Silmaril.Wasm.Abstract.ExposeP
  Silmaril.Elgot.ITree Silmaril.Proofs.Wasm.Abstract.StoreBody
  Silmaril.Proofs.Wasm.Abstract.StoreCall Silmaril.Proofs.Wasm.Abstract.CallX
  Silmaril.Proofs.Wasm.Abstract.ExposeE

variable {H : Type}

theorem stuck_bind {X Y : Type 1} (g : X → M (CallSig H) H Y) :
    (stuck >>= g : M (CallSig H) H Y) = stuck := by
  funext s
  show run' (stuck >>= g) s = run' stuck s
  rw [StoreBody.run_bind]
  exact diverge_bind _

/-- `liftP` through a bind whose continuation is read pointwise. -/
theorem liftP_bind {x : M (CallSig H) H Res} {k : Res → M (CallSig H) H Res}
    {k' : ResP → M (CallSig H) H ResP} (h : ∀ r, liftP (k r) = k' (ofRes r)) :
    liftP (x >>= k) = liftP x >>= k' := by
  unfold liftP
  rw [bind_assoc, bind_assoc]
  congr 1
  funext r
  rw [pure_bind]
  exact h r

theorem liftP_pure (r : Res) : liftP (pure r : M (CallSig H) H Res) = pure (ofRes r) := by
  unfold liftP; rw [pure_bind]

theorem liftP_stuck : liftP (stuck : M (CallSig H) H Res) = stuck := stuck_bind _

theorem liftP_thenK {k : Frame → List Val → M (CallSig H) H Res} (r : Res) :
    liftP (thenK k r) = thenKP (fun f stk => liftP (k f stk)) (ofRes r) := by
  obtain ⟨f, fl⟩ := r
  cases fl <;> first | rfl | exact liftP_pure _

theorem liftP_blockK {np nr : Nat} {stk : List Val} (r : Res) :
    liftP (blockK np nr stk r : M (CallSig H) H Res) = blockKP np nr stk (ofRes r) := by
  obtain ⟨f, fl⟩ := r
  cases fl with
  | brk k vs => cases k <;> exact liftP_pure _
  | _ => exact liftP_pure _

theorem liftP_tryK {np nr : Nat} {stk : List Val} {cs : List Catch} (r : Res) :
    liftP (tryK np nr stk cs r : M (CallSig H) H Res) = tryKP np nr stk cs (ofRes r) := by
  obtain ⟨f, fl⟩ := r
  cases fl with
  | throw a =>
    show liftP (getState >>= _) = getState >>= _
    unfold liftP
    rw [bind_assoc]
    congr 1
    funext s
    cases resolveCatch s.down f a cs with
    | none => exact stuck_bind _
    | some o =>
      cases o with
      | none => exact pure_bind _ _
      | some p => exact pure_bind _ _
  | brk k vs => cases k <;> exact liftP_pure _
  | _ => exact liftP_pure _

theorem liftP_loopK {np nr : Nat} {stk : List Val} (r : Res) :
    ((loopK np nr stk r : M (CallSig H) H _) >>= Sum.elim
        (fun b => (pure ∘ Sum.inl) (ofRes b)) (pure ∘ Sum.inr)) =
      loopKP np nr stk (ofRes r) := by
  obtain ⟨f, fl⟩ := r
  cases fl with
  | brk k vs => cases k <;> simp [loopK, loopKP, ofRes]
  | _ => simp [loopK, loopKP, ofRes]

mutual

theorem denXP_eq_liftP : ∀ (e : BExpr), xFree e = true →
    (denXP (H := H) e : Frame → List Val → M (CallSig H) H ResP) =
      fun f stk => liftP (denXE e f stk)
  | .op i args, h => by
    simp only [xFree, Bool.and_eq_true, Bool.not_eq_true'] at h
    funext f stk
    rw [denXP_op, denXE_op, denListXP_eq_liftP args h.2]
    beta_reduce
    refine (liftP_bind fun r => ?_).symm
    rw [liftP_thenK]
    congr 1
    funext f' stk'
    exact (opCXP_notX h.1 f' stk').symm
  | .block bt body, h => by
    simp only [xFree] at h
    funext f stk
    rw [denXP_block, denXE_block, denListXP_eq_liftP body h]
    beta_reduce
    cases arity f bt with
    | none => exact liftP_stuck.symm
    | some p => exact (liftP_bind liftP_blockK).symm
  | .loop bt body, h => by
    simp only [xFree] at h
    funext f stk
    rw [denXP_loop, denXE_loop]
    have hnat := Silmaril.Elgot.LawfulElgotMonad.naturality (m := M (CallSig H) H)
      (loopBodyXE bt body) (fun r => pure (ofRes r))
    have h1 : liftP (Silmaril.Elgot.iter (loopBodyXE bt body) ⟨(f, stk)⟩) =
        Silmaril.Elgot.iter (Silmaril.Elgot.mapReturn (loopBodyXE bt body)
          (fun r => pure (ofRes r))) ⟨(f, stk)⟩ :=
      congrFun hnat ⟨(f, stk)⟩
    rw [h1]
    congr 1
    funext c
    unfold Silmaril.Elgot.mapReturn loopBodyXE loopBodyXP
    rw [denListXP_eq_liftP body h]
    cases arity c.down.1 bt with
    | none => exact (stuck_bind _).symm
    | some p =>
      obtain ⟨np, nr⟩ := p
      simp only [liftP, bind_assoc, pure_bind]
      congr 1
      funext r
      exact (liftP_loopK r).symm
  | .if_ bt c t el, h => by
    simp only [xFree, Bool.and_eq_true] at h
    funext f stk
    rw [denXP_if, denXE_if, denListXP_eq_liftP c h.1.1, denListXP_eq_liftP t h.1.2,
      denListXP_eq_liftP el h.2]
    beta_reduce
    refine (liftP_bind fun r => ?_).symm
    obtain ⟨f₁, fl⟩ := r
    cases fl with
    | normal vs =>
      rcases vs with _ | ⟨cv, stk₁⟩
      · exact liftP_stuck
      · dsimp only [ofRes]
        cases truthy cv with
        | none => exact liftP_stuck
        | some b =>
          cases arity f₁ bt with
          | none => exact liftP_stuck
          | some p =>
            obtain ⟨np, nr⟩ := p
            cases b <;> exact liftP_bind liftP_blockK
    | brk k vs => exact liftP_pure _
    | ret vs => exact liftP_pure _
    | trap => exact liftP_pure _
    | throw a => exact liftP_pure _
  | .tryTable bt cs body, h => by
    simp only [xFree] at h
    funext f stk
    rw [denXP_try, denXE_try, denListXP_eq_liftP body h]
    beta_reduce
    cases arity f bt with
    | none => exact liftP_stuck.symm
    | some p => exact (liftP_bind liftP_tryK).symm

theorem denListXP_eq_liftP : ∀ (es : List BExpr), xFreeL es = true →
    (denListXP (H := H) es : Frame → List Val → M (CallSig H) H ResP) =
      fun f stk => liftP (denListXE es f stk)
  | [], _ => by
    funext f stk
    show pure _ = liftP (pure _)
    exact (liftP_pure (H := H) ⟨(f, .normal stk)⟩).symm
  | e :: es, h => by
    simp only [xFreeL, Bool.and_eq_true] at h
    funext f stk
    rw [denListXP_cons, denListXE_cons, denXP_eq_liftP e h.1, denListXP_eq_liftP es h.2]
    beta_reduce
    refine (liftP_bind fun r => ?_).symm
    exact liftP_thenK r

end

end Silmaril.Proofs.Wasm.Abstract.ExposeP
