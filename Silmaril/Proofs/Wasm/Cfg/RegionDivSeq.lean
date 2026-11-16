module

public import Silmaril.Proofs.Wasm.Cfg.RegionDiv

@[expose] public section

/-!
# Sequencing diverging region runs (proofs)

`runDiv_fold`: one layer of `DivFC` over `RunDivC` is `RunDivC`. `runDiv_append`: a diverging
code diverges before any continuation. `runDiv_after`: a code that runs to values, followed by a
code that diverges from them, diverges.
-/

namespace Silmaril.Wasm.Cfg.Proofs.Region

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Region Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H} {C : Abstract.CallRel H}
  {D : Store H → Nat → List Val → Prop}

theorem runDiv_fold {s : Store H} {f : Frame} {vs : List Val} {code : List Admin}
    (h : DivFC P host C D (RunDivC P host C D) s f vs code) : RunDivC P host C D s f vs code :=
  runDiv_coind (fun s f vs c => DivFC P host C D (RunDivC P host C D) s f vs c)
    (fun _ _ _ _ hc => DivFC.mono (fun _ _ _ _ h => .inr h) hc) h

/-- **A diverging code diverges before any continuation.** -/
theorem runDiv_append {s : Store H} {f : Frame} {vs : List Val} {X : List Admin}
    (h : RunDivC P host C D s f vs X) (Y : List Admin) :
    RunDivC P host C D s f vs (X ++ Y) := by
  refine runDiv_coind (fun s f vs c => ∃ X, c = X ++ Y ∧ RunDivC P host C D s f vs X) ?_
    ⟨X, rfl, h⟩
  rintro s f vs _ ⟨X, rfl, hX⟩
  have k : ∀ {s f vs Z}, RunDivC P host C D s f vs Z →
      (∃ X, Z ++ Y = X ++ Y ∧ RunDivC P host C D s f vs X) ∨ RunDivC P host C D s f vs (Z ++ Y) :=
    fun h => .inl ⟨_, rfl, h⟩
  have k0 : ∀ {s f vs Z}, RunDivC P host C D s f vs Z →
      (∃ X, Z = X ++ Y ∧ RunDivC P host C D s f vs X) ∨ RunDivC P host C D s f vs Z :=
    fun h => .inr h
  cases runDiv_unfold hX with
  | val hv h => exact .val hv (k h)
  | simple hi h₁ h => exact .simple hi h₁ (k h)
  | brIf h => exact .brIf (by simpa using k h)
  | brData hb h => exact .brData hb (by simpa using k h)
  | block hbt hm h => exact .block hbt hm (k h)
  | loop hbt hm h => exact .loop hbt hm (k h)
  | if_ h => exact .if_ (k h)
  | tryTable hbt hm h => exact .tryTable hbt hm (k h)
  | handlerIn h => exact .handlerIn (k0 h)
  | handlerNormal hin h => exact .handlerNormal hin (k h)
  | labelIn h => exact .labelIn (k0 h)
  | labelNormal hin h => exact .labelNormal hin (k h)
  | labelBr0 hin hn h => exact .labelBr0 hin hn (by simpa using k h)
  | call hfi hty hn hcall hvs h => exact .call hfi hty hn hcall hvs (k h)
  | callDiv hfi hty hn hD => exact .callDiv hfi hty hn hD
  | callInd hres hfi hty hn hcall hvs h => exact .callInd hres hfi hty hn hcall hvs (k h)
  | callIndDiv hres hfi hty hn hD => exact .callIndDiv hres hfi hty hn hD
  | callRef hfi hty hn hcall hvs h => exact .callRef hfi hty hn hcall hvs (k h)
  | callRefDiv hfi hty hn hD => exact .callRefDiv hfi hty hn hD

/-- `return_call_ref` never falls through. -/
theorem run_retCallRef_not_normal {s s' : Store H} {f f' : Frame} {vs ws : List Val} {y : TypeIdx}
    {code : List Admin} (h : RunC P host C s f vs (.plain (.returnCallRef y) :: code) s' f'
      (.normal ws)) : False := by
  generalize ho : (Out.normal ws) = o at h
  cases h with
  | returnCallRef => cases ho
  | returnCallRefNull => cases ho
  | val hv => simp [Admin.val?] at hv
  | simple hi => simp [SingleThreaded.Det.famOf] at hi
  | simpleTrap hi => simp [SingleThreaded.Det.famOf] at hi
  | brData hb => cases hb

/-- `return_call_indirect` never falls through. -/
theorem run_retCallInd_not_normal {s s' : Store H} {f f' : Frame} {vs ws : List Val}
    {x : TableIdx} {y : TypeIdx} {code : List Admin}
    (h : RunC P host C s f vs (.plain (.tableGet x) :: .plain (.refCast ⟨true, .typeIdx y⟩) ::
      .plain (.returnCallRef y) :: code) s' f' (.normal ws)) : False := by
  rcases run_simple_inv (famOf_tableGet' x) h with ⟨_, _, _, -, h₂⟩ | ⟨ho, -⟩
  · rcases run_simple_inv (famOf_refCast' _) h₂ with ⟨_, _, _, -, h₃⟩ | ⟨ho, -⟩
    · exact run_retCallRef_not_normal h₃
    · cases ho
  · cases ho

/-- **A code that runs to values, then a code that diverges from them, diverges.** -/
theorem runDiv_after {s s₁ : Store H} {f f₁ : Frame} {vs vs₁ : List Val} {X : List Admin}
    {o : Out} (h : RunC P host C s f vs X s₁ f₁ o) (ho : o = .normal vs₁) {Y : List Admin}
    (hY : RunDivC P host C D s₁ f₁ vs₁ Y) : RunDivC P host C D s f vs (X ++ Y) := by
  induction h generalizing vs₁ with
  | nil => cases ho; simpa using hY
  | val hv _ ih => exact runDiv_fold (.val hv (ih ho hY))
  | simple hi h₁ _ ih => exact runDiv_fold (.simple hi h₁ (ih ho hY))
  | brIf _ ih => exact runDiv_fold (.brIf (by simpa using ih ho hY))
  | brData hb _ ih => exact runDiv_fold (.brData hb (by simpa using ih ho hY))
  | block hbt hm _ ih => exact runDiv_fold (.block hbt hm (ih ho hY))
  | loop hbt hm _ ih => exact runDiv_fold (.loop hbt hm (ih ho hY))
  | if_ _ ih => exact runDiv_fold (.if_ (ih ho hY))
  | tryTable hbt hm _ ih => exact runDiv_fold (.tryTable hbt hm (ih ho hY))
  | handlerNormal hin _ _ ih => exact runDiv_fold (.handlerNormal hin (ih ho hY))
  | labelNormal hin _ _ ih => exact runDiv_fold (.labelNormal hin (ih ho hY))
  | labelBr0 hin hn _ _ ih => exact runDiv_fold (.labelBr0 hin hn (by simpa using ih ho hY))
  | call hfi hty hn hcall hvs _ ih => exact runDiv_fold (.call hfi hty hn hcall hvs (ih ho hY))
  | callInd hres hfi hty hn hcall hvs _ ih =>
    exact runDiv_fold (.callInd hres hfi hty hn hcall hvs (ih ho hY))
  | callRef hfi hty hn hcall hvs _ ih =>
    exact runDiv_fold (.callRef hfi hty hn hcall hvs (ih ho hY))
  | returnCallIndirect h' _ => subst ho; exact (run_retCallInd_not_normal h').elim
  | _ => cases ho

end Silmaril.Wasm.Cfg.Proofs.Region
