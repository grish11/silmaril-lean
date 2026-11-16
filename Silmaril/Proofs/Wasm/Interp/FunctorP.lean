module

public import Silmaril.Proofs.Wasm.Interp.PDivIff
public import Silmaril.Wasm.Abstract.FunctorP.Thms
public import Silmaril.Wasm.Abstract.XRecursionP.Thms

/-!
Proofs for `Silmaril.Wasm.Interp.FunctorP.Thms`: functions with the same exposed frame have the
same Core 3.0 closed observations. Their closed answers agree (the closure is the fixpoint of
`bodyCallXP`, which is read off the frame, `ExposeP.bodyCallXP_iff`), and Core 3.0 observes a
typed invocation exactly through its closed answers (`invoke_closedXP_adequacy`; divergence is
the absence of a closed answer, `invoke_diverges_iff_noAnswer`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Interp.FunctorP

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXT Silmaril.Wasm.Abstract.CallXP
open Silmaril.Wasm.Abstract.XRecursionP Silmaril.Wasm.Abstract.XDivergeP Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Interp
open Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall Silmaril.Wasm.Abstract.ExposeP

variable {H : Type}

/-- **Divergence is the absence of a closed answer**, for typed invocations. -/
theorem invoke_diverges_iff_noAnswer {tags : List TagInst} {o : GrowOracle} {s : Store H}
    {a : Nat} {vs : List Val} (hs : StoreOk s) (hok : InvokeOk s a vs)
    (hS : StoreChkE (ehExt tags) s.funcs) (hW : WasmFuncsT s) (hts : TagsOk tags s) :
    Diverges (profile o) noHostX (invoke s a vs) ↔ ¬ ∃ out, closedCallXP s a vs out := by
  have hct := invoke_callTyped hs hok hS hts
  refine ⟨fun hD => ?_, fun hne =>
    invoke_diverges_of_funDivXP hS hts hok (funDivXP_of_noAnswer hct hW hne)⟩
  rintro ⟨⟨s₂, fl⟩, hcall⟩
  obtain ⟨⟨-, -, fi, ps, rs, hfi, hty, hn⟩, -⟩ := id hct
  obtain ⟨_, _, _, _, _, hcfg⟩ := invoke_ok hs hok
  obtain ⟨hret, htr, hth⟩ := invoke_answer_steps (P := profile o) (host := noHostX) hS hts hfi hty
    hn hcall
  rcases calleeP_flow hct.1 hcall with ⟨ws, hws⟩ | hab
  · exact not_diverges_typed hcfg (hret ws hws)
      (fun x hx => Exec.BehaviourRefinement.not_step_of_terminal ⟨.values _, rfl⟩ hx) hD
  · cases fl with
    | trap =>
      exact not_diverges_typed hcfg (htr rfl)
        (fun x hx => Exec.BehaviourRefinement.not_step_of_terminal ⟨.trap, rfl⟩ hx) hD
    | throw t =>
      exact not_diverges_typed hcfg (hth t rfl)
        (fun x hx => Exec.BehaviourRefinement.not_step_of_terminal ⟨.throw t, rfl⟩ hx) hD
    | _ => exact hab.elim

/-- Equal frames give equal closed answers (non-trap). -/
theorem closedCallXP_iff_of_frame {s : Store H} {a b : Nat} {vs : List Val}
    (hfr : ((frameXP a vs : M (CallSig H) H (ULift.{1} Binaryen.Flow)).run ⟨s⟩).run =
      ((frameXP b vs : M (CallSig H) H (ULift.{1} Binaryen.Flow)).run ⟨s⟩).run)
    {s₂ : Store H} {fl : Binaryen.Flow} (hfl : fl ≠ .trap) :
    closedCallXP s a vs (s₂, fl) ↔ closedCallXP s b vs (s₂, fl) := by
  rw [closedCallXP_fixpoint, Silmaril.Wasm.Abstract.ExposeP.bodyCallXP_iff hfl,
    Silmaril.Wasm.Abstract.ExposeP.bodyCallXP_iff hfl, hfr]

theorem closedCallXP_trap_iff_of_frame {s : Store H} {a b : Nat} {vs : List Val}
    (hfr : ((frameXP a vs : M (CallSig H) H (ULift.{1} Binaryen.Flow)).run ⟨s⟩).run =
      ((frameXP b vs : M (CallSig H) H (ULift.{1} Binaryen.Flow)).run ⟨s⟩).run) :
    (∃ s₂, closedCallXP s a vs (s₂, .trap)) ↔ ∃ s₂, closedCallXP s b vs (s₂, .trap) := by
  rw [closedCallXP_fixpoint, Silmaril.Wasm.Abstract.ExposeP.bodyCallXP_trap_iff,
    Silmaril.Wasm.Abstract.ExposeP.bodyCallXP_trap_iff, hfr]

theorem trap_ne_vals (ws : List Val) : ([.trap] : List Admin) ≠ vals ws := by
  cases ws with
  | nil => simp [vals]
  | cons w ws =>
    intro h
    simp only [vals, List.map_cons, List.cons.injEq] at h
    obtain ⟨h1, -⟩ := h
    rcases w with ⟨⟨t, b⟩⟩ | b | r
    · cases t <;> exact absurd h1 (by simp [Val.toAdmin])
    · exact absurd h1 (by simp [Val.toAdmin])
    · exact absurd h1 (by simp [Val.toAdmin])

theorem trap_ne_throwing (t : Nat) : ([.trap] : List Admin) ≠ throwing t := by
  simp [throwing]

section
variable {tags : List TagInst} {o : GrowOracle} {s : Store H} {a b : Nat} {vs : List Val}
  {fi fi' : FuncInst H} {ps rs ps' rs' : List Validation.CValType}

/-- One direction of the non-trap normal forms. -/
theorem nf_transfer (hs : StoreOk s) (hoka : InvokeOk s a vs) (hokb : InvokeOk s b vs)
    (hS : StoreChkE (ehExt tags) s.funcs) (hW : WasmFuncsT s) (hts : TagsOk tags s)
    (hfa : s.funcs[a]? = some fi) (htya : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hfb : s.funcs[b]? = some fi') (htyb : Validation.DefType.funcType? fi'.type = some (ps', rs'))
    (hrs : rs.length = rs'.length)
    (hans : ∀ s₂ fl, fl ≠ .trap → closedCallXP s a vs (s₂, fl) → closedCallXP s b vs (s₂, fl))
    {c' : Config H} (hc : c'.code ≠ [.trap]) (hst : Steps (profile o) noHostX (invoke s a vs) c')
    (hnf : ∀ x, ¬ Step (profile o) noHostX c' x) : Steps (profile o) noHostX (invoke s b vs) c' := by
  obtain ⟨-, hA, -⟩ := invoke_closedXP_adequacy (o := o) hs hoka hS hW hts hfa htya
  obtain ⟨-, -, hB⟩ := invoke_closedXP_adequacy (o := o) hs hokb hS hW hts hfb htyb
  obtain ⟨-, s₂, fl, hcall, ⟨ws, hws, rfl⟩ | ⟨rfl, rfl⟩ | ⟨t, rfl, rfl⟩⟩ := hA c' hst hnf
  · have hnt : fl ≠ .trap := by rintro rfl; simp [Binaryen.Flow.retVals] at hws
    have := (hB s₂ fl (hans s₂ fl hnt hcall)).1 ws hws
    rwa [← hrs] at this
  · exact absurd rfl hc
  · exact (hB s₂ _ (hans s₂ _ (by simp) hcall)).2.2 t rfl

/-- One direction of the traps. -/
theorem trap_transfer (hs : StoreOk s) (hoka : InvokeOk s a vs) (hokb : InvokeOk s b vs)
    (hS : StoreChkE (ehExt tags) s.funcs) (hW : WasmFuncsT s) (hts : TagsOk tags s)
    (hfa : s.funcs[a]? = some fi) (htya : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hfb : s.funcs[b]? = some fi') (htyb : Validation.DefType.funcType? fi'.type = some (ps', rs'))
    (htr : (∃ s₂, closedCallXP s a vs (s₂, .trap)) → ∃ s₂, closedCallXP s b vs (s₂, .trap))
    (h : ∃ s₂, Steps (profile o) noHostX (invoke s a vs) ⟨s₂, {}, [.trap]⟩) :
    ∃ s₂, Steps (profile o) noHostX (invoke s b vs) ⟨s₂, {}, [.trap]⟩ := by
  obtain ⟨-, hA, -⟩ := invoke_closedXP_adequacy (o := o) hs hoka hS hW hts hfa htya
  obtain ⟨-, -, hB⟩ := invoke_closedXP_adequacy (o := o) hs hokb hS hW hts hfb htyb
  obtain ⟨s₂, hst⟩ := h
  obtain ⟨-, s₃, fl, hcall, hcase⟩ := hA _ hst
    (fun x hx => Exec.BehaviourRefinement.not_step_of_terminal ⟨.trap, rfl⟩ hx)
  rcases hcase with ⟨ws, -, hc⟩ | ⟨rfl, -⟩ | ⟨t, -, hc⟩
  · exact absurd (congrArg Config.code hc) (trap_ne_vals _)
  · obtain ⟨s₄, hb⟩ := htr ⟨s₃, hcall⟩
    exact ⟨s₄, (hB s₄ .trap hb).2.1 rfl⟩
  · exact absurd (congrArg Config.code hc) (trap_ne_throwing _)

theorem invoke_obs_of_frame (hs : StoreOk s) (hoka : InvokeOk s a vs) (hokb : InvokeOk s b vs)
    (hS : StoreChkE (ehExt tags) s.funcs) (hW : WasmFuncsT s) (hts : TagsOk tags s)
    (hfa : s.funcs[a]? = some fi) (htya : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hfb : s.funcs[b]? = some fi') (htyb : Validation.DefType.funcType? fi'.type = some (ps', rs'))
    (hrs : rs.length = rs'.length)
    (hfr : ((frameXP a vs : M (CallSig H) H (ULift.{1} Binaryen.Flow)).run ⟨s⟩).run =
      ((frameXP b vs : M (CallSig H) H (ULift.{1} Binaryen.Flow)).run ⟨s⟩).run) :
    (Diverges (profile o) noHostX (invoke s a vs) ↔ Diverges (profile o) noHostX (invoke s b vs)) ∧
    (∀ c' : Config H, c'.code ≠ [.trap] →
      ((Steps (profile o) noHostX (invoke s a vs) c' ∧ ∀ x, ¬ Step (profile o) noHostX c' x) ↔
        (Steps (profile o) noHostX (invoke s b vs) c' ∧ ∀ x, ¬ Step (profile o) noHostX c' x))) ∧
    ((∃ s₂, Steps (profile o) noHostX (invoke s a vs) ⟨s₂, {}, [.trap]⟩) ↔
      ∃ s₂, Steps (profile o) noHostX (invoke s b vs) ⟨s₂, {}, [.trap]⟩) := by
  have hans := fun s₂ fl (hfl : fl ≠ Binaryen.Flow.trap) => closedCallXP_iff_of_frame (s₂ := s₂) hfr hfl
  have htr := closedCallXP_trap_iff_of_frame hfr
  refine ⟨?_, fun c' hc => ⟨fun ⟨h₁, h₂⟩ => ⟨?_, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨?_, h₂⟩⟩,
    ⟨trap_transfer hs hoka hokb hS hW hts hfa htya hfb htyb htr.1,
      trap_transfer hs hokb hoka hS hW hts hfb htyb hfa htya htr.2⟩⟩
  · rw [invoke_diverges_iff_noAnswer hs hoka hS hW hts, invoke_diverges_iff_noAnswer hs hokb hS hW hts]
    refine not_congr ⟨fun ⟨⟨s₂, fl⟩, h⟩ => ?_, fun ⟨⟨s₂, fl⟩, h⟩ => ?_⟩
    · by_cases hfl : fl = .trap
      · subst hfl; obtain ⟨s₃, h'⟩ := htr.1 ⟨s₂, h⟩; exact ⟨_, h'⟩
      · exact ⟨_, (hans s₂ fl hfl).1 h⟩
    · by_cases hfl : fl = .trap
      · subst hfl; obtain ⟨s₃, h'⟩ := htr.2 ⟨s₂, h⟩; exact ⟨_, h'⟩
      · exact ⟨_, (hans s₂ fl hfl).2 h⟩
  · exact nf_transfer hs hoka hokb hS hW hts hfa htya hfb htyb hrs
      (fun s₂ fl hfl => (hans s₂ fl hfl).1) hc h₁ h₂
  · exact nf_transfer hs hokb hoka hS hW hts hfb htyb hfa htya hrs.symm
      (fun s₂ fl hfl => (hans s₂ fl hfl).2) hc h₁ h₂

end

end Silmaril.Proofs.Wasm.Interp.FunctorP
