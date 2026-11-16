module

public import Silmaril.Proofs.Wasm.Cfg.Bridge
public import Silmaril.Wasm.Abstract.HostEval.Thms
public import Silmaril.Wasm.Abstract.HostClosingXP.Thms

@[expose] public section

/-!
# The backward bridge: flat instructions (proofs)

`flat_bwd` (deterministic profile `SingleThreaded.profile o`, any host and oracle): a region run
of a checked, typed flat instruction other than a call is its native `evalFlat` result, with the
same store and frame and `FlowRel` flows. The non-control instructions run by Core reduction in
the region (`RunC.simple`, `RunC.simpleTrap`), and HostEval's flat completeness
(`Abstract.flat_complete`, a Core run to a stuck final form is the `evalFlat` result) identifies
the two ends. Constants, branches (`br`, `br_if`, `br_table`) and `return` are computed on both
sides. Every other region rule is excluded by the check (`flatChk` rejects calls of every form,
`throw`, structured instructions and `br_on_*`).
-/

namespace Silmaril.Wasm.Cfg.Proofs.Bridge

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Region Silmaril.Wasm.Cfg.Bridge
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Binaryen Silmaril.Wasm.Interp

set_option linter.unusedSimpArgs false

variable {H : Type} {host : HostSemantics H} {C : Abstract.CallRel H}

/-- `FlowMatch` against a Core outcome is `FlowRel` against the same region outcome. -/
theorem flowRel_of_match {fl : Flow} {oc : Logic.Core.Outcome} (h : FlowMatch fl oc) :
    FlowRel fl (ofOutcome oc) := by
  rcases fl with _ | _ | _ | _ | _ <;> rcases oc with _ | _ | _ | _ | _ | _ | _ <;>
    simp_all [FlowMatch, FlowRel, ofOutcome]

set_option linter.unusedTactic false in
/-- **A region run of a checked, typed flat instruction is its `evalFlat` result**
(deterministic profile, any host and oracle). The impossible rules share one case, which closes
some of them already at the code equation, hence the linter option. -/
theorem flat_bwd {o : SingleThreaded.GrowOracle} {s s' : Store H} {f f' : Frame}
    {stk : List Val} {i : Instr} {F : List (FuncInst H)} {mi : ModuleInst} {ret : Nat}
    {labels : List Nat} {oc : Option Nat} {out : Region.Out} (hi : ∀ x, i ≠ .call x)
    (hc : flatChk F mi f.locals.length ret labels stk.length i = some oc)
    (ht : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ [.plain i]⟩)
    (h : RunC (SingleThreaded.profile o) host C s f stk.reverse [.plain i] s' f' out) :
    ∃ fl, evalFlat s f stk i = some (s', f', fl) ∧ FlowRel fl out := by
  generalize hv : stk.reverse = vs at h
  generalize hcode : [Admin.plain i] = code at h
  cases h with
  | nil => cases hcode
  | val hva h' =>
    simp only [List.cons.injEq] at hcode
    obtain ⟨rfl, rfl⟩ := hcode
    obtain ⟨rfl, rfl, rfl⟩ := Proofs.Region.run_nil_inv h'
    cases i <;> simp [Admin.val?] at hva
    all_goals first
      | (subst hva; refine ⟨_, rfl, ?_⟩; simp [FlowRel, ← hv, ofInt])
      | simp [flatChk, flatChkE, extStep, noExt, flatEff] at hc
  | simple hi' h₁ h' =>
    simp only [List.cons.injEq, Admin.plain.injEq] at hcode
    obtain ⟨rfl, rfl⟩ := hcode
    obtain ⟨rfl, rfl, rfl⟩ := Proofs.Region.run_nil_inv h'
    subst hv
    obtain ⟨fl, hfl, hm⟩ := Abstract.flat_complete (oc := .normal _) hi hc ht h₁
      (fun _ => Sim.Step.not_vals) rfl
    exact ⟨fl, hfl, flowRel_of_match hm⟩
  | simpleTrap hi' h₁ =>
    simp only [List.cons.injEq, Admin.plain.injEq] at hcode
    obtain ⟨rfl, rfl⟩ := hcode
    subst hv
    obtain ⟨fl, hfl, hm⟩ := Abstract.flat_complete (oc := .trap) hi hc ht h₁
      (Abstract.outcome_ends_stuck (o := .trap) rfl _ _) rfl
    exact ⟨fl, hfl, flowRel_of_match hm⟩
  | trap => cases hcode
  | br =>
    simp only [List.cons.injEq, Admin.plain.injEq] at hcode
    obtain ⟨rfl, rfl⟩ := hcode
    exact ⟨_, rfl, rfl, [], by simp [← hv]⟩
  | ret =>
    simp only [List.cons.injEq, Admin.plain.injEq] at hcode
    obtain ⟨rfl, rfl⟩ := hcode
    exact ⟨_, rfl, [], by simp [← hv]⟩
  | @brIf _ _ _ _ ws k l _ _ h' =>
    simp only [List.cons.injEq, Admin.plain.injEq] at hcode
    obtain ⟨rfl, rfl⟩ := hcode
    have hs : stk = .i32 k :: ws.reverse := by
      rw [← List.reverse_reverse stk, hv]; simp
    subst hs
    by_cases hk : k = 0
    · simp only [hk, ↓reduceIte, List.nil_append] at h'
      obtain ⟨rfl, rfl, rfl⟩ := Proofs.Region.run_nil_inv h'
      subst hk
      exact ⟨.normal ws.reverse, rfl, by simp [FlowRel]⟩
    · simp only [hk, ↓reduceIte, List.singleton_append] at h'
      obtain ⟨rfl, rfl, rfl⟩ := Proofs.Region.run_br_inv h'
      refine ⟨.brk l.toNat ws.reverse, ?_, rfl, [], by simp⟩
      simp [evalFlat, truthy, asInt, Val.i32]
      exact ⟨k, rfl, hk⟩
  | brData hb h' =>
    simp only [List.cons.injEq, Admin.plain.injEq] at hcode
    obtain ⟨rfl, rfl⟩ := hcode
    cases hb with
    | @tableLt k ls d l hl =>
      obtain ⟨rfl, rfl, rfl⟩ := Proofs.Region.run_br_inv (by simpa using h')
      rename_i ws
      have hs : stk = .i32 k :: ws.reverse := by rw [← List.reverse_reverse stk, hv]; simp
      subst hs
      refine ⟨.brk l.toNat ws.reverse, ?_, rfl, [], by simp⟩
      simp [evalFlat, asInt, Val.i32]
      exact ⟨k, rfl, by erw [hl]; rfl⟩
    | @tableGe k ls l hl =>
      obtain ⟨rfl, rfl, rfl⟩ := Proofs.Region.run_br_inv (by simpa using h')
      rename_i ws
      have hs : stk = .i32 k :: ws.reverse := by rw [← List.reverse_reverse stk, hv]; simp
      subst hs
      refine ⟨.brk l.toNat ws.reverse, ?_, rfl, [], by simp⟩
      simp [evalFlat, asInt, Val.i32]
      exact ⟨k, rfl, by erw [List.getElem?_eq_none hl]; rfl⟩
    | _ => simp [flatChk, flatChkE, extStep, noExt, flatEff] at hc
  | _ =>
    simp only [List.cons.injEq, Admin.plain.injEq, reduceCtorEq, false_and] at hcode
    all_goals
      obtain ⟨h1, -⟩ := hcode
      first
        | exact absurd h1 (hi _)
        | (subst h1; simp [flatChk, flatChkE, extStep, noExt, flatEff] at hc; done)
        | (subst h1
           cases i <;> simp_all [Admin.IsReturnCallRef, Admin.IsCallRef, flatChk, flatChkE,
             extStep, noExt, flatEff])

end Silmaril.Wasm.Cfg.Proofs.Bridge
