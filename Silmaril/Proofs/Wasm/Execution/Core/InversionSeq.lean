module

public import Silmaril.Proofs.Wasm.Execution.Core.Inversion
public import Silmaril.Wasm.Execution.Core.Sim.Context

/-!
# Inversion of `call` and `call_ref` (Wasm callee) in a sequence context (proofs)

The sequence forms of `call_vals_inv` and `callRef_wasm_inv`, with a continuation `rest` left
untouched, by `Sim.Step.split_head` (as `callRef_host_inv_seq` is proved).
-/

@[expose] public section

namespace Silmaril.Wasm.Execution.Core.Proofs.Inversion

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem call_vals_inv_seq {s : Store H} {f : Frame} {c : Config H} {vs : List Val} {x : FuncIdx}
    {rest : List Admin} (h : Step P host ⟨s, f, vals vs ++ .plain (.call x) :: rest⟩ c) :
    ∃ a fi, f.module.funcs[x.toNat]? = some a ∧ s.funcs[a]? = some fi ∧
      c = ⟨s, f, vals vs ++ .ref (.func a) :: .callRefType fi.type :: rest⟩ := by
  obtain ⟨s', f', es'⟩ := c
  rcases Sim.Step.split_head (a := .plain (.call x)) rfl h with
    ⟨ws, us, is', rfl, hstep, rfl⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
  · obtain ⟨a, fi, hx, hf, hc⟩ := call_vals_inv hstep rfl
    simp only [Config.mk.injEq] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact ⟨a, fi, hx, hf, by simp⟩
  · cases h1
  · cases h1

theorem callRef_wasm_inv_seq {s : Store H} {f : Frame} {c : Config H} {vs : List Val} {a : Nat}
    {r : Admin} {fi : FuncInst H} {code : Func} {rest : List Admin} (hr : r.IsCallRef)
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm code)
    (h : Step P host ⟨s, f, vals vs ++ .ref (.func a) :: r :: rest⟩ c) :
    ∃ vs₁ vs₂ ps rs, vs = vs₁ ++ vs₂ ∧ Expand fi.type (.func ps rs) ∧ vs₂.length = ps.length ∧
      c = ⟨s, f, vals vs₁ ++ .frame rs.length (Frame.forCall fi.module vs₂ code.locals)
        [.label rs.length [] (expression code.body)] :: rest⟩ := by
  obtain ⟨s', f', es'⟩ := c
  have hcode' : vals vs ++ .ref (.func a) :: r :: rest =
      vals (vs ++ [Val.ref (.func a)]) ++ r :: rest := by simp [vals, Val.toAdmin]
  rw [hcode'] at h
  rcases Sim.Step.split_head (Admin.val?_of_isCallRef hr) h with
    ⟨ws', us', is', hsplit, hstep, rfl⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · rcases List.eq_nil_or_concat us' with rfl | ⟨us'', x, rfl⟩
    · exact (callRef_stuck hstep hr (by simp [vals])).elim
    · rw [List.concat_eq_append, ← List.append_assoc] at hsplit
      obtain ⟨rfl, hx⟩ := List.append_inj' hsplit rfl
      obtain rfl := (List.singleton_inj.1 hx).symm
      have hstep' : Step P host ⟨s, f, vals us'' ++ [.ref (.func a), r]⟩ ⟨s', f', is'⟩ := by
        simpa [vals, Val.toAdmin] using hstep
      obtain ⟨vs₁, vs₂, ps, rs, rfl, he, hn, hc⟩ := callRef_wasm_inv hstep' hr hf hcode rfl
      refine ⟨ws' ++ vs₁, vs₂, ps, rs, by simp, he, hn, ?_⟩
      simp only [Config.mk.injEq] at hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      simp
  · simp [Admin.IsCallRef] at hr
  · simp [Admin.IsCallRef] at hr

end Silmaril.Wasm.Execution.Core.Proofs.Inversion
