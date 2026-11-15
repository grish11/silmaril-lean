module

public import Silmaril.Proofs.Wasm.Execution.Core.Inversion

/-!
# Inversion of `call_ref` on a host function (proofs)

The host counterpart of `callRef_wasm_inv`, by the same induction. A Core step
of `vals vs ++ [ref.func a, call_ref]` with a host function at `a` either takes
a host answer (`call_ref-hostfunc`) or stutters on host divergence
(`call_ref-hostfunc-div`), on the top `ps.length` values. Consequently a call
the host has no outcome for has no step (`callRef_host_stuck`).
-/

@[expose] public section

namespace Silmaril.Wasm.Execution.Core.Proofs.Inversion

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded (Det.famOf Det.Fam Det.FamShape)

variable {H : Type} {P : Profile} {host : HostSemantics H}

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem callRef_host_inv {c c' : Config H} (h : Step P host c c') :
    ∀ {vs : List Val} {a : Nat} {r : Admin} {fi : FuncInst H} {hh : H}, r.IsCallRef →
      c.store.funcs[a]? = some fi → fi.code = .host hh →
      c.code = vals vs ++ [.ref (.func a), r] →
      ∃ vs₁ vs₂ ps rs, vs = vs₁ ++ vs₂ ∧ Expand fi.type (.func ps rs) ∧ vs₂.length = ps.length ∧
        ((∃ s' res, host hh c.store vs₂ (.returned s' res) ∧
            c' = ⟨s', c.frame, vals vs₁ ++ res.toAdmin⟩) ∨
          (host hh c.store vs₂ .diverged ∧
            c' = ⟨c.store, c.frame, vals vs₁ ++ vals vs₂ ++ [.ref (.func a), r]⟩)) := by
  induction h with
  | callRefFunc hr' hf' _ _ hcode' =>
    intro vs a r fi hh hr hf hcode hc
    obtain ⟨rfl, hx, rfl⟩ := last_two rfl rfl (Admin.val?_of_isCallRef hr')
      (Admin.val?_of_isCallRef hr) hc
    simp only [Admin.ref.injEq, Ref.func.injEq] at hx
    subst hx
    obtain rfl : _ = fi := Option.some.inj (hf'.symm.trans hf)
    cases hcode'.symm.trans hcode
  | callRefHost hr' hf' he hn hcode' hhost =>
    intro vs a r fi hh hr hf hcode hc
    obtain ⟨rfl, hx, rfl⟩ := last_two rfl rfl (Admin.val?_of_isCallRef hr')
      (Admin.val?_of_isCallRef hr) hc
    simp only [Admin.ref.injEq, Ref.func.injEq] at hx
    subst hx
    obtain rfl : _ = fi := Option.some.inj (hf'.symm.trans hf)
    obtain rfl := FuncCode.host.inj (hcode'.symm.trans hcode)
    exact ⟨[], _, _, _, rfl, he, hn, .inl ⟨_, _, hhost, by simp [vals]⟩⟩
  | callRefHostDiv hr' hf' he hn hcode' hhost =>
    intro vs a r fi hh hr hf hcode hc
    obtain ⟨rfl, hx, rfl⟩ := last_two rfl rfl (Admin.val?_of_isCallRef hr')
      (Admin.val?_of_isCallRef hr) hc
    simp only [Admin.ref.injEq, Ref.func.injEq] at hx
    subst hx
    obtain rfl : _ = fi := Option.some.inj (hf'.symm.trans hf)
    obtain rfl := FuncCode.host.inj (hcode'.symm.trans hcode)
    exact ⟨[], _, _, _, rfl, he, hn, .inr ⟨hhost, by simp [vals]⟩⟩
  | callRefNull hr' =>
    intro vs a r fi hh hr hf hcode hc
    obtain ⟨-, hx, -⟩ := last_two (vs := []) rfl rfl (Admin.val?_of_isCallRef hr')
      (Admin.val?_of_isCallRef hr) (by simpa [vals] using hc)
    cases hx
  | @ctxtInstrs s s' f f' vs₀ is is' rest hs hne ih =>
    intro vs a r fi hh hr hf hcode hc
    dsimp only at hc hf ⊢
    obtain ⟨w, b, t, hb, rfl⟩ := Sim.exists_head_of_not_all hs.not_all_isVal
    have hc' : vals (vs₀ ++ w) ++ b :: (t ++ rest) =
        vals (vs ++ [.ref (.func a)]) ++ r :: [] := by
      simpa [vals, Val.toAdmin] using hc
    obtain ⟨h1, rfl, h3⟩ := Sim.vals_append_cons_inj hb (Admin.val?_of_isCallRef hr) hc'
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 h3
    rcases List.eq_nil_or_concat w with rfl | ⟨w', x, rfl⟩
    · exact (callRef_stuck hs hr (by simp [vals])).elim
    · have h1' : (vs₀ ++ w') ++ [x] = vs ++ [Val.ref (.func a)] := by simpa using h1
      obtain ⟨hv, h2⟩ := List.append_inj' h1' rfl
      obtain rfl := List.singleton_inj.1 h2
      subst hv
      obtain ⟨vs₁, vs₂, ps, rs, rfl, he, hn, hres⟩ :=
        ih (vs := w') hr hf hcode (by simp [vals, Val.toAdmin])
      refine ⟨vs₀ ++ vs₁, vs₂, ps, rs, by simp, he, hn, ?_⟩
      rcases hres with ⟨s'', res, hhost, hc''⟩ | ⟨hhost, hc''⟩
      · simp only [Config.mk.injEq] at hc''
        obtain ⟨rfl, rfl, rfl⟩ := hc''
        exact .inl ⟨_, _, hhost, by simp⟩
      · simp only [Config.mk.injEq] at hc''
        obtain ⟨rfl, rfl, rfl⟩ := hc''
        exact .inr ⟨hhost, by simp⟩
  | @trapInstrs s f vs₀ rest _ =>
    intro vs a r fi hh hr hf hcode hc
    have hc' : vals vs₀ ++ Admin.trap :: rest = vals (vs ++ [.ref (.func a)]) ++ r :: [] := by
      simpa [vals, Val.toAdmin] using hc
    obtain ⟨-, rfl, -⟩ := Sim.vals_append_cons_inj rfl (Admin.val?_of_isCallRef hr) hc'
    simp [Admin.IsCallRef] at hr
  | @throwRefInstrs s f vs₀ x rest _ =>
    intro vs a r fi hh hr hf hcode hc
    have hc' : vals (vs₀ ++ [.ref (.exn x)]) ++ Admin.plain .throwRef :: rest =
        vals (vs ++ [.ref (.func a)]) ++ r :: [] := by
      simpa [vals, Val.toAdmin, throwing] using hc
    obtain ⟨-, rfl, -⟩ := Sim.vals_append_cons_inj rfl (Admin.val?_of_isCallRef hr) hc'
    simp [Admin.IsCallRef] at hr
  | _ =>
    intro vs a r fi hh hr hf hcode hc
    have hl := congrArg List.getLast? hc
    simp only [List.getLast?_append, List.getLast?_singleton, List.getLast?_cons_cons,
      Option.some_or, List.getLast?_cons] at hl
    have hk := isCallRef_control hr
    first
      | (exact absurd (fam_parametric ‹_› hl) (by simp [hk]))
      | (exact absurd (fam_numeric ‹_› hl) (by simp [hk]))
      | (exact absurd (fam_vector ‹_› hl) (by simp [hk]))
      | (exact absurd (fam_variable ‹_› hl) (by simp [hk]))
      | (exact absurd (fam_table ‹_› hl) (by simp [hk]))
      | (exact absurd (fam_memory ‹_› hl) (by simp [hk]))
      | (exact absurd (fam_reference ‹_› hl) (by simp [hk]))
      | (exact absurd (fam_aggregate ‹_› hl) (by simp [hk]))
      | (simp at hl; done)
      | (simp at hl; subst hl; simp [Admin.IsCallRef] at hr; done)
      | (simp at hl; subst hl; simp [Admin.IsCallRef, Det.famOf] at hk; done)

/-- **A host call with no host outcome is stuck**, on exactly its arguments. -/
theorem callRef_host_stuck {s : Store H} {f : Frame} {c : Config H} {vs : List Val} {a : Nat}
    {r : Admin} {fi : FuncInst H} {hh : H} {ps rs : Ty (.list .val)} (hr : r.IsCallRef)
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh) (he : Expand fi.type (.func ps rs))
    (hn : vs.length = ps.length) (hno : ∀ o, ¬ host hh s vs o) :
    ¬ Step P host ⟨s, f, vals vs ++ [.ref (.func a), r]⟩ c := by
  intro h
  obtain ⟨vs₁, vs₂, ps', rs', rfl, he', hn', hres⟩ := callRef_host_inv h hr hf hcode rfl
  have := (Expand.iff.1 he).symm.trans (Expand.iff.1 he')
  simp only [Option.some.injEq, Ty.func.injEq] at this
  obtain ⟨rfl, rfl⟩ := this
  simp only [List.length_append] at hn
  obtain rfl : vs₁ = [] := List.eq_nil_of_length_eq_zero (by omega)
  rcases hres with ⟨s', res, hhost, -⟩ | ⟨hhost, -⟩
  · exact hno _ hhost
  · exact hno _ hhost

end Silmaril.Wasm.Execution.Core.Proofs.Inversion
