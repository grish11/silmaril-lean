module

public import Silmaril.Wasm.Abstract.HostEval.Defs
public import Silmaril.Wasm.Abstract.HostCall.Thms
public import Silmaril.Wasm.Abstract.Recursion.Thms
public import Silmaril.Wasm.Logic.Core.Thms

/-!
# The native semantics with host calls (proofs)
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostEval

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Validation Silmaril.Wasm.Logic.Core

variable {H : Type}

theorem hostCall_fixpoint (host : HostSemantics H) :
    hostCall host = bodyCall (hostCall host) ⊔ hostAns host :=
  ((hostCallOp host).map_lfp).symm

theorem hostAns_closedHost : hostAns (closedHost : HostSemantics H) = ⊥ := by
  funext s a args out
  apply propext
  constructor
  · rintro ⟨_, _, _, _, _, h, _⟩
    exact h.elim
  · intro h
    exact h.elim

/-- With the closed host, closing with host calls is plain closing. -/
theorem hostCall_closedHost : hostCall (closedHost : HostSemantics H) = closedCall := by
  apply le_antisymm
  · refine OrderHom.lfp_le _ ?_
    intro s a args out h
    rcases h with h | h
    · rw [closedCall_fixpoint]
      exact h
    · rw [hostAns_closedHost] at h
      exact h.elim
  · refine OrderHom.lfp_le _ ?_
    intro s a args out h
    rw [hostCall_fixpoint]
    exact .inl h

variable {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

theorem vals_split (stk : List Val) (n : Nat) :
    vals stk.reverse = vals (stk.drop n).reverse ++ vals (stk.take n).reverse := by
  conv_lhs => rw [← List.take_append_drop n stk]
  simp [vals]

/-- **The host-call case of the forward simulation.** A native call of a host
function answered with values `vs` continues, in Core, at the native
continuation stack, in the host's store. -/
theorem wp_host_callOk {s₁ s₂ : Store H} {f₁ : Frame} {stk₁ : List Val} {x : Silmaril.Wasm.FuncIdx}
    {a : Nat} {fi : FuncInst H} {h : H} {ps rs : Ty (.list .val)} {vs : List Val}
    {rest : List Admin} {Q : Post H}
    (hx : f₁.module.funcs[x.toNat]? = some a) (hf : s₁.funcs[a]? = some fi)
    (he : Expand fi.type (.func ps rs)) (hcode : fi.code = .host h)
    (hlen : ps.length ≤ stk₁.length) (hres : vs.length = rs.length)
    (hans : host h s₁ (stk₁.take ps.length).reverse (.returned s₂ (.values vs)))
    (hk : WP P host s₂ f₁
      (vals ((vs.reverse.take rs.length) ++ stk₁.drop ps.length).reverse ++ rest) Q) :
    WP P host s₁ f₁ (vals stk₁.reverse ++ .plain (.call x) :: rest) Q := by
  have hn : ((stk₁.take ps.length).reverse).length = ps.length := by
    simp only [List.length_reverse, List.length_take]
    omega
  have st := coreHost_call_answer (P := P) (ws := (stk₁.drop ps.length).reverse) (rest := rest)
    hx hf he hn hcode (show coreHostRel host ⟨h, s₁, _⟩ (.answer (s₂, .values vs)) from hans)
  rw [vals_split stk₁ ps.length]
  have htk : vs.reverse.take rs.length = vs.reverse := by
    rw [List.take_of_length_le (by simp [hres])]
  rw [htk] at hk
  refine WP.steps (by simpa [List.append_assoc] using st) ?_
  simpa [vals, Result.toAdmin, List.reverse_append, List.append_assoc] using hk

/-- **The host-trap case of the forward simulation.** -/
theorem steps_host_callTrap {s₁ s₂ : Store H} {f₁ : Frame} {stk₁ : List Val}
    {x : Silmaril.Wasm.FuncIdx} {a : Nat} {fi : FuncInst H} {h : H} {ps rs : Ty (.list .val)}
    {rest : List Admin}
    (hx : f₁.module.funcs[x.toNat]? = some a) (hf : s₁.funcs[a]? = some fi)
    (he : Expand fi.type (.func ps rs)) (hcode : fi.code = .host h)
    (hlen : ps.length ≤ stk₁.length)
    (hans : host h s₁ (stk₁.take ps.length).reverse (.returned s₂ .trap)) :
    Steps P host ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) :: rest⟩ ⟨s₂, f₁, [.trap]⟩ := by
  have hn : ((stk₁.take ps.length).reverse).length = ps.length := by
    simp only [List.length_reverse, List.length_take]
    omega
  have st := coreHost_call_answer (P := P) (ws := (stk₁.drop ps.length).reverse) (rest := rest)
    hx hf he hn hcode (show coreHostRel host ⟨h, s₁, _⟩ (.answer (s₂, .trap)) from hans)
  rw [vals_split stk₁ ps.length]
  refine (by simpa [List.append_assoc] using st : Steps P host _ _).trans ?_
  simpa [Result.toAdmin] using steps_trap (P := P) (host := host) s₂ f₁ _ rest

end Silmaril.Proofs.Wasm.Abstract.HostEval
