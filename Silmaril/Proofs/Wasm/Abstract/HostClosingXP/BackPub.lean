module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.BackWhole

/-!
# The logged backward simulation, read at a final form (proofs)

* `back_vals`: a labelled run of typed trees to values is a normal logged canonical run whose
  calls resolve to exactly the run's log, ending at those values;
* `back_end`: `back_all` for trees, unfolded: a labelled run of typed trees to an end with no
  host-free step, not at a host call, is a logged canonical run whose calls resolve to exactly the
  run's log (or a resolved prefix, then a trapping callee), ending as the Core run does.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingXP

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp
open Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Abstract.CallXP (POut)

variable {H : Type} {host : HostSemantics H} {tags : List TagInst} {o : GrowOracle}

theorem not_mem_vals' {a : Admin} (ha : a.val? = none) {ws : List Val} : a ∉ vals ws := by
  intro hm
  obtain ⟨v, -, rfl⟩ := List.mem_map.1 hm
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin, Admin.val?] at ha

/-- The only outcome ending in values is falling through with them. -/
theorem ends_vals' {o : Outcome} {ws : List Val} (h : o.Ends (vals ws)) : o = .normal ws := by
  rcases o with vs | ⟨l, vs⟩ | vs | _ | a | ⟨vs, a, r⟩ | ⟨vs, r⟩
  · exact congrArg Outcome.normal (Sim.vals_injective h.symm)
  · obtain ⟨x, rest, -, h⟩ := h
    have : Admin.plain (.br x) ∈ vals ws := by rw [h]; simp
    exact (not_mem_vals' rfl this).elim
  · obtain ⟨rest, h⟩ := h
    have : Admin.plain .return_ ∈ vals ws := by rw [h]; simp
    exact (not_mem_vals' rfl this).elim
  · have : Admin.trap ∈ vals ws := by rw [show vals ws = [Admin.trap] from h]; simp
    exact (not_mem_vals' rfl this).elim
  · have : Admin.plain .throwRef ∈ vals ws := by
      rw [show vals ws = throwing a from h]; simp [throwing]
    exact (not_mem_vals' rfl this).elim
  · obtain ⟨hr, rest, h⟩ := h
    have : r ∈ vals ws := by rw [h]; simp
    exact (not_mem_vals' (Admin.val?_of_isReturnCallRef hr) this).elim
  · obtain ⟨hr, rest, h⟩ := h
    have : r ∈ vals ws := by rw [h]; simp
    exact (not_mem_vals' (Admin.val?_of_isReturnCallRef hr) this).elim

/-- **A labelled run to values is a normal logged run with exactly its log.** -/
theorem back_vals (hT : HostTyped host) (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {n : Nat} {s s₁ : Store H} {f f₁ : Frame} {stk ws : List Val} {es : List Binaryen.BExpr}
    {cs : List (Call (wasmHostSig H))} (ht : TypedP tags s f stk es)
    (hrun : EvRunN (profile o) host n ⟨s, f, tcode stk es⟩ cs ⟨s₁, f₁, vals ws⟩) :
    ∃ (l : List (OCall H)) (stk₁ : List Val), EvalLXPh s f stk es l (s₁, f₁, .flow (.normal stk₁)) ∧
      Shape.SubstPre Cl (l.map OCall.lift) cs ∧ ws = stk₁.reverse := by
  obtain ⟨l, r, hd, hres, hok⟩ := (back_all hT hH hE n).1 es s f stk _ cs ht hrun
    (ends_stuck (o := .normal ws) rfl s₁ f₁) (ends_decompose (o := .normal ws) rfl s₁)
  rcases hok with ⟨oc, he, hm⟩ | ⟨-, h⟩
  swap
  · exact (vals_ne_trap' h).elim
  obtain rfl := ends_vals' he
  obtain ⟨s', f', o'⟩ := r
  cases o' with
  | tail a args k =>
    obtain ⟨vs₁, c, h, -⟩ := matchP_tail_iff.mp hm
    cases h
  | flow fl =>
    rcases matchP_flow_iff.mp hm with ⟨rfl, rfl, hfm⟩ | ⟨-, vs, c, h, -⟩
    · rcases fl with stk₁ | _ | _ | _ | _ <;> simp only [FlowMatch] at hfm
      refine ⟨l, stk₁, hd, ?_, hfm⟩
      rcases hres with h | ⟨h, -⟩
      · exact h
      · cases h
    · cases h

/-- **A labelled run to an end is a logged run with exactly its log** (`back_all`, unfolded). -/
theorem back_end (hT : HostTyped host) (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {n : Nat} {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    {cs : List (Call (wasmHostSig H))} {c : Config H} (ht : TypedP tags s f stk es)
    (hrun : EvRunN (profile o) host n ⟨s, f, tcode stk es⟩ cs c)
    (hend : ∀ c', ¬ Step (profile o) Det.noHost c c') (hnd : decompose? c.store c.code = none) :
    ∃ (l : List (OCall H)) (r : Store H × Frame × POut), EvalLXPh s f stk es l r ∧
      (Shape.SubstPre Cl (l.map OCall.lift) cs ∨ (r.2.2 = .flow .trap ∧ TrapRes l cs)) ∧
      ((∃ oc : Outcome, oc.Ends c.code ∧ MatchP r c.store c.frame oc) ∨
        (r.2.2 = .flow .trap ∧ c.code = [.trap])) :=
  (back_all hT hH hE n).1 es s f stk c cs ht hrun hend hnd

end Silmaril.Proofs.Wasm.Abstract.HostClosingXP
