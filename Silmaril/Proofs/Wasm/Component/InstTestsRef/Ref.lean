module

public import Silmaril.Wasm.Component.InstTestsRef.Defs
public import Silmaril.Proofs.Wasm.Component.InstRef.Ref
public import Silmaril.Wasm.Component.Reference.Thms
public import Silmaril.Wasm.Verify.Kernel.Defs

/-!
# Component test binaries on the reference machine: decoding and runs

* `decodeRef_starts`, `decodeRef_trap`: `Conformance.decodeRef` reads the bytes as `startsRef`,
  `trapRef` (one definitional check by the kernel, `kernel_rfl`);
* `starts_valid`, `trap_valid`: the reference validator accepts them (`decide +kernel` on
  `check? Features.p2`, then `check?_sound`);
* `starts_ref`: from `hostConfigX`, `startsRef` instantiates, its host log is
  `[f(1) ↦ (), f(2) ↦ ()]`, and `get()` then returns `42` (`decide +kernel` on
  `sessSummaryFrom`, then `sessSummaryFrom_sound`);
* `trap_ref`: the instantiation of `trapRef` from `hostConfigX` traps (`trapSummaryL`,
  `traps_of_summaryL`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.InstTestsRef

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Conformance
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.InstTests Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Wasm.Component.Reference.Core3Adder (first)

/-! ## Decoding and validation -/

theorem decodeRef_starts : decodeRef startsBytes = .ok startsRef := by kernel_rfl

theorem decodeRef_trap : decodeRef trapBytes = .ok trapRef := by kernel_rfl

theorem starts_valid : ∃ ct, Valid Features.p2 startsRef ct := by
  have h : (check? Features.p2 startsRef).isOk = true := by decide +kernel
  cases e : check? Features.p2 startsRef with
  | error _ => rw [e] at h; cases h
  | ok ct => exact ⟨ct, check?_sound e⟩

theorem trap_valid : ∃ ct, Valid Features.p2 trapRef ct := by
  have h : (check? Features.p2 trapRef).isOk = true := by decide +kernel
  cases e : check? Features.p2 trapRef with
  | error _ => rw [e] at h; cases h
  | ok ct => exact ⟨ct, check?_sound e⟩

/-! ## Sessions from a given configuration -/

section Session

open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine

variable {E : CoreEngine} [∀ a b, Decidable (E.ExternSub a b)] {σ : Type}

/-- `sessRunBehaviours` is `sessRunFrom` from the host functions' configuration. -/
theorem sessRunBehaviours_eq (prof : ProfileKind) (h : Host E σ) (σ0 : σ) (c : CompAst E.Module)
    (ims : Iface) (calls : List (String × List Reference.Val)) :
    LinkedSession.sessRunBehaviours prof h σ0 c ims calls =
      sessRunFrom prof h (LinkedSession.hostConfig ims σ0) c (importArgs ims) calls := rfl

/-- **The executable session driver from a configuration is sound.** -/
theorem sessSummaryFrom_sound {emb : Embedder E σ} {o : Oracle E} {fuel : Nat}
    {c : CompAst E.Module} {args : Instantiate.Exports E} {m : Machine.Config E σ}
    {calls : List (String × List Reference.Val)} {p : List (Option (List Reference.Val)) × σ}
    (h : sessSummaryFrom emb o fuel c args m calls = some p) :
    p ∈ sessRunFrom o.prof (Host.ofEmbedder emb) m c args calls := by
  unfold sessSummaryFrom at h
  obtain ⟨⟨r, inst, es⟩, hi, h₁⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨fs, hfs, h₂⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h₂
  exact ⟨r.config, inst, es, fs, q.2, instantiateRun_mem emb o hi, hfs,
    Silmaril.Proofs.Wasm.Component.Reference.LinkedSession.runSess_sound emb o fuel hq, rfl⟩

end Session

/-! ## Runs -/

/-- The host log of `starts`: `f(u32 1)` and `f(u32 2)`, each answered `()`. -/
def startsLog : List HLinked2.HostEvent :=
  [(⟨0⟩, [toRefVal (.u32 1)], []), (⟨0⟩, [toRefVal (.u32 2)], [])]

theorem starts_summary' :
    (sessSummaryFrom embL first 400 startsRef (importArgs hostI) hostConfigX
        [("get", [])]).map (fun p => (p.1, p.2.2)) =
      some ([some [toRefVal (.u32 42)]], startsLog) := by
  decide +kernel

theorem starts_summary :
    sessSummaryFrom embL first 400 startsRef (importArgs hostI) hostConfigX [("get", [])] =
      some ([some [toRefVal (.u32 42)]], ((), startsLog)) := by
  obtain ⟨⟨outs, u, log⟩, h, he⟩ := Option.map_eq_some_iff.1 starts_summary'
  cases u
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact h

theorem starts_ref :
    (([some [toRefVal (.u32 42)]] : List (Option (List Value.Val))), ((), startsLog)) ∈
      sessRunFrom first.prof (Host.ofEmbedder embL) hostConfigX startsRef (importArgs hostI)
        [("get", [])] :=
  sessSummaryFrom_sound starts_summary

section Trap

open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon

/-- The instantiation of `c` with root arguments `args` from configuration `m` traps without an
`internal` fault within `fuel` steps of the logging embedder `embL`. -/
def trapSummaryL (fuel : Nat) (c : Core3Component) (args : Instantiate.Exports LinkedSession.E0)
    (m : Machine.Config LinkedSession.E0 (Unit × List HLinked2.HostEvent)) : Bool :=
  match hostStep? embL.hr (instantiateTop c args) m with
  | none => false
  | some (_, m₁) =>
    let r := Machine.run embL.hr embL.dispatch embL.X first fuel m₁
    decide (r.outcome = .trap) && !(r.labels.any Label.isInternalTrap)

/-- A trapping summary is a trapping instantiation of the reference machine. -/
theorem traps_of_summaryL {fuel : Nat} {c : Core3Component}
    {args : Instantiate.Exports LinkedSession.E0}
    {m : Machine.Config LinkedSession.E0 (Unit × List HLinked2.HostEvent)}
    (h : trapSummaryL fuel c args m = true) :
    InstResult.traps ∈ instBehaviours first.prof (Host.ofEmbedder embL) m c args := by
  unfold trapSummaryL at h
  split at h
  next => cases h
  next l m₁ e =>
    have ho : (Machine.run embL.hr embL.dispatch embL.X first fuel m₁).outcome = .trap ∧
        (Machine.run embL.hr embL.dispatch embL.X first fuel m₁).labels.any
          Label.isInternalTrap = false := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true]
        using h
    have hl : l = .host (instantiateTop c args) := hostStep?_run_label e
    have s₁ := hostStep?_sound first.prof embL.hr embL.dispatch e
    have hs := Machine.run_sound embL.hr embL.dispatch embL.X first fuel m₁
    have hT : Trapped (Machine.run embL.hr embL.dispatch embL.X first fuel m₁).config := by
      rcases Machine.run_outcome embL.hr embL.dispatch embL.X first fuel m₁ with e' | e'
      · exact absurd (e'.symm.trans ho.1) (by decide)
      · exact outcomeOf_trap _ (e' ▸ ho.1)
    refine ⟨_, _, hl ▸ Steps.cons s₁ hs, run_noHost _ _ _ _ _ _, fun msg hm => ?_, hT⟩
    have hany : (Machine.run embL.hr embL.dispatch embL.X first fuel m₁).labels.any
        Label.isInternalTrap = true :=
      List.any_eq_true.mpr ⟨_, hm, Label.isInternalTrap_trap_internal msg⟩
    exact absurd (hany.symm.trans ho.2) (by decide)

end Trap

theorem trap_ref : InstResult.traps ∈ instBehaviours first.prof (Host.ofEmbedder embL)
    hostConfigX trapRef (importArgs hostI) :=
  traps_of_summaryL (fuel := 400) (by decide +kernel)

end Silmaril.Proofs.Wasm.Component.InstTestsRef
