module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp.Callout
public import Silmaril.Proofs.Wasm.Component.Reference.CalloutMap

/-!
# Host-call redexes, statuses and resumption under a change of host code

`Reference.CalloutMap` renames the host code of a store towards the indices of a game semantics
(`H → Nat`); the reference machine of the decoded binaries renames the other way, from the IR's
import indices to the `canon lower` trampolines (`Nat → CanonHost`). The proofs do not depend on
the direction; this module restates them for any renaming `g : H → H'`:

* `decompose?_mapH_eqG`, `config_mapHG`, `decompose?_config_mapHG`: a host-call redex of the
  store is the redex of the renamed store, with the host code renamed;
* `status_mapH_callout`, `status_mapH_returned`: the status of a thread at a callout, or
  returned, is the same in the renamed store (with the host code renamed);
* `resume_mapHG`: resumption does not depend on host code.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded

variable {H H' : Type} (g : H → H')

/-! ## Redexes -/

theorem hostArity?_mapHG (s : Store H) (a : Nat) :
    hostArity? (Store.mapH g s) a = (hostArity? s a).map fun p => (g p.1, p.2) := by
  unfold hostArity?
  rw [Store.mapH_funcs_getElem?]
  cases s.funcs[a]? with
  | none => rfl
  | some fi =>
    simp only [Option.map_some]
    cases hc : fi.code <;> cases hft : fi.type.funcType? <;>
      simp [FuncInst.mapH, hc, hft, FuncCode.mapH]

/-- The renaming of a redex. -/
def mapRG : Ctx × Nat × H × List Execution.Core.Val → Ctx × Nat × H' × List Execution.Core.Val :=
  fun x => (x.1, x.2.1, g x.2.2.1, x.2.2.2)

theorem topRedex_mapHG (s : Store H) (vs : List Execution.Core.Val) (rest : List Admin) :
    topRedex (Store.mapH g s) vs rest = (topRedex s vs rest).map (mapRG g) := by
  unfold topRedex
  split
  · rw [hostArity?_mapHG]
    cases hostArity? s _ with
    | none => rfl
    | some p =>
      show (if p.2 ≤ _ then _ else none) = Option.map _ (if p.2 ≤ _ then _ else none)
      split <;> rfl
  · rfl

theorem decompose?_mapH_eqG (s : Store H) (code : List Admin) :
    decompose? (Store.mapH g s) code = (decompose? s code).map (mapRG g) := by
  rw [decompose?_eq, decompose?_eq]
  rcases hsp : splitVals code with ⟨vs, _ | ⟨d, rest⟩⟩
  · rfl
  · show decompHead (Store.mapH g s) vs d rest = (decompHead s vs d rest).map (mapRG g)
    cases d with
    | label n cont body =>
      simp only [decompHead, decompose?_mapH_eqG s body, Option.map_map]
      rfl
    | handler n cs body =>
      simp only [decompHead, decompose?_mapH_eqG s body, Option.map_map]
      rfl
    | frame n f body =>
      simp only [decompHead, decompose?_mapH_eqG s body, Option.map_map]
      rfl
    | plain i =>
      simp only [decompHead]
      split
      · exact topRedex_mapHG g s vs rest
      · rfl
    | ref r => rfl
    | callRefType t => exact topRedex_mapHG g s vs rest
    | returnCallRefType t => rfl
    | trap => rfl
termination_by sizeOf code
decreasing_by
  all_goals
    have h := splitVals_snd_sizeOf code
    rw [hsp] at h
    simp only [List.cons.sizeOf_spec, Admin.label.sizeOf_spec, Admin.handler.sizeOf_spec,
      Admin.frame.sizeOf_spec] at h
    omega

/-! ## Threads -/

theorem config_mapHG (s : Store H) (t : Thread) :
    t.config (Store.mapH g s) = Config.mapH g (t.config s) := by
  cases t with
  | pending a args => exact (invoke_mapH g s a args).symm
  | active f code => rfl

theorem decompose?_config_mapHG (s : Store H) (t : Thread) :
    decompose? (Store.mapH g s) (t.config (Store.mapH g s)).code =
      (decompose? s (t.config s).code).map (mapRG g) := by
  rw [config_mapHG, show (Config.mapH g (t.config s)).code = (t.config s).code from rfl]
  exact decompose?_mapH_eqG g s _


/-! ## Statuses and resumption -/

variable {g} {o : GrowOracle}

theorem resume_mapHG (s : Store H) (t : Thread) (r : CallResult) :
    resume (Store.mapH g s) t r = resume s t r := by
  unfold resume
  dsimp only
  rw [decompose?_config_mapHG]
  cases decompose? s (t.config s).code with
  | none => rfl
  | some x =>
    simp only [Option.map_some, config_mapHG]
    rfl

theorem code_config_mapHG (s : Store H) (t : Thread) :
    (t.config (Store.mapH g s)).code = (t.config s).code := by
  rw [config_mapHG]
  rfl

/-- **A callout is a callout of the renamed store**, with the host code renamed. -/
theorem status_mapH_callout {s : Store H} {t : Thread} {h : H} {args : List Execution.Core.Val}
    (hst : status o s t = .callout h args) : status o (Store.mapH g s) t = .callout (g h) args := by
  obtain ⟨E, a, hd⟩ := status_callout_inv hst
  have hd' : decompose? (Store.mapH g s) (t.config (Store.mapH g s)).code =
      some (E, a, g h, args) := by
    rw [decompose?_config_mapHG, hd]
    rfl
  have hc := code_config_mapHG (g := g) s t
  unfold status at hst ⊢
  dsimp only at hst ⊢
  rw [hd] at hst
  rw [hd']
  rw [hc]
  split_ifs at hst ⊢ <;> rfl

/-- **A returned status is the status of the renamed store.** -/
theorem status_mapH_returned {s : Store H} {t : Thread} {r : CallResult}
    (hst : status o s t = .returned r) : status o (Store.mapH g s) t = .returned r := by
  have hc := code_config_mapHG (g := g) s t
  have hd := decompose?_config_mapHG g s t
  unfold status at hst ⊢
  dsimp only at hst ⊢
  rw [hd]
  rw [hc]
  split_ifs at hst ⊢ <;> (cases hd' : decompose? s (t.config s).code <;> simp_all)

end Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp
