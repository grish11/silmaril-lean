module

public import Silmaril.Project.Shapes.WasmWast.Defs
public import Silmaril.Wasm.Game.Instantiate.Thms
public import Silmaril.Wasm.SingleThreaded.Exec.InvokeRun
public import Silmaril.Wasm.SingleThreaded.Exec.StatusComplete
public import Silmaril.Wasm.SingleThreaded.Determinism.Join
public import Silmaril.Wasm.SingleThreaded.Soundness
public import Silmaril.Wasm.Verify.Kernel.Thms

/-!
# Proofs: WAST script commands from one kernel evaluation

* `storeOk_of_inst`: the store of an instantiated module (valid, no imports, scalar function
  exports) is well typed, through `Silmaril.Wasm.Game.IsInstance.ok`;
* `invokeOk_of_invokeOkB`: typed arguments give the premise `InvokeOk` of `$invoke`;
* `actK_sound`: a stopped run of `runInvokeK` at a result is a host-free normal form, and its
  store is well typed (`runInvoke?_steps_noHost`, `runInvoke?_stopped`, `runInvoke?_sound`);
* `invokeNF_unique`: host-free normal forms of an invocation are unique (`DStep.join'`,
  `nf_unique_of_join`), hence `scriptAt_unique`: a script reaches at most one state;
* `scriptHolds_of_kernel`: `scriptK … = true` gives `ScriptHolds`.
-/

@[expose] public section

namespace Silmaril.Proofs.Project.Shapes.WasmWast

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded Silmaril.Project.Shapes.WasmWast

/-! ## Instances -/

theorem forall₂_of_mapM {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → List.Forall₂ (fun a b => f a = some b) l l'
  | [], l', h => by simp at h; subst h; exact .nil
  | a :: l, l', h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [ha, hl] at h
      | some bs =>
        have h' : b :: bs = l' := by simpa [ha, hl] using h
        subst h'
        exact .cons ha (forall₂_of_mapM hl)

/-- The store of an instantiated module with no imports and scalar function exports is well
typed. -/
theorem storeOk_of_inst {m : Module} {mt : CModuleType} {s : Store Nat} {f : Frame}
    (hv : validate? m = some mt) (himp : mt.imports = [])
    (hi : instantiateOnce? (Game.importStore []) m [] = some (s, f, none))
    (hx : exportsScalar s f.module = true) : StoreOk s := by
  unfold exportsScalar at hx
  obtain ⟨ts, hts⟩ := Option.isSome_iff_exists.mp hx
  have hI : Game.IsInstance m mt ⟨[], ts, Game.exportFuncAddrs f.module, s⟩ := by
    refine ⟨hv, by simp [himp], by simp [himp, CExternType.funcs], ⟨f, ?_, rfl⟩, ?_⟩
    · rw [himp]
      exact hi
    · refine (forall₂_of_mapM hts).imp fun a ft h => ?_
      cases hf : s.funcs[a]? with
      | none => simp [hf] at h
      | some fi => exact ⟨fi, rfl, by simpa [hf] using h⟩
  exact hI.ok.storeOk

/-! ## Invocations -/

theorem valOk_of_argsOk {s : Store Nat} :
    ∀ {vs : List Val} {ps : List CValType}, argsOk vs ps = true → List.Forall₂ (ValOk s) vs ps
  | [], [], _ => .nil
  | .num n :: vs, p :: ps, h => by
    simp only [argsOk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, h⟩ := h
    exact .cons (.num n) (valOk_of_argsOk h)
  | [], _ :: _, h => by simp [argsOk] at h
  | _ :: _, [], h => by cases ‹Val› <;> simp [argsOk] at h
  | .vec _ :: _, _ :: _, h => by simp [argsOk] at h
  | .ref _ :: _, _ :: _, h => by simp [argsOk] at h

theorem invokeOk_of_invokeOkB {s : Store Nat} {a : Nat} {args : List Val}
    (h : invokeOkB s a args = true) : InvokeOk s a args := by
  unfold invokeOkB at h
  split at h
  · rename_i fi hfi
    split at h
    · rename_i ps rs hft
      unfold DefType.funcType? at hft
      split at hft
      · rename_i P R hex
        simp only [Option.some.injEq, Prod.mk.injEq] at hft
        obtain ⟨rfl, rfl⟩ := hft
        exact ⟨fi, P, R, hfi, Expand.iff.mpr hex, valOk_of_argsOk h⟩
      · cases hft
    · cases h
  · cases h

/-- A stopped kernel run at a result is a host-free normal form with a well-typed store. -/
theorem actK_sound {o : GrowOracle} {fuel : Nat} {mi : ModuleInst} {s : Store Nat}
    {act : Action} {c : Config Nat} (hs : StoreOk s) (h : actK o fuel mi s act = some c) :
    ∃ a, exportFunc? mi act.name = some a ∧ InvokeNF o s a act.args c ∧
      (∃ r, c.outcome? = some r) ∧ StoreOk c.store := by
  unfold actK at h
  split at h
  · rename_i a ha
    split at h
    · rename_i hok
      have hi := invokeOk_of_invokeOkB hok
      split at h
      · rename_i c' r hrun
        cases h
        rw [Silmaril.Wasm.Verify.Kernel.runInvokeK_eq] at hrun
        obtain ⟨-, hr⟩ := Exec.InvokeRun.runInvoke?_eq_some hrun
        have hst := Exec.InvokeRun.runInvoke?_steps_noHost hs hi hrun
        have hnf := (Exec.InvokeRun.runInvoke?_stopped hs hi hrun).2
        obtain ⟨-, ⟨_, _, _, _, _, hok'⟩, -⟩ := Exec.InvokeRun.runInvoke?_sound hs hi hrun
        exact ⟨a, ha, ⟨hst, hnf⟩, ⟨r, hr.symm⟩, ConfigOk.storeOk hok'⟩
      · cases h
    · cases h
  · cases h

/-- Host-free normal forms of an invocation under `profile o` are unique. -/
theorem invokeNF_unique {o : GrowOracle} {s : Store Nat} {a : Nat} {args : List Val}
    {c c' : Config Nat} (h : InvokeNF o s a args c) (h' : InvokeNF o s a args c') : c = c' :=
  nf_unique_of_join (R := Det.DStep o) (fun ha hb => Det.DStep.join' ha hb) h.1 h'.1 h.2 h'.2

/-! ## Scripts -/

theorem instance_unique {m : Module} {s s' : Store Nat} {mi mi' : ModuleInst}
    (h : Instance m s mi) (h' : Instance m s' mi') : s = s' ∧ mi = mi' := by
  obtain ⟨-, f, hf, rfl⟩ := h
  obtain ⟨-, f', hf', rfl⟩ := h'
  rw [hf] at hf'
  simp only [Option.some.injEq, Prod.mk.injEq] at hf'
  obtain ⟨rfl, rfl, -⟩ := hf'
  exact ⟨rfl, rfl⟩

theorem run_unique {o : GrowOracle} {mi : ModuleInst} {s s₁ s₂ : Store Nat} {acts : List Action}
    (h₁ : Run o mi s acts s₁) (h₂ : Run o mi s acts s₂) : s₁ = s₂ := by
  induction h₁ with
  | nil => cases h₂; rfl
  | cons ha hc _ _ ih =>
    cases h₂ with
    | cons ha' hc' _ h' =>
      rw [ha] at ha'
      cases ha'
      cases invokeNF_unique hc hc'
      exact ih h'

theorem run_append {o : GrowOracle} {mi : ModuleInst} {s s₁ s₂ : Store Nat}
    {l₁ l₂ : List Action} (h₁ : Run o mi s l₁ s₁) (h₂ : Run o mi s₁ l₂ s₂) :
    Run o mi s (l₁ ++ l₂) s₂ := by
  induction h₁ with
  | nil => exact h₂
  | cons ha hc hr _ ih => exact .cons ha hc hr (ih h₂)

/-- A script reaches at most one state. -/
theorem scriptAt_unique {o : GrowOracle} {m : Module} {pre : List Action}
    {mi mi' : ModuleInst} {s s' : Store Nat} (h : ScriptAt o m pre mi s)
    (h' : ScriptAt o m pre mi' s') : mi = mi' ∧ s = s' := by
  obtain ⟨s₀, hI, hr⟩ := h
  obtain ⟨s₀', hI', hr'⟩ := h'
  obtain ⟨rfl, rfl⟩ := instance_unique hI hI'
  exact ⟨rfl, run_unique hr hr'⟩

/-- The claim of one command, at the unique state of the script before it. -/
theorem holds_of_run {o : GrowOracle} {m : Module} {pre : List Action} {mi : ModuleInst}
    {s : Store Nat} {act : Action} {a : Nat} {c : Config Nat} {r : Result}
    (hS : ScriptAt o m pre mi s) (ha : exportFunc? mi act.name = some a)
    (hc : InvokeNF o s a act.args c) (hr : c.outcome? = some r) :
    Reaches o m pre act r ∧ Only o m pre act r := by
  refine ⟨⟨mi, s, a, c, hS, ha, hc, hr⟩, fun mi' s' a' c' hS' ha' hc' => ?_⟩
  obtain ⟨rfl, rfl⟩ := scriptAt_unique hS hS'
  rw [ha] at ha'
  cases ha'
  rw [← invokeNF_unique hc hc']
  exact hr

theorem cmdsK_holds {o : GrowOracle} {fuel : Nat} {m : Module} {mi : ModuleInst} :
    ∀ {cmds : List Cmd} {done : List Action} {s : Store Nat}, StoreOk s →
      ScriptAt o m done mi s → cmdsK o fuel mi s cmds = true →
      ∀ k (cmd : Cmd), cmds[k]? = some cmd → cmd.Holds o m (done ++ pre cmds k)
  | [], _, _, _, _, _, k, _, hk => by simp at hk
  | cmd :: cmds, done, s, hs, hS, h, k, cmd', hk => by
    unfold cmdsK at h
    split at h
    · rename_i c hc
      obtain ⟨a, ha, hnf, ⟨r, hr⟩, hs'⟩ := actK_sound hs hc
      simp only [Bool.and_eq_true] at h
      obtain ⟨he, h⟩ := h
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        simp only [pre, List.take_zero, List.map_nil, List.append_nil]
        rcases cmd with ⟨act, _ | e⟩
        · trivial
        · simp only [decide_eq_true_eq] at he
          have := holds_of_run hS ha hnf he
          cases e <;> exact this
      | succ k =>
        simp only [List.getElem?_cons_succ] at hk
        obtain ⟨s₀, hI, hrun⟩ := hS
        have hS' : ScriptAt o m (done ++ [cmd.act]) mi c.store :=
          ⟨s₀, hI, run_append hrun (.cons ha hnf hr (.nil _))⟩
        have := cmdsK_holds hs' hS' h k cmd' hk
        simpa [pre, List.take_succ_cons, List.append_assoc] using this
    · cases h

/-- **One kernel evaluation proves every command of a script.** -/
theorem scriptHolds_of_kernel {o : GrowOracle} {fuel : Nat} {m : Module} {cmds : List Cmd}
    (h : scriptK o fuel m cmds = true) : ScriptHolds o m cmds := by
  unfold scriptK at h
  split at h
  · rename_i mt hv
    simp only [Bool.and_eq_true, List.isEmpty_iff] at h
    obtain ⟨himp, h⟩ := h
    split at h
    · rename_i s f hi
      simp only [Bool.and_eq_true] at h
      obtain ⟨hx, h⟩ := h
      have hs := storeOk_of_inst hv himp hi hx
      have hS : ScriptAt o m [] f.module s :=
        ⟨s, ⟨⟨mt.exports, by rw [← himp]; exact validate?_sound hv⟩, f, hi, rfl⟩, .nil _⟩
      intro k cmd hk
      simpa using cmdsK_holds hs hS h k cmd hk
    · cases h
  · cases h

end Silmaril.Proofs.Project.Shapes.WasmWast

end
