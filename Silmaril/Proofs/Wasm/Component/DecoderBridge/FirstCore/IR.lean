module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore.CoreSim
public import Silmaril.Proofs.Wasm.Component.Reference.InstImpCore
public import Silmaril.Wasm.Component.DecoderBridge.Sim.Defs

/-!
# A failing first node of the IR, as a run of its module alone

`NodeQuiet n (.fail ()) cm w` (`DecoderBridge.Sim.Defs`) is a run of the engine instance of the
decoded module `m` of `cm` (`Param.instOfI` at `profile o`). When `m` has no imports:

* `coreIface_exports`, `coreIface_imports`: the interface `coreIface` reads has the module's
  function export names in order (`funcExportNames`), and no imports;
* `exportAddrs_some`: so the IR's export lookup succeeds whenever preparation does
  (`lookup_funcExport_gen`);
* `nodeQuiet_fail`: a quiet failure of the node is a failed preparation of `m` in the empty
  store, or a preparation with a start function whose run (`Internal o`) traps.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.DecoderBridge
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SingleThreaded (GrowOracle Internal status profile)

/-! ## The interface of a decoded module -/

theorem forIn_names {α β : Type} {F : α → Array β → Except String (ForInStep (Array β))}
    {name : β → String} {sel : α → Option String}
    (hF : ∀ x acc r, F x acc = .ok r →
      (sel x = none ∧ r = .yield acc) ∨ ∃ v, sel x = some (name v) ∧ r = .yield (acc.push v)) :
    ∀ (xs : List α) (acc W : Array β), forIn xs acc F = .ok W →
      W.toList.map name = acc.toList.map name ++ xs.filterMap sel
  | [], acc, W, h => by
    simp only [List.forIn_nil] at h
    cases h
    simp
  | x :: xs, acc, W, h => by
    simp only [List.forIn_cons] at h
    cases hx : F x acc with
    | error e => rw [hx] at h; cases h
    | ok r =>
      rw [hx] at h
      rcases hF x acc r hx with ⟨hs, rfl⟩ | ⟨v, hs, rfl⟩
      · have := forIn_names hF xs acc W h
        rw [this, List.filterMap_cons, hs]
      · have := forIn_names hF xs (acc.push v) W h
        rw [this, List.filterMap_cons, hs]
        simp

/-- **The function exports `coreIface` reads are the module's, by name, in order.** -/
theorem coreIface_exports {m : Silmaril.Wasm.Module} {n : List (String × String)}
    {i e : CoreIface} (h : coreIface m = .ok (n, i, e)) :
    e.map (·.1) = Silmaril.Wasm.Component.Reference.funcExportNames m := by
  unfold coreIface at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i W hW
      cases h
      have := forIn_names (name := (·.1))
        (sel := fun (x : Silmaril.Wasm.Export) => match x.index with
          | .func _ => some x.name
          | _ => none) ?_ _ _ _ hW
      · rw [List.toList_toArray] at this
        rw [this]
        simp only [List.map_nil, List.nil_append,
          Silmaril.Wasm.Component.Reference.funcExportNames]
        congr 1
      · intro x acc r hr
        rcases x with ⟨nm, idx⟩
        cases idx with
        | func f =>
          simp only at hr
          split at hr
          · split at hr
            · cases hr
            · cases hr; exact .inr ⟨_, rfl, rfl⟩
          · cases hr
        | _ => cases hr; exact .inl ⟨rfl, rfl⟩

/-- A module without imports has no imports in the interface `coreIface` reads. -/
theorem coreIface_imports {m : Silmaril.Wasm.Module} {n : List (String × String)}
    {i e : CoreIface} (h : coreIface m = .ok (n, i, e)) (himp : m.imports = []) : i = [] := by
  unfold coreIface at h
  simp only [bind, Except.bind, himp] at h
  split at h
  · cases h
  · rename_i v hv
    split at h
    · cases h
    · cases h
      simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at hv
      rw [← hv]

/-! ## The export lookup of the IR -/

theorem mapM_some_of_forall {α β : Type} {F : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, ∃ y, F x = some y) → ∃ r, l.mapM F = some r
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a List.mem_cons_self
    obtain ⟨r, hr⟩ := mapM_some_of_forall (l := l) fun x hx => h x (List.mem_cons_of_mem _ hx)
    exact ⟨b :: r, by simp [hb, hr]⟩

/-- **The IR's export lookup succeeds whenever preparation does**, for the interface
`coreIface` reads. -/
theorem exportAddrs_some (P : Silmaril.Wasm.Numerics.Profile) {m : Silmaril.Wasm.Module}
    {exps : CoreIface} {s' : Store Nat} {mi : ModuleInst} {st : Option Nat}
    (hp : Silmaril.Wasm.Component.Engine.Core3.prepareE? ({} : Store Nat) m [] = some (s', mi, st))
    (hn : Silmaril.Wasm.Component.Reference.funcExportNames m = exps.map (·.1)) :
    ∃ addrs, Param.exportAddrs (Silmaril.Wasm.Component.Reference.core3P P) mi exps =
      some addrs := by
  obtain ⟨mt, f', st₀, hv, -, hi, rfl, -⟩ :=
    Silmaril.Wasm.Component.Engine.Core3.Typed.prepareE?_inv hp
  refine mapM_some_of_forall fun x hx => ?_
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  have hl := lookup_funcExport_gen hn hv hi rfl (k := k) (n := exps[k].1) (ft := exps[k].2)
    (by simp [hk])
  exact ⟨_, by
    show ((f'.module.exports.map fun x => (x.name, x.addr)).lookup exps[k].1).bind _ = _
    rw [hl]
    rfl⟩

/-! ## A quiet failure of the node -/

section Fail

variable {o : GrowOracle}

theorem internalP_profileR {H : Type} :
    Silmaril.Wasm.Game.InternalP (H := H) (profile o) = Internal o := by
  funext x y
  rcases x with ⟨s, t⟩
  rcases y with ⟨s', t'⟩
  rfl

theorem code_of_statusP_trap {H : Type} {s : Store H} {t : Silmaril.Wasm.SingleThreaded.Thread}
    (h : Silmaril.Wasm.Game.statusP (profile o) s t = .returned .trap) :
    (t.config s).code = [.trap] ∨ ∃ a, (t.config s).code = throwing a := by
  by_cases h₂ : (t.config s).code = [.trap]
  · exact .inl h₂
  by_cases h₃ : ∃ a, (t.config s).code = throwing a
  · exact .inr h₃
  exfalso
  unfold Silmaril.Wasm.Game.statusP at h
  simp only at h
  split_ifs at h <;> first | cases h | (split at h <;> cases h)

theorem flatStatus_trap {H : Type} {st : Silmaril.Wasm.SingleThreaded.Status H}
    (h : Silmaril.Wasm.Component.Reference.flatStatus st = .returned .trap) :
    st = .returned .trap := by
  rcases st with _ | ⟨_ | _⟩ | _ | _ <;> simp [Silmaril.Wasm.Component.Reference.flatStatus] at h
  · split at h <;> cases h
  · rfl
  · split at h <;> cases h

/-- **A quiet failure of a node whose module has no imports**: its preparation in the empty store
fails, or it reports a start function whose run traps. -/
theorem nodeFail_cases {m : Silmaril.Wasm.Module} {exps : CoreIface}
    {ys : List (Σ _ : (sigN ([] : CoreIface).length).Op, Option Payload)}
    (hn : Silmaril.Wasm.Component.Reference.funcExportNames m = exps.map (·.1))
    (h : EngineInst (Silmaril.Wasm.Component.Reference.core3P (profile o))
      (Param.instOfI (Silmaril.Wasm.Component.Reference.core3P (profile o)) m [] exps) [] ys
      (.fail ())) :
    Silmaril.Wasm.Component.Engine.Core3.prepareE? ({} : Store Nat) m [] = none ∨
      ∃ s' mi a c, Silmaril.Wasm.Component.Engine.Core3.prepareE? ({} : Store Nat) m [] =
          some (s', mi, some a) ∧
        Relation.ReflTransGen (Internal o) (s', Silmaril.Wasm.SingleThreaded.Thread.invoke a []) c ∧
        status o c.1 c.2 = .returned .trap := by
  have hprep : (Silmaril.Wasm.Component.Reference.core3P (profile o)).prepare?
      ((Silmaril.Wasm.Component.Reference.core3P (profile o)).empty Nat) m [] =
      Silmaril.Wasm.Component.Engine.Core3.prepareE? ({} : Store Nat) m [] := rfl
  rcases h with ⟨hnone, -⟩ | ⟨J, f, c', hJ, hs, hr, hst⟩
  · left
    simp only [Param.instOfI, Param.allocHosts, List.map_nil, hprep] at hnone
    cases hp : Silmaril.Wasm.Component.Engine.Core3.prepareE? ({} : Store Nat) m [] with
    | none => rfl
    | some p =>
      obtain ⟨s', mi, st⟩ := p
      rw [hp] at hnone
      obtain ⟨addrs, ha⟩ := exportAddrs_some (profile o) hp hn
      simp only [ha, Option.map_some] at hnone
      cases hnone
  · right
    simp only [Param.instOfI, Param.allocHosts, List.map_nil, hprep] at hJ
    cases hp : Silmaril.Wasm.Component.Engine.Core3.prepareE? ({} : Store Nat) m [] with
    | none => rw [hp] at hJ; cases hJ
    | some p =>
      obtain ⟨s', mi, st⟩ := p
      rw [hp] at hJ
      dsimp only at hJ
      obtain ⟨addrs, -, rfl⟩ := Option.map_eq_some_iff.mp hJ
      cases hs
      refine ⟨s', mi, f, c', rfl, ?_, ?_⟩
      · cases hr with
        | nil run =>
          have e : @Engine.CoreEngine.Internal (Silmaril.Wasm.Component.Reference.core3P (profile o)) Nat =
              Internal o := internalP_profileR
          unfold Engine.CoreEngine.Steps at run
          rw [e] at run
          exact run
        | call _ _ hh => exact absurd hh (Nat.not_lt_zero _)
      · exact status_trap_of_code (code_of_statusP_trap (flatStatus_trap hst))

end Fail

end Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore
