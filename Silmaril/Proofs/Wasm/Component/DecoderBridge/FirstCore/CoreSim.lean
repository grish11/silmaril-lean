module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore.CoreRun
public import Silmaril.Proofs.Wasm.Component.Reference.SplitInit
public import Silmaril.Proofs.Wasm.Component.Reference.SplitBack
public import Silmaril.Proofs.Wasm.Component.Reference.HostMap
public import Silmaril.Proofs.Wasm.Component.Reference.StartBase
public import Silmaril.Wasm.Component.Reference.Engine.Core3.Typed.Prepare.Defs

/-!
# The first core instantiation in the shared core store, from the engine's own run

The IR instantiates a decoded module `m` alone (`Param.instOfI`, in the empty store at host
type `Nat`); the reference machine instantiates it in the core store `s₀` its earlier
definitions built (host functions of `canon lower`, at host type `CanonHost`). For a module
without imports, data or element segments:

* `prepareE_shift`: the reference preparation is the IR's, its store mapped to the host type of
  the machine (`Store.mapH`) and relocated past `s₀` (`CoreShift.reloc`), its module instance and
  start function shifted (`instantiateOnce?_mapH`, `instantiateOnce?_reloc`);
* `startTrap_shift`: a run of the start function of the IR's instance (`Internal o`, any
  number of steps) to a trap, for a module in the split fragment, is matched by the interpreter
  run (`runC (stepI o)`) of the shifted start function in the relocated store, typed when `s₀`
  is (`steps_shift`, `Steps.mapH`, `runCI_complete`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SingleThreaded (GrowOracle Internal status statusC internalC runC)
open Silmaril.Wasm.SingleThreaded.Exec (stepI)

variable {H : Type}

/-! ## Preparation in the shared store -/

theorem reloc_emptyR (s₀ : Store H) : reloc s₀ ({} : Store H) = s₀ := by
  obtain ⟨⟩ := s₀
  simp [reloc, Store.app, Shift.store]

theorem externAddrsOk_nil {H' : Type} (s : Store H) (s' : Store H')
    (ts : List Silmaril.Wasm.Validation.CExternType) :
    externAddrsOk? s [] ts = externAddrsOk? s' [] ts := by
  cases ts <;> rfl

theorem instantiateOnce_shift (g : Nat → H) (s₀ : Store H) {m : Silmaril.Wasm.Module}
    (hseg : m.data = [] ∧ m.elems = []) :
    instantiateOnce? s₀ m [] = (instantiateOnce? ({} : Store Nat) m []).map
      (fun p => (reloc s₀ (Store.mapH g p.1), (sh s₀).frame p.2.1, p.2.2)) := by
  have h₁ := instantiateOnce?_reloc s₀ ({} : Store H) m [] hseg
  rw [reloc_emptyR, List.map_nil] at h₁
  rw [h₁]
  have h₂ := instantiateOnce?_mapH g ({} : Store Nat) m []
  rw [empty_mapH] at h₂
  rw [h₂]
  cases instantiateOnce? ({} : Store Nat) m [] with
  | none => rfl
  | some p => rfl

/-- **Preparation in the shared store is the preparation alone, shifted.** -/
theorem prepareE_shift (g : Nat → H) (s₀ : Store H) {m : Silmaril.Wasm.Module}
    (hseg : m.data = [] ∧ m.elems = []) :
    Silmaril.Wasm.Component.Engine.Core3.prepareE? s₀ m [] =
      (Silmaril.Wasm.Component.Engine.Core3.prepareE? ({} : Store Nat) m []).map
        (fun p => (reloc s₀ (Store.mapH g p.1), (sh s₀).minst p.2.1,
          p.2.2.map (s₀.funcs.length + ·))) := by
  unfold Silmaril.Wasm.Component.Engine.Core3.prepareE?
  cases Silmaril.Wasm.Validation.validate? m with
  | none => rfl
  | some mt =>
    dsimp only
    rw [externAddrsOk_nil s₀ ({} : Store Nat)]
    split_ifs
    · rw [instantiateOnce_shift g s₀ hseg]
      cases instantiateOnce? ({} : Store Nat) m [] with
      | none => rfl
      | some p =>
        obtain ⟨s', f', st⟩ := p
        cases st with
        | none => rfl
        | some x =>
          simp only [Option.map_some]
          show (((sh s₀).minst f'.module).funcs[x.toNat]?).map _ = _
          simp only [Shift.minst, List.getElem?_map, sh_fn]
          cases f'.module.funcs[x.toNat]? <;> rfl
    · rfl

/-! ## Runs -/

section Runs

variable {o : GrowOracle}

/-- Internal steps are host-free Core steps of the threads' configurations. -/
theorem steps_of_internal {x y : Store H × Silmaril.Wasm.SingleThreaded.Thread}
    (h : Relation.ReflTransGen (Internal o) x y) :
    Relation.ReflTransGen (Step (Silmaril.Wasm.SingleThreaded.profile o) (fun _ _ _ _ => False))
      (x.2.config x.1) (y.2.config y.1) := by
  induction h with
  | refl => exact .refl
  | @tail b c _ hst ih =>
    obtain ⟨s, t⟩ := b
    obtain ⟨s', t'⟩ := c
    obtain ⟨f', code', rfl, hs⟩ := hst
    exact ih.tail hs

/-- Host-free Core steps from a thread's configuration are internal steps of the thread. -/
theorem internal_of_steps {s : Store H} {t : Silmaril.Wasm.SingleThreaded.Thread} {d : Config H}
    (h : Relation.ReflTransGen
      (Step (Silmaril.Wasm.SingleThreaded.profile o) (fun _ _ _ _ => False)) (t.config s) d) :
    ∃ t', Relation.ReflTransGen (Internal o) (s, t) (d.store, t') ∧ t'.config d.store = d := by
  induction h with
  | refl => exact ⟨t, by rw [Silmaril.Wasm.SingleThreaded.Thread.config_store], by
      rw [Silmaril.Wasm.SingleThreaded.Thread.config_store]⟩
  | @tail d e _ hst ih =>
    obtain ⟨t', hr, ht'⟩ := ih
    refine ⟨.active e.frame e.code, hr.tail ⟨e.frame, e.code, rfl, ?_⟩, rfl⟩
    rw [ht']
    exact hst

/-- The relocated invocation is the invocation of the shifted function. -/
theorem shC_invoke (s₀ u : Store H) {a : Nat} (ha : a < u.funcs.length) :
    shC s₀ (invoke u a []) = invoke (reloc s₀ u) (s₀.funcs.length + a) [] := by
  obtain ⟨fi, hfi⟩ : ∃ fi, u.funcs[a]? = some fi := getElem?_of_lt' ha
  have hr : (reloc s₀ u).funcs[s₀.funcs.length + a]? = some ((sh s₀).finst fi) := by
    rw [funcs_reloc, hfi]
    rfl
  simp only [shC, invoke, hfi, hr, Option.map_some, Option.getD_some, vals, List.map_nil,
    List.nil_append]
  simp [Shift.ref, Shift.finst]
  rfl

/-- A status `returned trap` is a trap or a throw. -/
theorem code_of_status_trap {s : Store H} {t : Silmaril.Wasm.SingleThreaded.Thread}
    (h : status o s t = .returned .trap) :
    (t.config s).code = [.trap] ∨ ∃ a, (t.config s).code = throwing a := by
  by_cases h₂ : (t.config s).code = [.trap]
  · exact .inl h₂
  by_cases h₃ : ∃ a, (t.config s).code = throwing a
  · exact .inr h₃
  exfalso
  unfold status at h
  simp only at h
  split_ifs at h <;> first | cases h | (split at h <;> cases h)

theorem toAdmin_ne_trap (v : Val) : v.toAdmin ≠ .trap := by
  rcases v with ⟨⟨_ | _⟩, b⟩ | b | r <;> simp [Val.toAdmin]

theorem toAdmin_ne_throwRef (v : Val) : v.toAdmin ≠ .plain .throwRef := by
  rcases v with ⟨⟨_ | _⟩, b⟩ | b | r <;> simp [Val.toAdmin]

/-- A thread whose code is a trap or a throw has the status `returned trap`. -/
theorem status_trap_of_code {s : Store H} {t : Silmaril.Wasm.SingleThreaded.Thread}
    (h : (t.config s).code = [.trap] ∨ ∃ a, (t.config s).code = throwing a) :
    status o s t = .returned .trap := by
  unfold status
  simp only
  rcases h with h | ⟨a, h⟩
  · have hv : ¬ ∃ vs, (t.config s).code = vals vs := fun ⟨vs, hv⟩ => by
      have hm : Admin.trap ∈ vals vs := by rw [← hv, h]; simp
      obtain ⟨w, -, hw⟩ := List.mem_map.mp hm
      exact toAdmin_ne_trap w hw
    split_ifs
    rfl
  · have hv : ¬ ∃ vs, (t.config s).code = vals vs := fun ⟨vs, hv⟩ => by
      have hm : Admin.plain .throwRef ∈ vals vs := by rw [← hv, h]; simp [throwing]
      obtain ⟨w, -, hw⟩ := List.mem_map.mp hm
      exact toAdmin_ne_throwRef w hw
    have ht : ¬ (t.config s).code = [.trap] := by rw [h]; nofun
    have hx : ∃ a, (t.config s).code = throwing a := ⟨a, h⟩
    split_ifs
    rfl

theorem code_shift_trap (δ : Shift) {code : List Admin}
    (h : code = [.trap] ∨ ∃ a, code = throwing a) :
    δ.code code = [.trap] ∨ ∃ a, δ.code code = throwing a := by
  rcases h with rfl | ⟨a, rfl⟩
  · left; simp
  · right; exact ⟨δ.ex + a, by simp [Shift.ref, throwing]⟩

/-- **The start function's trap, in the shared store**: a run of the start function of the
module's instance alone to a trap is matched by an interpreter run of the shifted start function
in the relocated store to a trap. -/
theorem startTrap_shift (g : Nat → H) (s₀ : Store H) (hs₀ : StoreOk s₀)
    {m : Silmaril.Wasm.Module} (himp : m.imports = [])
    (hsplit : Silmaril.Wasm.Component.DecoderBridge.splitMod m = true) {s' : Store Nat}
    {mi : ModuleInst} {a : Nat}
    (hp : Silmaril.Wasm.Component.Engine.Core3.prepareE? ({} : Store Nat) m [] = some (s', mi, some a))
    {c : Store Nat × Silmaril.Wasm.SingleThreaded.Thread}
    (hrun : Relation.ReflTransGen (Internal o) (s', Silmaril.Wasm.SingleThreaded.Thread.invoke a []) c)
    (hst : status o c.1 c.2 = .returned .trap) :
    ∃ n s'' t'', runC (stepI o) n (reloc s₀ (Store.mapH g s'))
        (Silmaril.Wasm.SingleThreaded.Thread.invoke (s₀.funcs.length + a) []) =
          (s'', t'', .returned .trap) ∧ statusC (stepI o) s'' t'' = .returned .trap := by
  simp only [Silmaril.Wasm.Component.DecoderBridge.splitMod, Bool.and_eq_true,
    List.isEmpty_iff] at hsplit
  obtain ⟨⟨⟨⟨htags, hmems⟩, htabs⟩, hdata⟩, helems⟩ := hsplit
  obtain ⟨mt, f', st₀, hv, -, hi, rfl, hst₀⟩ :=
    Silmaril.Wasm.Component.Engine.Core3.Typed.prepareE?_inv hp
  obtain ⟨x, rfl, hx⟩ := hst₀ a rfl
  -- the store of the instance alone is good, and the start function is one of its functions
  have hi' : instantiateOnce? ({} : Store Nat) { m with start := none }
      (Silmaril.Wasm.Link.GC.Preparation.imports []) = some (s', f', none) := by
    rw [instantiateOnce?_noStart, show Silmaril.Wasm.Link.GC.Preparation.imports [] = [] from rfl,
      hi]
    rfl
  have hprof : Silmaril.Wasm.Link.GC.inProfile { m with start := none } = true := by
    simp [Silmaril.Wasm.Link.GC.inProfile, htags, hmems, htabs, hdata, helems, himp]
  obtain ⟨hgood, hmod⟩ := storeGood_once hprof hi' (fun _ h => by cases h) rfl rfl rfl
    (fun _ h => by cases h)
  have ha : a < s'.funcs.length := hmod.funcs a (List.mem_of_getElem? hx)
  have hgood' : StoreGood (Store.mapH g s') := (storeGood_mapH_iff g s').mpr hgood
  have ha' : a < (Store.mapH g s').funcs.length := by simpa using ha
  -- the run alone, at host type `H`, relocated
  have h₁ := steps_of_internal hrun
  have h₂ := Steps.mapH (P := Silmaril.Wasm.SingleThreaded.profile o) g h₁
  have hc₀ : Config.mapH g ((Silmaril.Wasm.SingleThreaded.Thread.invoke a []).config s') =
      invoke (Store.mapH g s') a [] := invoke_mapH g s' a []
  rw [hc₀] at h₂
  obtain ⟨h₃, -⟩ := steps_shift s₀ h₂ (splitGood_invoke hgood' ha' (fun _ h => by cases h))
  rw [shC_invoke s₀ _ ha'] at h₃
  -- back to threads, in the shared store
  have h₃' : Relation.ReflTransGen
      (Step (Silmaril.Wasm.SingleThreaded.profile o) (fun _ _ _ _ => False))
      ((Silmaril.Wasm.SingleThreaded.Thread.invoke (s₀.funcs.length + a) []).config
        (reloc s₀ (Store.mapH g s')))
      (shC s₀ (Config.mapH g (c.2.config c.1))) := h₃
  obtain ⟨t', hr, ht'⟩ := internal_of_steps h₃'
  -- the final status
  have hcode := code_of_status_trap hst
  have hst' : status o (shC s₀ (Config.mapH g (c.2.config c.1))).store t' = .returned .trap := by
    refine status_trap_of_code ?_
    rw [ht']
    exact code_shift_trap (sh s₀) hcode
  -- typing of the shared invocation
  have hp' := prepareE_shift g s₀ (m := m) ⟨hdata, helems⟩
  rw [hp] at hp'
  obtain ⟨-, -, -, hcfg⟩ :=
    Silmaril.Wasm.Component.Engine.Core3.Typed.prepareE?_typed hs₀ hp'
  have hok : ConfigOk ((Silmaril.Wasm.SingleThreaded.Thread.invoke (s₀.funcs.length + a) []).config
      (reloc s₀ (Store.mapH g s'))) [] := hcfg _ rfl
  obtain ⟨n, hn⟩ := runCI_complete (I := fun c => ConfigOk c [])
    Silmaril.Wasm.SingleThreaded.Exec.typedInv' hok hr (by rw [hst']; nofun)
  rw [hst'] at hn
  refine ⟨n, _, _, hn, ?_⟩
  obtain ⟨-, hok', -⟩ := Silmaril.Wasm.SingleThreaded.Exec.runCI_sound_typed n _ _ hok hn
  rw [Silmaril.Wasm.SingleThreaded.Exec.statusI_eq_typed hok']
  exact hst'

end Runs

end Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore
