module

public import Silmaril.Proofs.Wasm.Component.Reference.Adequacy.WitnessInst
public import Silmaril.Proofs.Wasm.Component.Core3G.Sim
public import Silmaril.Wasm.Game.Machine.Thms

/-!
# The trap witnesses: core runs and their uniqueness

* `set_reach`, `get_reach`, `zero_reach`: the export calls of the witnesses as host-free thread
  runs to a result, for every profile;
* `result_unique`: at a deterministic profile `profile o`, a host-free run to a result is
  unique (`reach_normal_unique`), so these are the only runs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.Adequacy

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Game
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)

open Silmaril.Proofs.Wasm.Component.Reference.Litmus (steps_frame_label)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread
local notation "CVal" => Silmaril.Wasm.Execution.Core.Val

/-! ## Reading the bodies -/

theorem isSet_code {fi : FuncInst Nat} (h : isSet fi = true) :
    ∃ (code : Silmaril.Wasm.Func) (x : Silmaril.Wasm.GlobalIdx), fi.code = .wasm code ∧
      code.locals = [] ∧ code.body = [.intConst .i32 1, .globalSet x, .intConst .i32 0] ∧
      x.toNat = 0 := by
  unfold isSet at h
  split at h
  next t a x b hc =>
    have h' : (a = 1 ∧ x.toNat = 0) ∧ b = 0 := by
      simpa only [Bool.and_eq_true, beq_iff_eq] using h
    obtain ⟨⟨rfl, hx⟩, rfl⟩ := h'
    exact ⟨_, x, hc, rfl, rfl, hx⟩
  next => cases h

theorem isGet_code {fi : FuncInst Nat} (h : isGet fi = true) :
    ∃ (code : Silmaril.Wasm.Func) (x : Silmaril.Wasm.GlobalIdx), fi.code = .wasm code ∧
      code.locals = [] ∧ code.body = [.globalGet x] ∧ x.toNat = 0 := by
  unfold isGet at h
  split at h
  next t x hc =>
    have hx : x.toNat = 0 := by simpa only [beq_iff_eq] using h
    exact ⟨_, x, hc, rfl, rfl, hx⟩
  next => cases h

theorem isZero_code {fi : FuncInst Nat} (h : isZero fi = true) :
    ∃ code : Silmaril.Wasm.Func, fi.code = .wasm code ∧ code.locals = [] ∧
      code.body = [.intConst .i32 0] := by
  unfold isZero at h
  split at h
  next t a hc =>
    have ha : a = 0 := by simpa only [beq_iff_eq] using h
    subst ha
    exact ⟨_, hc, rfl, rfl⟩
  next => cases h

/-! ## Runs -/

/-- A Core run from a thread's configuration, after one step, is a host-free thread run. -/
theorem reach_of_steps {P : Profile} {s : Store Nat} {t : STh} {c₁ c' : Config Nat}
    (h₁ : Step P Silmaril.Wasm.SingleThreaded.Det.noHost (t.config s) c₁)
    (h : Steps P Silmaril.Wasm.SingleThreaded.Det.noHost c₁ c') :
    Reach P (s, t) (c'.store, .active c'.frame c'.code) := by
  refine Relation.ReflTransGen.head (b := (c₁.store, .active c₁.frame c₁.code))
    ⟨c₁.frame, c₁.code, rfl, h₁⟩ ?_
  clear h₁
  induction h with
  | refl => exact .refl
  | tail _ st ih => exact ih.tail ⟨_, _, rfl, st⟩

/-- **A call of a function `[] → [i32]` without locals**, whose body runs to one value. -/
theorem call_reach {P : Profile} {s s' : Store Nat} {a : Nat} {fi : FuncInst Nat}
    {code : Silmaril.Wasm.Func} {v : CVal} (hf : s.funcs[a]? = some fi)
    (hty : FnType.ofDefType? fi.type = some fnI32) (hcode : fi.code = .wasm code)
    (hbody : Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
      ⟨s, Frame.forCall fi.module [] code.locals, expression code.body⟩
      ⟨s', Frame.forCall fi.module [] code.locals, vals [v]⟩) :
    Reach P (s, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a [])
      (s', .active {} (vals [v])) := by
  have he : Expand fi.type fnI32.toComp := FnType.expand_of_ofDefType? hty
  let F := Frame.forCall fi.module [] code.locals
  let n := (Ty.ofList (fnI32.results.map ScalarType.toC)).length
  have hn : [v].length = n := (Ty.length_ofList (fnI32.results.map ScalarType.toC)).symm
  have s₁ : Step P Silmaril.Wasm.SingleThreaded.Det.noHost (invoke s a [])
      ⟨s, {}, [.frame n F [.label n [] (expression code.body)]]⟩ :=
    .callRefFunc trivial hf he (Ty.length_ofList (fnI32.params.map ScalarType.toC)).symm hcode
  have s₃ : Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
      ⟨s, {}, [.frame n F [.label n [] (expression code.body)]]⟩
      ⟨s', {}, [.frame n F [.label n [] (vals [v])]]⟩ :=
    steps_frame_label hbody
  have s₄ : Step P Silmaril.Wasm.SingleThreaded.Det.noHost
      ⟨s', {}, [.frame n F [.label n [] (vals [v])]]⟩ ⟨s', {}, [.frame n F (vals [v])]⟩ :=
    .ctxtFrame .labelVals
  have s₅ : Step P Silmaril.Wasm.SingleThreaded.Det.noHost
      ⟨s', {}, [.frame n F (vals [v])]⟩ ⟨s', {}, vals [v]⟩ :=
    .frameVals hn
  exact reach_of_steps s₁ ((s₃.tail s₄).tail s₅)

/-- The store after `poke` on the instance of `pokePeekCore`: the global set to `1`. -/
def ppStore₁ : Store Nat := ppStore.setGlobal 0 (Silmaril.Wasm.Execution.Core.Val.i32 1)

/-- **`set`, from the instance's store**: returns `0` and sets the global to `1`. -/
theorem set_reach {P : Profile} :
    Reach P (ppStore, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat 0 [])
      (ppStore₁, .active {} (vals [Silmaril.Wasm.Execution.Core.Val.i32 0])) := by
  obtain ⟨-, -, ⟨fi₀, fi₁, hfuncs, hty₀, -, hset, -, hg₀, -⟩, ⟨g, hglob, -⟩⟩ := ppFacts
  obtain ⟨code, x, hcode, hloc, hbody, hx⟩ := isSet_code hset
  have hf : ppStore.funcs[0]? = some fi₀ := by rw [hfuncs]; rfl
  refine call_reach hf hty₀ hcode ?_
  let F := Frame.forCall fi₀.module [] code.locals
  have hglobal : ppStore.global? F x = some (0, g) := by
    simp [Store.global?, F, Frame.forCall, hg₀, hx, hglob]
  rw [hbody]
  have a₁ : Step P Silmaril.Wasm.SingleThreaded.Det.noHost
      ⟨ppStore, F, vals [] ++ [(Silmaril.Wasm.Execution.Core.Val.i32 1).toAdmin, .plain (.globalSet x)] ++
        [.plain (.intConst .i32 0)]⟩
      ⟨ppStore.setGlobal 0 (Silmaril.Wasm.Execution.Core.Val.i32 1), F, vals [] ++ [] ++ [.plain (.intConst .i32 0)]⟩ :=
    .ctxtInstrs (.variable (.globalSet hglobal)) (.inr (by simp))
  exact Relation.ReflTransGen.single a₁

/-- **`get`, at a store with the instance's functions**: returns the global. -/
theorem get_reach {P : Profile} {s : Store Nat} (hs : s.funcs = ppStore.funcs) {g : GlobalInst}
    (hglob : s.globals[0]? = some g) :
    Reach P (s, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat 1 [])
      (s, .active {} (vals [g.value])) := by
  obtain ⟨-, -, ⟨fi₀, fi₁, hfuncs, -, hty₁, -, hget, -, hg₁⟩, -⟩ := ppFacts
  obtain ⟨code, x, hcode, hloc, hbody, hx⟩ := isGet_code hget
  have hf : s.funcs[1]? = some fi₁ := by rw [hs, hfuncs]; rfl
  refine call_reach hf hty₁ hcode ?_
  let F := Frame.forCall fi₁.module [] code.locals
  have hglobal : s.global? F x = some (0, g) := by
    simp [Store.global?, F, Frame.forCall, hg₁, hx, hglob]
  rw [hbody]
  exact Relation.ReflTransGen.single (.variable (.globalGet hglobal))

/-- **`f` of `zeroCore`, at a store with the instance's functions**: returns `0`. -/
theorem zero_reach {P : Profile} {s : Store Nat} (hs : s.funcs = zStore.funcs) :
    Reach P (s, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat 0 [])
      (s, .active {} (vals [Silmaril.Wasm.Execution.Core.Val.i32 0])) := by
  obtain ⟨-, -, ⟨fi, hfuncs, hty, hz⟩⟩ := zFacts
  obtain ⟨code, hcode, hloc, hbody⟩ := isZero_code hz
  have hf : s.funcs[0]? = some fi := by rw [hs, hfuncs]; rfl
  refine call_reach hf hty hcode ?_
  rw [hbody]
  exact .refl

theorem ppStore_global : ∃ g : GlobalInst, ppStore.globals[0]? = some g ∧ g.value = Silmaril.Wasm.Execution.Core.Val.i32 0 := by
  obtain ⟨-, -, -, ⟨g, hglob, hv⟩⟩ := ppFacts
  exact ⟨g, by rw [hglob]; rfl, hv⟩

theorem ppStore₁_global :
    ∃ g : GlobalInst, ppStore₁.globals[0]? = some g ∧ g.value = Silmaril.Wasm.Execution.Core.Val.i32 1 := by
  obtain ⟨-, -, -, ⟨g, hglob, -⟩⟩ := ppFacts
  refine ⟨{ g with value := Silmaril.Wasm.Execution.Core.Val.i32 1 }, ?_, rfl⟩
  simp [ppStore₁, Store.setGlobal, hglob]

/-! ## Uniqueness at deterministic profiles -/

theorem result_toAdmin_inj : ∀ {r r' : Result}, r.toAdmin = r'.toAdmin → r = r'
  | .values vs, .values vs', h => by
    rw [Silmaril.Wasm.SingleThreaded.vals_injective h]
  | .values vs, .trap, h => absurd ⟨vs, h.symm⟩ Silmaril.Proofs.Wasm.Component.Core3G.not_vals_trap
  | .values vs, .throw a, h =>
    absurd ⟨vs, h.symm⟩ (Silmaril.Proofs.Wasm.Component.Core3G.not_vals_throwing a)
  | .trap, .values vs, h => absurd ⟨vs, h⟩ Silmaril.Proofs.Wasm.Component.Core3G.not_vals_trap
  | .trap, .trap, _ => rfl
  | .trap, .throw a, h => by simp [Result.toAdmin] at h
  | .throw a, .values vs, h =>
    absurd ⟨vs, h⟩ (Silmaril.Proofs.Wasm.Component.Core3G.not_vals_throwing a)
  | .throw a, .trap, h => by simp [Result.toAdmin] at h
  | .throw a, .throw b, h => by simp [Result.toAdmin] at h; rw [h]

/-- **A host-free run to a result is unique** at a deterministic profile. -/
theorem result_unique {o : Silmaril.Wasm.SingleThreaded.GrowOracle} {x : Store Nat × STh}
    {s₁ s₂ : Store Nat} {t₁ t₂ : STh} {r₁ r₂ : Result}
    (h₁ : Reach (Silmaril.Wasm.SingleThreaded.profile o) x (s₁, t₁)) (f₁ : ResultAt s₁ t₁ r₁)
    (h₂ : Reach (Silmaril.Wasm.SingleThreaded.profile o) x (s₂, t₂)) (f₂ : ResultAt s₂ t₂ r₂) :
    s₂ = s₁ ∧ t₂ = t₁ ∧ r₂ = r₁ := by
  have e := reach_normal_unique h₂ h₁ (resultAt_no_internal f₂) (resultAt_no_internal f₁)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  exact ⟨rfl, rfl, result_toAdmin_inj (f₂.symm.trans f₁)⟩

end Silmaril.Proofs.Wasm.Component.Reference.Adequacy
