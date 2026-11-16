module

public import Silmaril.Sim.X86.GModule.Defs

/-!
# The G simulator as an instantiated module: what is proved (header, proofs inline)

PROVED (kernel evaluation by `decide` for the facts about the concrete instantiation; no native
evaluation):

* `simInit_isSome`, `f₀_globals` (`[0, …, 22]`), `s₀_globals_length`, `f₀_s₀`: instantiation
  succeeds, and `s₀`, `f₀` are its store and frame;
* `exportExternAddr_loc`: the export named `locName i` is the global at address `i`;
* **`gval_eq_export`**: for every store `s` (of any host type), the simulator's view of a
  location (`gval s f₀ l`, the abstraction `Enc` is stated with) is the value an embedder reads
  through the location's exported global;
* `enc_congr`: `Enc` depends only on the global values and the instance's global addresses;
* **`enc_loadStore`** (loading): every x86 state `σ` is encoded by `loadStore σ`, which is the
  instantiated store `s₀` with only the global values changed (`loadStore_funcs`, …,
  `loadStore_globalTypes`: the same global types, so it is reachable by `global.set` on the
  exported mutable globals).
-/

@[expose] public section

namespace Silmaril.Sim.X86.GModule

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Sim.X86.G

theorem simInit_isSome : simInit.isSome = true := by decide

theorem f₀_globals : f₀.module.globals = List.range 23 := by decide

theorem s₀_globals_length : s₀.globals.length = 23 := by decide

/-- `s₀`, `f₀` are the instantiation's store and frame. -/
theorem f₀_s₀ : ∃ st, simInit = some (s₀, f₀, st) := by
  cases h : simInit with
  | none => have := simInit_isSome; rw [h] at this; cases this
  | some r => exact ⟨r.2.2, by simp [s₀, f₀, h]⟩

theorem exportExternAddr_loc : ∀ i : Fin 23, exportExternAddr? f₀.module (locName i) = some (.global i) := by
  decide

/-- **The view is the exported-global read.** -/
theorem gval_eq_export {H : Type} (s : Store H) (l : Loc) :
    gval s f₀ l = exportGlobalVal s f₀.module (locName l.idx) := by
  rw [gval_eq, f₀_globals, List.getElem?_range l.idx_lt, Option.bind_some]
  unfold exportGlobalVal
  rw [exportExternAddr_loc ⟨l.idx, l.idx_lt⟩]

/-- `Enc` depends only on the global values and the instance's global addresses. -/
theorem enc_congr {H H' : Type} {s : Store H} {s' : Store H'} {f f' : Frame}
    {σ : Silmaril.X86.State} (hs : s'.globals = s.globals)
    (hf : f'.module.globals = f.module.globals) (h : Enc s f σ) : Enc s' f' σ := by
  have hg : ∀ l, gval s' f' l = gval s f l := fun l => by rw [gval_eq, gval_eq, hs, hf]
  obtain ⟨⟨ha, hi⟩, hr, hrip, h1, h2, h3, h4⟩ := h
  refine ⟨⟨fun l => ?_, fun l₁ l₂ a => ?_⟩, ?_⟩
  · obtain ⟨a, h₁, h₂⟩ := ha l
    exact ⟨a, hf ▸ h₁, hs ▸ h₂⟩
  · rw [hf]; exact hi l₁ l₂ a
  · simp only [hg]
    exact ⟨hr, hrip, h1, h2, h3, h4⟩

/-- **Loading**: the instantiated store, with the location globals set, encodes `σ`. -/
theorem enc_loadStore (σ : Silmaril.X86.State) : Enc (loadStore σ) f₀ σ :=
  enc_congr (s := encStore (H := Nat) σ) (f := encFrame) rfl (by rw [f₀_globals]; rfl)
    (enc_encStore σ)

theorem loadStore_funcs (σ : Silmaril.X86.State) : (loadStore σ).funcs = s₀.funcs := rfl

theorem loadStore_mems (σ : Silmaril.X86.State) : (loadStore σ).mems = s₀.mems := rfl

/-- The loaded store has the instantiated store's global types: only values changed. -/
theorem loadStore_globalTypes (σ : Silmaril.X86.State) :
    (loadStore σ).globals.map (·.type) = s₀.globals.map (·.type) := by
  have h : s₀.globals.map (·.type) = List.replicate 23 ⟨.var, .num (.int .i64)⟩ := by decide
  rw [h]
  simp [loadStore, encStore]

end Silmaril.Sim.X86.GModule

/-! Old names (module `Silmaril.Sim.Wasm.X86G`). -/

namespace Silmaril.Sim.Wasm.X86G

@[deprecated Silmaril.Sim.X86.GModule.simInit_isSome (since := "2026-11-10")]
alias simInit_isSome := Silmaril.Sim.X86.GModule.simInit_isSome
@[deprecated Silmaril.Sim.X86.GModule.f₀_globals (since := "2026-11-10")]
alias f₀_globals := Silmaril.Sim.X86.GModule.f₀_globals
@[deprecated Silmaril.Sim.X86.GModule.s₀_globals_length (since := "2026-11-10")]
alias s₀_globals_length := Silmaril.Sim.X86.GModule.s₀_globals_length
@[deprecated Silmaril.Sim.X86.GModule.f₀_s₀ (since := "2026-11-10")]
alias f₀_s₀ := Silmaril.Sim.X86.GModule.f₀_s₀
@[deprecated Silmaril.Sim.X86.GModule.gval_eq_export (since := "2026-11-10")]
alias gval_eq_export := Silmaril.Sim.X86.GModule.gval_eq_export
@[deprecated Silmaril.Sim.X86.GModule.enc_congr (since := "2026-11-10")]
alias enc_congr := Silmaril.Sim.X86.GModule.enc_congr
@[deprecated Silmaril.Sim.X86.GModule.enc_loadStore (since := "2026-11-10")]
alias enc_loadStore := Silmaril.Sim.X86.GModule.enc_loadStore
@[deprecated Silmaril.Sim.X86.GModule.loadStore_funcs (since := "2026-11-10")]
alias loadStore_funcs := Silmaril.Sim.X86.GModule.loadStore_funcs
@[deprecated Silmaril.Sim.X86.GModule.loadStore_mems (since := "2026-11-10")]
alias loadStore_mems := Silmaril.Sim.X86.GModule.loadStore_mems
@[deprecated Silmaril.Sim.X86.GModule.loadStore_globalTypes (since := "2026-11-10")]
alias loadStore_globalTypes := Silmaril.Sim.X86.GModule.loadStore_globalTypes
@[deprecated Silmaril.Sim.X86.GModule.exportExternAddr_loc (since := "2026-11-10")]
alias exportAddr_loc := Silmaril.Sim.X86.GModule.exportExternAddr_loc

end Silmaril.Sim.Wasm.X86G

end
