module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp.Core
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore.CoreSim

/-!
# The first instantiated module against its trampolines, from the engine's own run

The IR instantiates a decoded module `m` with `n` imports against fresh host functions with
codes `0, …, n - 1` (`Param.allocHosts`); for a module of the fragment those are `irStore n`,
all of core type `fFlat`. The reference machine instantiates it against `n` trampolines, all
with the same host code `h` (`lowStore n h`). The two stores differ only in host code:

* `allocHosts_ir`: the IR's store of imports is `irStore n`, its addresses `0, …, n - 1`;
* `mapH_irStore`: renaming every host code of `irStore n` to `h` gives `lowStore n h`;
* `prepareE_mapH`: preparation commutes with renaming host code (the import check reads only
  function types);
* `startTrap_low`: a run of the start function of the IR's instance (`Internal o`) to a trap is
  matched by the interpreter run (`runC (stepI o)`) of the same start function in the renamed
  store (`Steps.mapH`, `runCI_complete` along typing).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore
open Silmaril.Wasm.Component Silmaril.Wasm.Component.DecoderBridge
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SingleThreaded (GrowOracle Internal status statusC internalC runC)
open Silmaril.Wasm.SingleThreaded.Exec (stepI)

/-! ## The stores -/

/-- The IR's store of `n` imports of core type `fFlat`: host function `i` has code `i`. -/
def irStore (n : Nat) : Store Nat := { ({} : Store Nat) with funcs := (List.range n).map lowFI }

theorem allocHost_irStore (k : Nat) :
    Silmaril.Wasm.SingleThreaded.allocHost (irStore k) (Param.v1Type fFlat) k =
      (irStore (k + 1), k) := by
  simp only [Silmaril.Wasm.SingleThreaded.allocHost, Silmaril.Wasm.Execution.Core.allocFunc,
    irStore, List.length_map, List.length_range, Prod.mk.injEq, and_true]
  rw [List.range_succ, List.map_append]
  rfl

/-- **The IR's store of imports** of a module whose imports all have core type `fFlat`. -/
theorem allocHosts_ir (P : Silmaril.Wasm.Numerics.Profile) :
    ∀ (imps : CoreIface) (k : Nat), imps.all (·.2 == fFlat) = true →
      Param.allocHosts (Silmaril.Wasm.Component.Reference.core3P P) (irStore k) k imps =
        (irStore (k + imps.length), List.range' k imps.length)
  | [], k, _ => rfl
  | (nm, ft) :: imps, k, h => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    have e := allocHosts_ir P imps (k + 1) h
    have hA : (Silmaril.Wasm.Component.Reference.core3P P).allocHost (irStore k)
        (Param.v1Type fFlat) k = (irStore (k + 1), k) := allocHost_irStore k
    show (match (Silmaril.Wasm.Component.Reference.core3P P).allocHost (irStore k)
        (Param.v1Type fFlat) k with
      | (s₁, a) => match Param.allocHosts (Silmaril.Wasm.Component.Reference.core3P P) s₁
          (k + 1) imps with
        | (s₂, as) => (s₂, a :: as)) = _
    rw [hA]
    dsimp only
    rw [e]
    simp only [List.length_cons, List.range'_succ]
    congr 2
    omega

theorem irStore_zero : irStore 0 = ({} : Store Nat) := rfl

theorem mapH_irStore {H : Type} (n : Nat) (h : H) :
    Store.mapH (fun _ => h) (irStore n) = lowStore n h := by
  simp only [Store.mapH, irStore, lowStore, List.map_map]
  congr 1
  rw [show ((FuncInst.mapH fun _ => h) ∘ (lowFI : Nat → FuncInst Nat)) = fun _ => lowFI h from rfl,
    List.map_const', List.length_range]

/-! ## Preparation -/

section Prep

variable {H H' : Type}

theorem externAddrType_mapH (g : H → H') (s : Store H) (xa : ExternAddr) :
    externAddrType? (Store.mapH g s) xa = externAddrType? s xa := by
  cases xa <;> simp [externAddrType?, Store.mapH, List.getElem?_map]
  rfl

theorem externAddrsOk_mapH (g : H → H') (s : Store H) :
    ∀ (xas : List ExternAddr) (ts : List Silmaril.Wasm.Validation.CExternType),
      externAddrsOk? (Store.mapH g s) xas ts = externAddrsOk? s xas ts
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | xa :: xas, t :: ts => by
    simp only [externAddrsOk?, externAddrOk?, externAddrType_mapH, externAddrsOk_mapH g s xas ts]

/-- **Preparation commutes with renaming host code.** -/
theorem prepareE_mapH (g : H → H') (s : Store H) (m : Silmaril.Wasm.Module)
    (xas : List ExternAddr) :
    Silmaril.Wasm.Component.Engine.Core3.prepareE? (Store.mapH g s) m xas =
      (Silmaril.Wasm.Component.Engine.Core3.prepareE? s m xas).map
        (fun p => (Store.mapH g p.1, p.2.1, p.2.2)) := by
  unfold Silmaril.Wasm.Component.Engine.Core3.prepareE?
  cases Silmaril.Wasm.Validation.validate? m with
  | none => rfl
  | some mt =>
    dsimp only
    rw [externAddrsOk_mapH]
    split_ifs
    · rw [instantiateOnce?_mapH]
      cases instantiateOnce? s m xas with
      | none => rfl
      | some p =>
        obtain ⟨s', f', st⟩ := p
        cases st with
        | none => rfl
        | some x =>
          simp only [mapS_some]
          cases f'.module.funcs[x.toNat]? <;> rfl
    · rfl

end Prep

/-! ## The start function's trap -/

section Runs

variable {o : GrowOracle} {H : Type}

/-- **The start function's trap, against the trampolines**: a run of the start function of the
IR's instance to a trap is matched by an interpreter run of the same start function in the
store with renamed host code, to a trap. -/
theorem startTrap_low (g : Nat → H) {s : Store Nat} (hs : StoreOk (Store.mapH g s))
    {m : Silmaril.Wasm.Module} {xas : List ExternAddr} {s' : Store Nat} {mi : ModuleInst}
    {a : Nat}
    (hp : Silmaril.Wasm.Component.Engine.Core3.prepareE? s m xas = some (s', mi, some a))
    {c : Store Nat × Silmaril.Wasm.SingleThreaded.Thread}
    (hrun : Relation.ReflTransGen (Internal o) (s', Silmaril.Wasm.SingleThreaded.Thread.invoke a []) c)
    (hst : status o c.1 c.2 = .returned .trap) :
    ∃ n s'' t'', runC (stepI o) n (Store.mapH g s')
        (Silmaril.Wasm.SingleThreaded.Thread.invoke a []) =
          (s'', t'', .returned .trap) ∧ statusC (stepI o) s'' t'' = .returned .trap := by
  have h₁ := steps_of_internal hrun
  have h₂ := Steps.mapH (P := Silmaril.Wasm.SingleThreaded.profile o) g h₁
  have h₃ : Relation.ReflTransGen
      (Step (Silmaril.Wasm.SingleThreaded.profile o) (fun _ _ _ _ => False))
      ((Silmaril.Wasm.SingleThreaded.Thread.invoke a []).config (Store.mapH g s'))
      (Config.mapH g (c.2.config c.1)) := by
    have hc₀ : Config.mapH g ((Silmaril.Wasm.SingleThreaded.Thread.invoke a []).config s') =
        invoke (Store.mapH g s') a [] := invoke_mapH g s' a []
    rw [hc₀] at h₂
    exact h₂
  obtain ⟨t', hr, ht'⟩ := internal_of_steps h₃
  have hcode := code_of_status_trap hst
  have hst' : status o (Config.mapH g (c.2.config c.1)).store t' = .returned .trap := by
    refine status_trap_of_code ?_
    rw [ht']
    exact hcode
  have hp' := prepareE_mapH g s m xas
  rw [hp] at hp'
  obtain ⟨-, -, -, hcfg⟩ :=
    Silmaril.Wasm.Component.Engine.Core3.Typed.prepareE?_typed hs hp'
  have hok : ConfigOk ((Silmaril.Wasm.SingleThreaded.Thread.invoke a []).config
      (Store.mapH g s')) [] := hcfg _ rfl
  obtain ⟨n, hn⟩ := runCI_complete (I := fun c => ConfigOk c [])
    Silmaril.Wasm.SingleThreaded.Exec.typedInv' hok hr (by rw [hst']; nofun)
  rw [hst'] at hn
  refine ⟨n, _, _, hn, ?_⟩
  obtain ⟨-, hok', -⟩ := Silmaril.Wasm.SingleThreaded.Exec.runCI_sound_typed n _ _ hok hn
  rw [Silmaril.Wasm.SingleThreaded.Exec.statusI_eq_typed hok']
  exact hst'

end Runs

end Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp
