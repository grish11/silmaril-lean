module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp.Sim
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore.IR

/-!
# A quiet failure of a first node with lowered imports, as a run without import calls

`NodeQuiet n (.fail ()) cm w` is a run of the engine instance of the decoded module `m` of `cm`
against fresh host functions for its imports (`Param.instOfI`), each import call answered at
once by its wiring `w`. When every import of `m` has core type `fFlat` and is wired to the
`canon lower` of `f: func(u32)`:

* `nodeFailImp_cases`: the failure is a failed preparation of `m` against the imports
  (`irStore n`), or a preparation with a start function whose run (`Internal o`) traps **before
  any import call**. An import call is a callout of a typed thread (preparation types the start
  invocation, `prepareE?_typed`; internal steps preserve typing, `reachable_typed`), so its
  argument is one `i32` (`callout_args_typed`), which lifts to a `u32`: the wiring then calls `f`
  (`implsN_lower_call`), which a quiet node does not do.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore
open Silmaril.Wasm.Component Silmaril.Wasm.Component.DecoderBridge
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SingleThreaded (GrowOracle Internal status profile)

/-! ## The wiring calls `f` -/

/-- The wiring of an import of the fragment: the lowering of `f: func(u32)`. -/
abbrev lowF : Impl := ⟨[.lower ⟨[.u32], []⟩], .call 0⟩

/-- **An import call with an `i32` argument is wired to a call of `f`**: it is not answered at
once. -/
theorem implsN_lower_call {w : List Impl} {n : Nat} (hw : ∀ im ∈ w, im = lowF)
    {h : Fin n} (hh : h.val < w.length) (b : BitVec 32) (r : Option Payload) :
    implsN 1 w n (h, .flat [⟨.int .i32, b⟩]) ≠ .pure r := by
  have hget : w[h.val]? = some lowF := by
    rw [List.getElem?_eq_getElem hh, hw _ (List.getElem_mem hh)]
  intro e
  simp only [implsN, implsH, hget, Impl.prog, runChain, Adapter.down, liftArgs, ValTy.liftList,
    ValTy.lift, Option.map_some, Target.prog, Nat.zero_lt_one, ↓reduceIte] at e
  cases e

/-! ## Typing of the IR's start run -/

section Typing

variable {o : GrowOracle}

theorem storeOk_irStore : ∀ n, StoreOk (irStore n)
  | 0 => (Silmaril.Wasm.Component.Engine.Core3.Typed.empty_ok _).1
  | n + 1 => by
    have h := allocHost_irStore n
    exact (Silmaril.Wasm.Component.Engine.Core3.Typed.allocHost_storeOk (storeOk_irStore n) h).1

theorem funcs_steps {x y : Store Nat × Silmaril.Wasm.SingleThreaded.Thread}
    (h : Relation.ReflTransGen (Internal o) x y) : y.1.funcs = x.1.funcs := by
  induction h with
  | refl => rfl
  | @tail b c _ hst ih =>
    obtain ⟨s, t⟩ := b
    obtain ⟨s', t'⟩ := c
    exact (Silmaril.Wasm.SingleThreaded.Internal.funcs_prefix hst).trans ih

theorem statusP_profile {H : Type} (s : Store H) (t : Silmaril.Wasm.SingleThreaded.Thread) :
    Silmaril.Wasm.Game.statusP (profile o) s t = status o s t := by
  have e : ∀ y, Silmaril.Wasm.Game.InternalP (profile o) (s, t) y = Internal o (s, t) y :=
    fun y => by rw [internalP_profileR]
  unfold Silmaril.Wasm.Game.statusP status
  split_ifs <;> first | rfl | (exfalso; simp_all)

/-- **The start function of the IR's instance makes no untyped import call**: at a callout
reached from the start invocation, the argument is one `i32`. -/
theorem callout_i32 {n : Nat} {m : Silmaril.Wasm.Module} {xas : List ExternAddr}
    {s' : Store Nat} {mi : ModuleInst} {a : Nat}
    (hp : Silmaril.Wasm.Component.Engine.Core3.prepareE? (irStore n) m xas = some (s', mi, some a))
    {s₁ : Store Nat} {t₁ : Silmaril.Wasm.SingleThreaded.Thread}
    (hrun : Relation.ReflTransGen (Internal o) (s', Silmaril.Wasm.SingleThreaded.Thread.invoke a [])
      (s₁, t₁))
    {h : Nat} {args : List Silmaril.Wasm.Execution.Core.Val} (hst : status o s₁ t₁ = .callout h args) :
    ∃ b : BitVec 32, args = [.num ⟨.int .i32, b⟩] := by
  obtain ⟨hs', -, ⟨new, hnew, hwasm⟩, hcfg⟩ :=
    Silmaril.Wasm.Component.Engine.Core3.Typed.prepareE?_typed (storeOk_irStore n) hp
  have ht : Silmaril.Wasm.SingleThreaded.ThreadOk s'
      (Silmaril.Wasm.SingleThreaded.Thread.invoke a []) [] := hcfg a rfl
  obtain ⟨hs₁, ht₁⟩ := Silmaril.Wasm.SingleThreaded.reachable_typed hrun hs' ht
  obtain ⟨fi, hfi, hcode, ps, rs, hexp, hargs⟩ :=
    Silmaril.Wasm.Component.Engine.Core3.Typed.callout_args_typed hs₁ ht₁ hst
  have hf : s₁.funcs = s'.funcs := funcs_steps hrun
  rw [hf, hnew] at hfi
  rcases List.mem_append.mp hfi with hfi | hfi
  · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hfi
    have he := Expand.func_eq hexp
      (Silmaril.Wasm.Component.Engine.Core3.Typed.expand_ofFlatType (Param.v1Type fFlat))
    injection he with he₁ he₂
    rw [he₁] at hargs
    simp only [Param.v1Type, fFlat, List.map_cons, List.map_nil, Silmaril.Wasm.Validation.Ty.toList_ofList] at hargs
    rcases hargs with _ | ⟨hv, hrest⟩
    cases hrest
    obtain ⟨b, rfl⟩ := ValOk.int_inv hv
    exact ⟨b, rfl⟩
  · obtain ⟨c, hc⟩ := hwasm fi hfi
    rw [hc] at hcode
    cases hcode

end Typing

/-! ## A quiet failure -/

section Fail

variable {o : GrowOracle}

/-- **The IR's export lookup succeeds whenever preparation does** (any store, any imports). -/
theorem exportAddrs_someX (P : Silmaril.Wasm.Numerics.Profile) {m : Silmaril.Wasm.Module}
    {exps : CoreIface} {s : Store Nat} {xas : List ExternAddr} {s' : Store Nat} {mi : ModuleInst}
    {st : Option Nat}
    (hp : Silmaril.Wasm.Component.Engine.Core3.prepareE? s m xas = some (s', mi, st))
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

theorem range'_zero (n : Nat) : List.range' 0 n = List.range n := (List.range_eq_range' ..).symm

/-- **A quiet failure of a node whose imports are lowerings of `f: func(u32)`**: its
preparation against the imports fails, or it reports a start function whose run traps before any
import call. -/
theorem nodeFailImp_cases {m : Silmaril.Wasm.Module} {imps exps : CoreIface} {w : List Impl}
    {ys : List (Σ _ : (sigN imps.length).Op, Option Payload)}
    (hn : Silmaril.Wasm.Component.Reference.funcExportNames m = exps.map (·.1))
    (himps : imps.all (·.2 == fFlat) = true) (hwl : imps.length ≤ w.length)
    (hw : ∀ im ∈ w, im = lowF)
    (h : EngineInst (Silmaril.Wasm.Component.Reference.core3P (profile o))
      (Param.instOfI (Silmaril.Wasm.Component.Reference.core3P (profile o)) m imps exps) imps ys
      (.fail ()))
    (hq : ∀ y ∈ ys, implsN 1 w imps.length y.1 = .pure y.2) :
    Silmaril.Wasm.Component.Engine.Core3.prepareE? (irStore imps.length) m
        ((List.range imps.length).map ExternAddr.func) = none ∨
      ∃ s' mi a c, Silmaril.Wasm.Component.Engine.Core3.prepareE? (irStore imps.length) m
          ((List.range imps.length).map ExternAddr.func) = some (s', mi, some a) ∧
        Relation.ReflTransGen (Internal o) (s', Silmaril.Wasm.SingleThreaded.Thread.invoke a []) c ∧
        status o c.1 c.2 = .returned .trap := by
  have hA := allocHosts_ir (profile o) imps 0 himps
  rw [irStore_zero, Nat.zero_add, range'_zero] at hA
  have hprep : (Silmaril.Wasm.Component.Reference.core3P (profile o)).prepare?
      (irStore imps.length) m ((List.range imps.length).map
        (Silmaril.Wasm.Component.Reference.core3P (profile o)).ofFunc) =
      Silmaril.Wasm.Component.Engine.Core3.prepareE? (irStore imps.length) m
        ((List.range imps.length).map ExternAddr.func) := rfl
  have e : Param.allocHosts (Silmaril.Wasm.Component.Reference.core3P (profile o))
      ((Silmaril.Wasm.Component.Reference.core3P (profile o)).empty Nat) 0 imps =
      (irStore imps.length, List.range imps.length) := hA
  rcases h with ⟨hnone, -⟩ | ⟨J, f, c', hJ, hs, hr, hst⟩
  · left
    unfold Param.instOfI at hnone
    rw [e] at hnone
    dsimp only at hnone
    rw [hprep] at hnone
    cases hp : Silmaril.Wasm.Component.Engine.Core3.prepareE? (irStore imps.length) m
        ((List.range imps.length).map ExternAddr.func) with
    | none => rfl
    | some p =>
      obtain ⟨s', mi, st⟩ := p
      rw [hp] at hnone
      obtain ⟨addrs, ha⟩ := exportAddrs_someX (profile o) hp hn
      simp only [ha, Option.map_some] at hnone
      cases hnone
  · right
    unfold Param.instOfI at hJ
    rw [e] at hJ
    dsimp only at hJ
    rw [hprep] at hJ
    cases hp : Silmaril.Wasm.Component.Engine.Core3.prepareE? (irStore imps.length) m
        ((List.range imps.length).map ExternAddr.func) with
    | none => rw [hp] at hJ; cases hJ
    | some p =>
      obtain ⟨s', mi, st⟩ := p
      rw [hp] at hJ
      dsimp only at hJ
      obtain ⟨addrs, -, rfl⟩ := Option.map_eq_some_iff.mp hJ
      cases hs
      have e : @Engine.CoreEngine.Internal (Silmaril.Wasm.Component.Reference.core3P (profile o))
          Nat = Internal o := internalP_profileR
      cases hr with
      | nil run =>
        unfold Engine.CoreEngine.Steps at run
        rw [e] at run
        exact ⟨s', mi, f, c', rfl, run, status_trap_of_code (code_of_statusP_trap (flatStatus_trap hst))⟩
      | @call _ s₁ _ t₁ hc args _ _ run callout hh r _ =>
        exfalso
        unfold Engine.CoreEngine.Steps at run
        rw [e] at run
        obtain ⟨args', hst', hfl⟩ :=
          Silmaril.Wasm.Component.Engine.Core3.Typed.flatStatus_eq_callout' callout
        have hst'' : status o s₁ t₁ = .callout hc args' := (statusP_profile s₁ t₁).symm.trans hst'
        obtain ⟨b, rfl⟩ := callout_i32 hp run hst''
        simp only [List.mapM_cons, List.mapM_nil, Silmaril.Wasm.SingleThreaded.toFlat?] at hfl
        cases hfl
        exact implsN_lower_call hw (by simp only; omega) b r (hq _ List.mem_cons_self)

end Fail

end Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp
