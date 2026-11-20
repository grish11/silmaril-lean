module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Rules
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Live.Defs
public import Silmaril.Wasm.Game.IOAccept.Thms
public import Silmaril.Wasm.SingleThreaded.Agreement
public import Silmaril.Wasm.Verify.Check.Thms

/-!
# Proofs: forward execution for non-vacuity of the memory-observing examples

Shared rules for exhibiting concrete traced sessions of the example modules, for every profile:

* the spec instance of a module exists when the checker computes it (`spec_exists`, kernel
  evaluation of `specInstance?`), and the memories of a prepared instance have the sizes a
  kernel check reads (`memSizes`);
* **forward steps** of the instructions the examples use, in a function body (`step_body`: frame
  and label of arity `0`) and between a value prefix and a rest (`step_mid`): packed and full
  `i32` stores, `call`, `local.set`, `local.get`;
* `decompose_fill`: the host-call redex in a callout context is found by `decompose?`;
* the counting host (`countEnv`) answers every call, and is admitted by `ShapedReply shape` when
  its answers have the shape (`countEnv_reply`); its first handle `base pol` and the next two are
  not the policy's sentinel (`base_ne`).

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game
  Silmaril.Wasm.Game.Accept Silmaril.Wasm.Game.IOAccept Silmaril.Accept.Handle
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Live Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound

/-- The host-free semantics of traced sessions' internal steps. -/
abbrev NH : HostSemantics Nat := fun _ _ _ _ => False

/-! ## Instances -/

/-- The spec instance exists when the checker computes it. -/
theorem spec_exists {m : Module} (h : (Silmaril.Wasm.Verify.specInstance? m).isSome = true) :
    ∃ mt Is c₀, IsSpecInstance m mt Is c₀ := by
  obtain ⟨⟨mt, Is, c₀⟩, hx⟩ := Option.isSome_iff_exists.1 h
  exact ⟨mt, Is, c₀, Silmaril.Wasm.Verify.isSpecInstance_of_specInstance? hx⟩

/-- The memory sizes of the prepared instance of a module. -/
def memSizes (m : Module) : List Nat :=
  match prep m with
  | some (c, _) => c.store.mems.map fun mi => mi.bytes.size
  | none => []

/-- A prepared instance with one memory of one page. -/
theorem one_page {m : Module} (hm : memSizes m = [65536]) {c : Config Nat}
    {st : Option FuncIdx} (hp : prep m = some (c, st)) :
    ∃ mi, c.store.mems = [mi] ∧ mi.bytes.size = 65536 := by
  unfold memSizes at hm
  rw [hp] at hm
  simpa using hm

/-! ## Forward steps -/

variable {P : Profile} {host : HostSemantics Nat} {s s' : Store Nat} {F F' : Frame}
  {is is' : List Admin}

/-- A step between a value prefix and a rest. -/
theorem step_mid (pre : List Val) (rest : List Admin) (h : Step P host ⟨s, F, is⟩ ⟨s', F', is'⟩) :
    Step P host ⟨s, F, vals pre ++ is ++ rest⟩ ⟨s', F', vals pre ++ is' ++ rest⟩ := by
  by_cases hne : pre ≠ [] ∨ rest ≠ []
  · exact Step.ctxtInstrs h hne
  · simp only [ne_eq, not_or, not_not] at hne
    obtain ⟨rfl, rfl⟩ := hne
    simpa [vals] using h

/-- A step in the body of a called function. -/
theorem step_body {f : Frame} {n k : Nat} (h : Step P host ⟨s, F, is⟩ ⟨s', F', is'⟩) :
    Step P host ⟨s, f, [.frame n F [.label k [] is]]⟩ ⟨s', f, [.frame n F' [.label k [] is']]⟩ :=
  .ctxtFrame (.ctxtLabel h)

/-- A store succeeds in bounds. -/
theorem store_some {B : ByteArray} {a n : Nat} (w : BitVec (8 * n)) (h : a + n ≤ B.size) :
    ∃ B', Memory.store B a w = some B' := by
  rcases hs : Memory.store B a w with _ | B'
  · have := store_none_lt hs
    omega
  · exact ⟨B', rfl⟩

/-- A packed `i32` store to memory `0`. -/
theorem step_storePack {sz : PackSize} {a v : BitVec 32} {mi : MemInst} {b : ByteArray}
    (hF : F.module.mems = [0]) (hmi : s.mems[0]? = some mi)
    (hst : Memory.store mi.bytes (effAddr a.toNat ⟨0, 0⟩) (count := sz.width / 8)
      (v.setWidth _) = some b) :
    Step P host ⟨s, F, [.plain (.intConst .i32 a), .plain (.intConst .i32 v),
      .plain (.intStore .i32 (some sz) ⟨0⟩ ⟨0, 0⟩)]⟩ ⟨s.setMem 0 { mi with bytes := b }, F, []⟩ :=
  .memory (.storePackVal (a := .i32) (i := a) (t := .i32) (c := v) (mem?_of hF hmi) hst)

/-- A full-width `i32` store to memory `0`. -/
theorem step_store32 {a v : BitVec 32} {mi : MemInst} {b : ByteArray}
    (hF : F.module.mems = [0]) (hmi : s.mems[0]? = some mi)
    (hst : Memory.store mi.bytes (effAddr a.toNat ⟨0, 0⟩) (count := IntType.i32.width / 8)
      (v.setWidth _) = some b) :
    Step P host ⟨s, F, [.plain (.intConst .i32 a), .plain (.intConst .i32 v),
      .plain (.intStore .i32 none ⟨0⟩ ⟨0, 0⟩)]⟩ ⟨s.setMem 0 { mi with bytes := b }, F, []⟩ :=
  .memory (.storeIntVal (a := .i32) (i := a) (t := .i32) (c := v) (mem?_of hF hmi) hst)

/-- `call x` of the function at address `a`. -/
theorem step_call {x : FuncIdx} {a : Nat} {fi : FuncInst Nat}
    (hx : F.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi) :
    Step P host ⟨s, F, [.plain (.call x)]⟩ ⟨s, F, [.ref (.func a), .callRefType fi.type]⟩ :=
  Step.call hx hf

/-- `local.set x`. -/
theorem step_localSet {x : LocalIdx} {v : Val} (hx : x.toNat < F.locals.length) :
    Step P host ⟨s, F, [v.toAdmin, .plain (.localSet x)]⟩ ⟨s, F.setLocal x v, []⟩ :=
  .variable (.localSet hx)

/-- `local.get x`. -/
theorem step_localGet {x : LocalIdx} {v : Val} (hv : F.local? x = some (some v)) :
    Step P host ⟨s, F, [.plain (.localGet x)]⟩ ⟨s, F, [v.toAdmin]⟩ :=
  .variable (.localGet hv)

/-- **Completeness of `decompose?`**: a host-call redex in a callout context is found. -/
theorem decompose_fill {s : Store Nat} (E : Ctx) {args : List Val} {a : Nat} {c : Admin}
    {fi : FuncInst Nat} {ps rs : Ty (.list .val)} {h : Nat} (hc : c.IsCallRef)
    (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
    (hn : args.length = ps.length) (hcode : fi.code = .host h) :
    decompose? s (E.fill (vals args ++ [.ref (.func a), c])) = some (E, a, h, args) := by
  induction E with
  | top pre rest =>
    have := decompose?_wrap pre rest (decompose?_redex hc hf he hn hcode)
    simpa [Ctx.wrap, Ctx.fill] using this
  | label pre n cont E rest ih =>
    have hsp : splitVals (Ctx.fill (.label pre n cont E rest) (vals args ++ [.ref (.func a), c]))
        = (pre, .label n cont (E.fill (vals args ++ [.ref (.func a), c])) :: rest) := by
      simp only [Ctx.fill, List.append_assoc, List.singleton_append]
      exact splitVals_vals_cons rfl rest
    rw [decompose?_of_split hsp]
    simp [decompHead, ih]
  | handler pre n cs E rest ih =>
    have hsp : splitVals (Ctx.fill (.handler pre n cs E rest) (vals args ++ [.ref (.func a), c]))
        = (pre, .handler n cs (E.fill (vals args ++ [.ref (.func a), c])) :: rest) := by
      simp only [Ctx.fill, List.append_assoc, List.singleton_append]
      exact splitVals_vals_cons rfl rest
    rw [decompose?_of_split hsp]
    simp [decompHead, ih]
  | frame pre n f E rest ih =>
    have hsp : splitVals (Ctx.fill (.frame pre n f E rest) (vals args ++ [.ref (.func a), c]))
        = (pre, .frame n f (E.fill (vals args ++ [.ref (.func a), c])) :: rest) := by
      simp only [Ctx.fill, List.append_assoc, List.singleton_append]
      exact splitVals_vals_cons rfl rest
    rw [decompose?_of_split hsp]
    simp [decompHead, ih]

/-- The callout context of a call in the body of a called function (frame and label of arity
`0`), with `rest` after the call. -/
abbrev bodyCtx (F : Frame) (rest : List Admin) : Ctx :=
  .frame [] 0 F (.label [] 0 [] (.top [] rest) []) []

/-! ## The counting host -/

/-- The counting host is admitted when its answers have the shape. -/
theorem countEnv_reply {out : Nat → BitVec 32 → List Val} {shape : Nat → List Val → Prop}
    (h : ∀ k q, shape k (out k q)) (s : Store Nat) :
    ReplyEnvs (ShapedReply shape) s (countEnv out) := by
  rintro q e a q' ⟨-, rfl⟩
  refine ⟨⟨rfl, rfl⟩, fun vs hv => ?_⟩
  cases hv
  exact h _ _

/-- The first handles of a counting host are not the sentinel. -/
theorem base_ne (pol : Policy (BitVec 32)) {k : BitVec 32} (hk : k + 1 ≠ 0) :
    pol.sentinel ≠ some (base pol + k) := by
  unfold base
  rcases pol.sentinel with _ | x
  · simp
  · intro h
    simp only [Option.getD_some, Option.some.injEq] at h
    apply hk
    bv_omega

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live
