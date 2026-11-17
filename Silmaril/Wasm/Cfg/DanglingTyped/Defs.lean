module

public import Silmaril.Wasm.Cfg.DanglingExn.Defs
public import Silmaril.Wasm.Execution.Core.Sim.TypedContext

@[expose] public section

/-!
# A relaxed typing invariant for dangling exception references: definitions

A host may throw an exception address that names no exception of the store
(`DanglingExn.Dangling`). `catch_all_ref` then pushes the dangling reference as a value, Wasm code
may store it in a local or a global, put it in the fields of a new exception, and later a Wasm
`throw` may allocate exactly that address (aliasing). No Core typing holds for such a
configuration (`DanglingExn.not_valOk_exn`, `not_storeOk_of_global`, `not_storeOk_addExn_self`).
The definitions here keep Core's `RefOk`, `ConfigOk` and `StoreOk` unchanged and never change the
actual store: they type a configuration on a **typing witness** of its store.

* `gst s T X`: the store `s` with tags `T` and exceptions `X`, every other component unchanged;
* `GhostOk s T X`: `gst s T X` witnesses `s`. The tags of `s` are a prefix of `T`; `X` is longer
  than `s.exns`; each exception of `s` sits in `X` at its address with its tag and its fields equal
  up to exception addresses (`ValApprox`); every further exception of `X` (a pad, at a dangling
  address of `s`) has no field and a tag that is not a tag of `s`;
* `Unsupp`, `ISupp`, `ASupp`, `FrameBelow`, `FuncsSupp`: the supported profile. No `ref.test`,
  `br_on_cast`, `br_on_cast_fail` or aggregate (struct, array) instruction; `ref.cast` only at a
  defined type, as `call_indirect` produces; every frame names only tags of the store. The
  exception checker's profile (`Interp.XProfile.xInstr` with `throw`, `throw_ref`, `try_table`)
  is inside it;
* `HeapBelow s`: struct and array fields name only exceptions of `s`;
* **`ConfigOkD c`**: supported, `HeapBelow`, and some witness types the code in context
  (`Sim.ContextTyped`) with the actual frame and code;
* **`StoreOkD s`**: supported functions, `HeapBelow`, and some witness that is `StoreOk`;
* `HostTypedD host`: every answer keeps the store and its values have the callee's result types;
  thrown addresses are unconstrained (`HostTyped` without its exception clause).

Theorems in `Silmaril.Wasm.Cfg.DanglingTyped.Thms`.
-/

namespace Silmaril.Wasm.Cfg.DanglingTyped

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

variable {H : Type}

/-! ## Equality up to exception addresses -/

/-- References equal up to exception addresses (the left ones below `N`). -/
inductive RefApprox (N : Nat) : Ref → Ref → Prop where
  | refl (r : Ref) : RefApprox N r r
  | exn {a b : Nat} (h : a < N) : RefApprox N (.exn a) (.exn b)
  | extern {r r' : Ref} (h : RefApprox N r r') : RefApprox N (.extern r) (.extern r')

/-- Values equal up to exception addresses (the left ones below `N`). -/
def ValApprox (N : Nat) (v w : Val) : Prop :=
  v = w ∨ ∃ r r', v = .ref r ∧ w = .ref r' ∧ RefApprox N r r'

/-- Every exception address of a reference satisfies `p`. -/
def RefLeaves (p : Nat → Prop) : Ref → Prop
  | .exn a => p a
  | .extern r => RefLeaves p r
  | _ => True

/-! ## The supported profile -/

/-- Instructions outside the supported profile: runtime type tests and casts other than
`ref.cast` at a defined type, and the aggregate (struct and array) instructions. -/
def Unsupp : Instr → Prop
  | .refTest _ | .brOnCast .. | .brOnCastFail .. => True
  | .refCast ⟨_, .abstract _⟩ => True
  | .structNew _ | .structNewDefault _ | .structGet .. | .structSet .. | .arrayNew _
  | .arrayNewDefault _ | .arrayNewFixed .. | .arrayNewData .. | .arrayNewElem .. | .arrayGet ..
  | .arraySet _ | .arrayLen | .arrayFill _ | .arrayCopy .. | .arrayInitData ..
  | .arrayInitElem .. => True
  | _ => False

/-- Structured instructions (with nested bodies). -/
def Structured : Instr → Prop
  | .block .. | .loop .. | .if_ .. | .tryTable .. => True
  | _ => False

/-- **A supported instruction**: no unsupported instruction, also in nested bodies. -/
inductive ISupp : Instr → Prop where
  | block (bt : BlockType) {body : List Instr} (h : ∀ i ∈ body, ISupp i) :
      ISupp (.block bt body)
  | loop (bt : BlockType) {body : List Instr} (h : ∀ i ∈ body, ISupp i) : ISupp (.loop bt body)
  | if_ (bt : BlockType) {b₁ b₂ : List Instr} (h₁ : ∀ i ∈ b₁, ISupp i) (h₂ : ∀ i ∈ b₂, ISupp i) :
      ISupp (.if_ bt b₁ b₂)
  | tryTable (bt : BlockType) (cs : List Catch) {body : List Instr} (h : ∀ i ∈ body, ISupp i) :
      ISupp (.tryTable bt cs body)
  | atom {i : Instr} (hs : ¬ Structured i) (hn : ¬ Unsupp i) : ISupp i

/-- A frame whose module names only tag addresses below `k`. -/
def FrameBelow (k : Nat) (f : Frame) : Prop := ∀ t ∈ f.module.tags, t < k

/-- **A supported administrative instruction**: supported instructions, frames below `k`. -/
inductive ASupp (k : Nat) : Admin → Prop where
  | plain {i : Instr} (h : ISupp i) : ASupp k (.plain i)
  | ref (r : Ref) : ASupp k (.ref r)
  | callRefType (d : DefType) : ASupp k (.callRefType d)
  | returnCallRefType (d : DefType) : ASupp k (.returnCallRefType d)
  | label (n : Nat) {cont : List Instr} {body : List Admin} (hc : ∀ i ∈ cont, ISupp i)
      (hb : ∀ a ∈ body, ASupp k a) : ASupp k (.label n cont body)
  | handler (n : Nat) (cs : List Catch) {body : List Admin} (hb : ∀ a ∈ body, ASupp k a) :
      ASupp k (.handler n cs body)
  | frame (n : Nat) {fr : Frame} {body : List Admin} (hf : FrameBelow k fr)
      (hb : ∀ a ∈ body, ASupp k a) : ASupp k (.frame n fr body)
  | trap : ASupp k .trap

/-- **Supported functions**: Wasm bodies are supported, modules name tags below the store's. -/
def FuncsSupp (s : Store H) : Prop :=
  ∀ fi ∈ s.funcs, FrameBelow s.tags.length ⟨[], fi.module⟩ ∧
    ∀ code, fi.code = .wasm code → ∀ i ∈ code.body, ISupp i

/-- **Struct and array fields name exceptions of the store** (also under `extern`). -/
def HeapBelow (s : Store H) : Prop :=
  (∀ si ∈ s.structs, ∀ r, FieldVal.val (.ref r) ∈ si.fields → RefLeaves (· < s.exns.length) r) ∧
    ∀ ai ∈ s.arrays, ∀ r, FieldVal.val (.ref r) ∈ ai.fields → RefLeaves (· < s.exns.length) r

/-! ## Typing witnesses -/

/-- `s` with tags `T` and exceptions `X`. -/
abbrev gst (s : Store H) (T : List TagInst) (X : List ExnInst) : Store H :=
  { s with tags := T, exns := X }

/-- **`gst s T X` is a typing witness of `s`.** -/
structure GhostOk (s : Store H) (T : List TagInst) (X : List ExnInst) : Prop where
  tags : s.tags <+: T
  lt : s.exns.length < X.length
  real : ∀ (a : Nat) (e : ExnInst), s.exns[a]? = some e → ∃ e', X[a]? = some e' ∧
    e'.tag = e.tag ∧ List.Forall₂ (ValApprox X.length) e.fields e'.fields
  pad : ∀ (a : Nat) (e' : ExnInst), s.exns.length ≤ a → X[a]? = some e' →
    s.tags.length ≤ e'.tag ∧ e'.fields = []

/-- **The relaxed configuration invariant.** -/
structure ConfigOkD (c : Config H) : Prop where
  funcs : FuncsSupp c.store
  frame : FrameBelow c.store.tags.length c.frame
  code : ∀ a ∈ c.code, ASupp c.store.tags.length a
  heap : HeapBelow c.store
  ghost : ∃ T X, GhostOk c.store T X ∧ Sim.ContextTyped ⟨gst c.store T X, c.frame, c.code⟩

/-- **The relaxed store invariant.** -/
def StoreOkD (s : Store H) : Prop :=
  FuncsSupp s ∧ HeapBelow s ∧ ∃ T X, GhostOk s T X ∧ StoreOk (gst s T X)

/-! ## Hosts -/

/-- Typing of a host answer, except its exception address. -/
def ResultTypedD (s : Store H) : Result → List CValType → Prop
  | .values vs, ts => List.Forall₂ (ValOk s) vs ts
  | _, _ => True

/-- **A store-keeping host whose values are typed**, any exception address allowed. -/
def HostTypedD (host : HostSemantics H) : Prop :=
  ∀ (hh : H) (s : Store H) (us : List Val) (s' : Store H) (r : Result),
    host hh s us (.returned s' r) → s' = s ∧ ∀ fi ∈ s.funcs, fi.code = .host hh →
      ∀ ps rs, Expand fi.type (.func ps rs) → ResultTypedD s r rs.toList

end Silmaril.Wasm.Cfg.DanglingTyped
