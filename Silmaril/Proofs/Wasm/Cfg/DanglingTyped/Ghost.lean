module

public import Silmaril.Proofs.Wasm.Cfg.DanglingTyped.Widen
public import Silmaril.Proofs.Wasm.Cfg.DanglingTyped.Approx
public import Silmaril.Wasm.Execution.Core.Soundness.ProgressAux

@[expose] public section

/-!
# The typing witness of a store with dangling exception references (proofs)

A **witness store** `gst s T X` is `s` with tags `T` and exceptions `X`, every other component
unchanged. `GhostOk s T X` says that it witnesses `s`:

* the tags of `s` are a prefix of `T`;
* `X` has more exceptions than `s`;
* each exception of `s` is in `X` at the same address with the same tag and fields equal up to
  exception references (`ValApprox`);
* each further exception of `X` (a **pad**, at a dangling address of `s`) has a tag that is not a
  tag of `s`.

The witness only types: no claim is made that it runs like `s`. The step lemma
`step_ghost` relates one host-free Core step of `s` to one of the witness, for configurations in
the supported profile (`ASupp`, no `ref.test`, `br_on_cast*`, aggregate instructions, and
`ref.cast` only at a defined type, as `call_indirect` produces), whose frames name only tags of
`s` (`FrameBelow`). Every decision the step takes reads the same answer on both stores:
`CatchMatches` (a pad's tag is not a tag of any frame), `RefOk` at the supported casts (an
exception reference is never a reference to a defined type, `not_refOk_exn_typeIdx`), and the
store lookups other than exceptions. The resulting witness code differs from the actual code only
in exception references (caught payloads, `CodeApprox`), and a Wasm `throw` allocates in the
witness at `X.length` instead of `s.exns.length`.
-/

namespace Silmaril.Wasm.Cfg.Proofs.DanglingTyped

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

variable {H : Type}

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

/-! ## Witness stores -/

/-- `s` with tags `T` and exceptions `X`. -/
abbrev gst (s : Store H) (T : List TagInst) (X : List ExnInst) : Store H :=
  { s with tags := T, exns := X }

/-- **`gst s T X` is a typing witness of `s`.** -/
structure GhostOk (s : Store H) (T : List TagInst) (X : List ExnInst) : Prop where
  tags : s.tags <+: T
  lt : s.exns.length < X.length
  real : ∀ (a : Nat) (e : ExnInst), s.exns[a]? = some e → ∃ e', X[a]? = some e' ∧
    e'.tag = e.tag ∧ List.Forall₂ (ValApprox X.length) e.fields e'.fields
  pad : ∀ (a : Nat) (e' : ExnInst), s.exns.length ≤ a → X[a]? = some e' → s.tags.length ≤ e'.tag

theorem GhostOk.widen {s : Store H} {T : List TagInst} {X : List ExnInst} (h : GhostOk s T X) :
    Widen s (gst s T X) :=
  ⟨rfl, h.tags, fun a e he => by
    obtain ⟨e', h', -⟩ := h.real a e he
    exact ⟨e', h'⟩⟩

/-! ## Reference typing on the witness -/

theorem refOk_exn_isExn {s : Store H} {r : Ref} {rt : CRefType} (h : RefOk s r rt) :
    ∀ a n hh, r = .exn a → rt = .ref n hh → isExnT hh = true := by
  induction h with
  | exn _ => intro a n hh e1 e2; cases e2; rfl
  | sub h hok hs ih =>
    intro a n hh e1 e2
    subst e2
    cases hs with
    | refNonNull h' => exact (Sub.exn_aux h').2.1 (ih a _ _ e1 rfl)
    | refNull h' => exact (Sub.exn_aux h').2.1 (ih a _ _ e1 rfl)
  | _ => intro a n hh e1; cases e1

/-- **An exception reference is never a reference to a defined type.** -/
theorem not_refOk_exn_typeIdx {s : Store H} {m : ModuleInst} {a : Nat} {b : Bool} {y : TypeIdx} :
    ¬ RefOk s (.exn a) (m.instRef ⟨b, .typeIdx y⟩) := by
  intro h
  have := refOk_exn_isExn h a _ _ rfl rfl
  revert this
  simp [liftHeap, isExnT, Ty.subst]

/-- A reference that is not an exception reference has the same types on the witness. -/
theorem refOk_of_gst {s : Store H} {T : List TagInst} {X : List ExnInst} {r : Ref}
    {rt : CRefType} (h : RefOk (gst s T X) r rt) (hr : ∀ a, r ≠ .exn a) : RefOk s r rt := by
  induction h with
  | null => exact .null
  | i31 b => exact .i31 b
  | struct hh => exact .struct hh
  | array hh => exact .array hh
  | func hh => exact .func hh
  | exn _ => exact absurd rfl (hr _)
  | host a => exact .host a
  | @extern r' h₁ hn ih =>
    refine .extern (ih fun a e => ?_) hn
    subst e
    have := refOk_exn_isExn h₁ a _ _ rfl rfl
    simp [isExnT] at this
  | sub _ hok hs ih => exact .sub (ih hr) hok hs

/-- **A supported cast decides alike on a store and its witness.** -/
theorem refOk_gst_iff {s : Store H} {T : List TagInst} {X : List ExnInst} (hg : GhostOk s T X)
    {m : ModuleInst} {r : Ref} {rt : RefType} (hn : ¬ Unsupp (.refCast rt)) :
    RefOk (gst s T X) r (m.instRef rt) ↔ RefOk s r (m.instRef rt) := by
  refine ⟨fun h => ?_, fun h => hg.widen.refOk h⟩
  by_cases hr : ∃ a, r = .exn a
  · obtain ⟨a, rfl⟩ := hr
    obtain ⟨b, ht⟩ := rt
    cases ht with
    | abstract _ => exact absurd trivial hn
    | typeIdx y => exact absurd h not_refOk_exn_typeIdx
  · exact refOk_of_gst h fun a e => hr ⟨a, e⟩

/-- **A catch clause decides alike on a store and its witness**, at a frame below the store's
tags. -/
theorem catchMatches_gst_iff {s : Store H} {T : List TagInst} {X : List ExnInst}
    (hg : GhostOk s T X) {f : Frame} (hf : FrameBelow s.tags.length f) {a : Nat} {c : Catch} :
    CatchMatches (gst s T X) f a c ↔ CatchMatches s f a c := by
  cases c with
  | catchAll _ => exact Iff.rfl
  | catchAllRef _ => exact Iff.rfl
  | catch_ x l =>
    show (∃ e ta, X[a]? = some e ∧ _ ∧ _) ↔ (∃ e ta, s.exns[a]? = some e ∧ _ ∧ _)
    constructor
    · rintro ⟨e', ta, he', hta, rfl⟩
      by_cases ha : a < s.exns.length
      · obtain ⟨e', h', ht, -⟩ := hg.real a _ (List.getElem?_eq_getElem ha)
        rw [he'] at h'
        cases h'
        exact ⟨_, _, List.getElem?_eq_getElem ha, hta, ht.symm⟩
      · have := hg.pad a e' (Nat.le_of_not_lt ha) he'
        have := hf _ (List.mem_of_getElem? hta)
        omega
    · rintro ⟨e, ta, he, hta, rfl⟩
      obtain ⟨e', h', ht, -⟩ := hg.real a e he
      exact ⟨e', _, h', hta, ht⟩
  | catchRef x l =>
    show (∃ e ta, X[a]? = some e ∧ _ ∧ _) ↔ (∃ e ta, s.exns[a]? = some e ∧ _ ∧ _)
    constructor
    · rintro ⟨e', ta, he', hta, rfl⟩
      by_cases ha : a < s.exns.length
      · obtain ⟨e', h', ht, -⟩ := hg.real a _ (List.getElem?_eq_getElem ha)
        rw [he'] at h'
        cases h'
        exact ⟨_, _, List.getElem?_eq_getElem ha, hta, ht.symm⟩
      · have := hg.pad a e' (Nat.le_of_not_lt ha) he'
        have := hf _ (List.mem_of_getElem? hta)
        omega
    · rintro ⟨e, ta, he, hta, rfl⟩
      obtain ⟨e', h', ht, -⟩ := hg.real a e he
      exact ⟨e', _, h', hta, ht⟩

end Silmaril.Wasm.Cfg.Proofs.DanglingTyped
