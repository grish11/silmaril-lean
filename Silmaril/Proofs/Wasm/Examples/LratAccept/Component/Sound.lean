module

public import Silmaril.Proofs.Wasm.Examples.LratAccept.Component.Inst
public import Silmaril.Wasm.Component.Reference.ListLift.Thms
public import Silmaril.Wasm.Component.Reference.ListLift.Bump.Thms
public import Silmaril.Wasm.Acceptor.Abi.Thms
public import Silmaril.Wasm.Acceptor.Bridge.Thms

/-!
# The LRAT acceptor component: soundness of accepting calls

An instance of the acceptor kit (`Silmaril.Wasm.Acceptor`):

* `lower2`, `holdsL_nested`: the lowering of the two arguments ends in a store of the acceptor
  holding them (`params_holds` with `lratBump`, read by the kit's `flatHolds_two`), and a
  lowered `list<list<s32>>` reads back as `nestedAt` with its blocks in bounds (the kit's
  `holdsL_listAt` with `reads_words`);
* `lratKit`, `streamExport`, `nestedExport`: the kit of `lratComp` (instance, bump allocator,
  invariant `LInvL`) and its two exports, with `Goal xs cs := xs ∈ UnsatStream ∧
  (Silmaril.Logic.SAT.Carrier.LratStream.decode cs).isSome` and `Goal p cs := p ∈ UnsatNested ∧ (Silmaril.Logic.SAT.Carrier.LratStream.decode
  cs).isSome`; `streamExport_core`, `nestedExport_core`: the Core obligations, from the kit's
  `flatHolds_read2` and the core soundness theorems
  `Silmaril.Wasm.Examples.LratAccept.checkStream_sound`, `checkNested_sound`, which hold from
  any LRAT state;
* `checkStream_sound`, `checkStream_cert`, `checkNested_sound`, `checkNested_cert`: the kit's
  `CheckerExport.sound`; `checkStream_rejects_problem`, `checkStream_rejects_cert`,
  `checkNested_rejects_problem`, `checkNested_rejects_cert`: the kit's
  `CheckerExport.rejects_none`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Examples.LratAccept.Component

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Examples.LratAccept
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.ListLift
open Silmaril.Wasm.Acceptor (Kit CheckerExport reads_s32 reads_words flatHolds_two flatHolds_read2
  holdsL_listAt checkList_map)
open Silmaril.Wasm.Logic.Words (wd words)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Logic.SAT.Carrier (UnsatStream UnsatNested decodeStream decodeNested)

/-! ## Reading the arguments -/

theorem memBytesOf_acc {s : Store Nat} {G : List (BitVec 32)} {B₀ : ByteArray} {top : BitVec 32}
    {B₁ : ByteArray} (hs : AccStore s G B₀ top B₁) : memBytesOf s 1 = B₁ := by
  simp [memBytesOf, hs.mems]

/-- **The clauses of a `list<list<s32>>` are the words of their blocks** (the kit's
`holdsL_listAt` at `reads_words`). -/
theorem holdsL_nested {B : ByteArray} {lo hi : Nat} (p : List (List (BitVec 32))) (q : Nat)
    (h : HoldsL B lo hi (.list .s32) (p.map LVal.ofWords) q) :
    nestedAt B q p.length = p ∧
      ∀ i < p.length, (wd B (q + 8 * i)).toNat + 4 * (wd B (q + 8 * i + 4)).toNat ≤ B.size :=
  holdsL_listAt reads_words p q h

/-! ## The lowering of the two arguments -/

/-- **The two lowered arguments in memory**: a list of type `list<t>` and the certificate words,
lowered into memory address `1`, end in a store of the acceptor whose ABI memory holds them. -/
theorem lower2 {P : Profile} {t : LTy} {us : List LVal} {cs : List (BitVec 32)} {s : Store Nat}
    {fl : List Core.Val}
    (hL : LParams P 10 1 [.list t, .list .s32] [.list us, LVal.ofWords cs] accI.store fl s) :
    ∃ q₁ q₂ G B₀ top B₁ lo hi, fl = [.i32 (BitVec.ofNat 32 q₁),
        .i32 (BitVec.ofNat 32 us.length), .i32 (BitVec.ofNat 32 q₂),
        .i32 (BitVec.ofNat 32 cs.length)] ∧
      q₁ < 2 ^ 32 ∧ q₂ < 2 ^ 32 ∧ us.length < 2 ^ 32 ∧ cs.length < 2 ^ 32 ∧
      AccStore s G B₀ top B₁ ∧
      q₁ + us.length * t.size ≤ B₁.size ∧ HoldsL B₁ lo hi t us q₁ ∧
      q₂ + 4 * cs.length ≤ B₁.size ∧ words B₁ q₂ cs.length = cs := by
  obtain ⟨t₁, ⟨⟨G, B₀, B₁, hs⟩, -⟩, -, -, hF⟩ := params_holds (lratBump P) hL lInvL_init
  rw [memBytesOf_acc hs] at hF
  obtain ⟨q₁, q₂, rfl, hq₁, hq₂, hl₁, hl₂, hb₁, hL₁, hb₂, hL₂⟩ := flatHolds_two hF
  simp only [List.length_map, LTy.size_s32] at hl₂ hb₂ ⊢
  obtain ⟨hw, -⟩ := holdsL_listAt reads_s32 cs q₂ hL₂
  exact ⟨q₁, q₂, G, B₀, _, B₁, heapBase, t₁, rfl, hq₁, hq₂, hl₁, hl₂, hs, hb₁, hL₁, by omega, hw⟩

/-! ## The kit instance -/

/-- **The kit of `lratComp`**: the instance `accI`, the bump allocator `lratBump` for memory
`1`, the invariant `LInvL` from `heapBase`. -/
def lratKit : Kit lratComp where
  I := accI
  good := lratComp_good
  inst := lratComp_inst
  N := memBytes
  Inv := LInvL
  bump P := by
    show BumpAlloc P (lratComp.coreAddr accI "cabi_realloc") 1 memBytes LInvL
    rw [t_coreAddrs.1]
    exact lratBump P
  base := heapBase
  init := lInvL_init

/-- **The export `check-stream`**: an accepting call means that the stream is unsatisfiable and
the certificate decodes. -/
def streamExport : CheckerExport lratComp (List (BitVec 32)) (List (BitVec 32)) where
  x := ⟨"check-stream", [("problem", .list .s32), ("cert", .list .s32)], "check-stream"⟩
  mem := List.mem_cons_self
  enc xs cs := [LVal.ofWords xs, LVal.ofWords cs]
  typed xs cs := by
    show LTy.checkParams [.list .s32, .list .s32] [LVal.ofWords xs, LVal.ofWords cs] = true
    simp only [LTy.checkParams, LVal.ofWords, LTy.check, Bool.and_true,
      checkList_map (t := .s32) (f := LVal.s32) (fun _ => rfl)]
  Goal xs cs := xs ∈ UnsatStream ∧ (Silmaril.Logic.SAT.Carrier.LratStream.decode cs).isSome = true

/-- **The export `check-nested`**: an accepting call means that the formula is
unsatisfiable and the certificate decodes. -/
def nestedExport : CheckerExport lratComp (List (List (BitVec 32))) (List (BitVec 32)) where
  x := ⟨"check-nested", [("problem", .list (.list .s32)), ("cert", .list .s32)], "check-nested"⟩
  mem := List.mem_cons_of_mem _ List.mem_cons_self
  enc p cs := [LVal.ofNested p, LVal.ofWords cs]
  typed p cs := by
    show LTy.checkParams [.list (.list .s32), .list .s32] [LVal.ofNested p, LVal.ofWords cs] = true
    have hw : ∀ c : List (BitVec 32), (LTy.list .s32).check (LVal.ofWords c) = true := fun c => by
      simp only [LVal.ofWords, LTy.check]
      exact checkList_map (t := .s32) (f := LVal.s32) (fun _ => rfl) c
    simp only [LTy.checkParams, LVal.ofNested, LTy.check, Bool.and_true, checkList_map hw]
    exact checkList_map (t := .s32) (f := LVal.s32) (fun _ => rfl) cs
  Goal p cs := p ∈ UnsatNested ∧ (Silmaril.Logic.SAT.Carrier.LratStream.decode cs).isSome = true

/-- **The Core obligation of `check-stream`.** -/
theorem streamExport_core : streamExport.CoreSound lratKit := by
  rintro P xs cs s t fl s' f' r ⟨⟨G, B₀, B₁, hs⟩, -⟩ hF hS hr
  change FlatHolds (memBytesOf s 1) heapBase t [.list .s32, .list .s32]
    [LVal.ofWords xs, LVal.ofWords cs] fl at hF
  rw [memBytesOf_acc hs] at hF
  obtain ⟨q₁, q₂, rfl, hq₁, hq₂, hl₁, hl₂, hin₁, hw₁, hin₂, hw₂⟩ :=
    flatHolds_read2 reads_s32 reads_s32 hF
  change Steps _ _ (invoke s (lratComp.coreAddr accI "check-stream") _) _ at hS
  rw [t_coreAddrs.2.1] at hS
  have hB := hs.size₁
  have h₁ : q₁ + 4 * xs.length ≤ B₁.size := hin₁.1
  have h₂ : q₂ + 4 * cs.length ≤ B₁.size := hin₂.1
  have hU := Silmaril.Wasm.Examples.LratAccept.checkStream_sound (pp := BitVec.ofNat 32 q₁)
    (pl := BitVec.ofNat 32 xs.length) (cp := BitVec.ofNat 32 q₂) (cl := BitVec.ofNat 32 cs.length)
    hs (by rw [toNat_ofNat hq₁, toNat_ofNat hl₁]; omega)
    (by rw [toNat_ofNat hq₂, toNat_ofNat hl₂]; omega) hS hr
  rw [toNat_ofNat hq₁, toNat_ofNat hl₁, toNat_ofNat hq₂, toNat_ofNat hl₂] at hU
  rw [show wordsAt B₁ q₁ xs.length = xs from hw₁,
    show wordsAt B₁ q₂ cs.length = cs from hw₂] at hU
  exact hU

/-- **The Core obligation of `check-nested`.** -/
theorem nestedExport_core : nestedExport.CoreSound lratKit := by
  rintro P p cs s t fl s' f' r ⟨⟨G, B₀, B₁, hs⟩, -⟩ hF hS hr
  change FlatHolds (memBytesOf s 1) heapBase t [.list (.list .s32), .list .s32]
    [LVal.ofNested p, LVal.ofWords cs] fl at hF
  rw [memBytesOf_acc hs] at hF
  obtain ⟨q₁, q₂, rfl, hq₁, hq₂, hl₁, hl₂, hin₁, hn₁, hin₂, hw₂⟩ :=
    flatHolds_read2 reads_words reads_s32 hF
  change Steps _ _ (invoke s (lratComp.coreAddr accI "check-nested") _) _ at hS
  rw [t_coreAddrs.2.2] at hS
  have hB := hs.size₁
  have h₂ : q₂ + 4 * cs.length ≤ B₁.size := hin₂.1
  have hU := Silmaril.Wasm.Examples.LratAccept.checkNested_sound (pp := BitVec.ofNat 32 q₁)
    (pl := BitVec.ofNat 32 p.length) (cp := BitVec.ofNat 32 q₂) (cl := BitVec.ofNat 32 cs.length)
    hs (by rw [toNat_ofNat hq₁, toNat_ofNat hl₁]; exact hin₁)
    (by rw [toNat_ofNat hq₂, toNat_ofNat hl₂]; omega) hS hr
  rw [toNat_ofNat hq₁, toNat_ofNat hl₁, toNat_ofNat hq₂, toNat_ofNat hl₂] at hU
  rw [show nestedAt B₁ q₁ p.length = p from hn₁,
    show wordsAt B₁ q₂ cs.length = cs from hw₂] at hU
  exact hU

/-! ## The headline results -/

/-- **An accepting call of `check-stream` is on an unsatisfiable stream.** -/
theorem checkStream_sound (P : Profile) (prof : ProfileKind) (xs cs : List (BitVec 32))
    (h : Outcome.returns (some [.bool true]) ∈ exportBehaviours prof (refHost P) () lratComp.toRef
      [] "check-stream" [(LVal.ofWords xs).toRef, (LVal.ofWords cs).toRef]) :
    xs ∈ UnsatStream :=
  (streamExport.sound lratKit streamExport_core P prof xs cs h).1

/-- **An accepting call of `check-stream` is on a decodable certificate.** -/
theorem checkStream_cert (P : Profile) (prof : ProfileKind) (xs cs : List (BitVec 32))
    (h : Outcome.returns (some [.bool true]) ∈ exportBehaviours prof (refHost P) () lratComp.toRef
      [] "check-stream" [(LVal.ofWords xs).toRef, (LVal.ofWords cs).toRef]) :
    (Silmaril.Logic.SAT.Carrier.LratStream.decode cs).isSome = true :=
  (streamExport.sound lratKit streamExport_core P prof xs cs h).2

/-- **An accepting call of `check-nested` is on an unsatisfiable formula.** -/
theorem checkNested_sound (P : Profile) (prof : ProfileKind) (p : List (List (BitVec 32)))
    (cs : List (BitVec 32))
    (h : Outcome.returns (some [.bool true]) ∈ exportBehaviours prof (refHost P) () lratComp.toRef
      [] "check-nested" [(LVal.ofNested p).toRef, (LVal.ofWords cs).toRef]) :
    p ∈ UnsatNested :=
  (nestedExport.sound lratKit nestedExport_core P prof p cs h).1

/-- **An accepting call of `check-nested` is on a decodable certificate.** -/
theorem checkNested_cert (P : Profile) (prof : ProfileKind) (p : List (List (BitVec 32)))
    (cs : List (BitVec 32))
    (h : Outcome.returns (some [.bool true]) ∈ exportBehaviours prof (refHost P) () lratComp.toRef
      [] "check-nested" [(LVal.ofNested p).toRef, (LVal.ofWords cs).toRef]) :
    (Silmaril.Logic.SAT.Carrier.LratStream.decode cs).isSome = true :=
  (nestedExport.sound lratKit nestedExport_core P prof p cs h).2

/-! ## Rejection -/

theorem decodeStream_ne_none {xs : List (BitVec 32)} (h : xs ∈ UnsatStream) :
    decodeStream xs ≠ none := by
  obtain ⟨F, hF, -⟩ := h; simp [hF]

theorem decodeNested_ne_none {p : List (List (BitVec 32))} (h : p ∈ UnsatNested) :
    decodeNested p ≠ none := by
  obtain ⟨F, hF, -⟩ := h; simp [hF]

theorem decode_ne_none {cs : List (BitVec 32)} (h : (Silmaril.Logic.SAT.Carrier.LratStream.decode cs).isSome = true) :
    Silmaril.Logic.SAT.Carrier.LratStream.decode cs ≠ none := by
  simpa [Option.isSome_iff_ne_none] using h

/-- **A malformed stream problem is never accepted.** -/
theorem checkStream_rejects_problem (P : Profile) (prof : ProfileKind) {xs : List (BitVec 32)}
    (cs : List (BitVec 32)) (hD : decodeStream xs = none) :
    Outcome.returns (some [.bool true]) ∉ exportBehaviours prof (refHost P) () lratComp.toRef
      [] "check-stream" [(LVal.ofWords xs).toRef, (LVal.ofWords cs).toRef] :=
  streamExport.rejects_none lratKit streamExport_core (f := fun xs _ => xs)
    (fun _ _ h => decodeStream_ne_none h.1) P prof (q := cs) hD

/-- **A malformed certificate is never accepted** (stream problems). -/
theorem checkStream_rejects_cert (P : Profile) (prof : ProfileKind) (xs : List (BitVec 32))
    {cs : List (BitVec 32)} (hD : Silmaril.Logic.SAT.Carrier.LratStream.decode cs = none) :
    Outcome.returns (some [.bool true]) ∉ exportBehaviours prof (refHost P) () lratComp.toRef
      [] "check-stream" [(LVal.ofWords xs).toRef, (LVal.ofWords cs).toRef] :=
  streamExport.rejects_none lratKit streamExport_core (f := fun _ cs => cs)
    (fun _ _ h => decode_ne_none h.2) P prof (p := xs) hD

/-- **A malformed nested problem is never accepted.** -/
theorem checkNested_rejects_problem (P : Profile) (prof : ProfileKind)
    {p : List (List (BitVec 32))} (cs : List (BitVec 32)) (hD : decodeNested p = none) :
    Outcome.returns (some [.bool true]) ∉ exportBehaviours prof (refHost P) () lratComp.toRef
      [] "check-nested" [(LVal.ofNested p).toRef, (LVal.ofWords cs).toRef] :=
  nestedExport.rejects_none lratKit nestedExport_core (f := fun p _ => p)
    (fun _ _ h => decodeNested_ne_none h.1) P prof (q := cs) hD

/-- **A malformed certificate is never accepted** (nested problems). -/
theorem checkNested_rejects_cert (P : Profile) (prof : ProfileKind) (p : List (List (BitVec 32)))
    {cs : List (BitVec 32)} (hD : Silmaril.Logic.SAT.Carrier.LratStream.decode cs = none) :
    Outcome.returns (some [.bool true]) ∉ exportBehaviours prof (refHost P) () lratComp.toRef
      [] "check-nested" [(LVal.ofNested p).toRef, (LVal.ofWords cs).toRef] :=
  nestedExport.rejects_none lratKit nestedExport_core (f := fun _ cs => cs)
    (fun _ _ h => decode_ne_none h.2) P prof (p := p) hD

end Silmaril.Proofs.Wasm.Examples.LratAccept.Component
