module

public import Silmaril.Wasm.Game.Accept.Defs
public import Silmaril.Formats.Accept.Thms

/-! # Inputs accepted by a core Wasm module: theorems

* Acceptance is read off the callouts: callout-equivalent modules accept the same values for
  every decoder (`accepted_eq_of_calloutEquiv`), and callout equivalence is *exactly* the
  equivalence preserving every decoder's accepted set (`calloutEquiv_iff`).
* More environments, more callouts (`callouts_mono`, `accepted_mono`).
* Sessions contain the product runs (`Session.of_steps`) and host-free Core runs
  (`Session.of_core_steps`).
* The decoders: `bytes32` reads exactly the segment `[ptr, ptr + len)` (`bytes32_eq_some_iff`,
  `length_of_segment`, `getElem?_of_segment`), which is the contiguous elementwise read the
  canonical ABI's `list<u8>` load performs (elements of size and alignment `1`).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.Accept

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game Silmaril.Formats.Accept

variable {P : Profile} {Envs Envs' : Store Nat → SEnv UImp → Prop} {k : Nat} {m m' : Module}

theorem mem_accepted {α : Type} {dec : Callout → Option α} {imp : String × String} {a : α} :
    a ∈ accepted dec P Envs k imp m ↔ ∃ o ∈ Callouts P Envs k m, o.imp = imp ∧ dec o = some a :=
  Iff.rfl

/-- **Callout-equivalent modules accept the same values**, for every decoder and import. -/
theorem accepted_eq_of_calloutEquiv (h : CalloutEquiv P Envs k m m') {α : Type}
    (dec : Callout → Option α) (imp : String × String) :
    accepted dec P Envs k imp m = accepted dec P Envs k imp m' := by
  unfold accepted; rw [h]

/-- **Callout equivalence is the coarsest equivalence preserving acceptance**: two modules have
the same callouts iff every decoder accepts the same values through every import. -/
theorem calloutEquiv_iff : CalloutEquiv P Envs k m m' ↔
    ∀ (α : Type) (dec : Callout → Option α) (imp : String × String),
      accepted dec P Envs k imp m = accepted dec P Envs k imp m' := by
  refine ⟨fun h _ dec imp => accepted_eq_of_calloutEquiv h dec imp, fun h => ?_⟩
  ext o
  have e := congrArg (o ∈ ·) (h Callout some o.imp)
  simp only [mem_accepted, Option.some.injEq, eq_iff_iff] at e
  exact ⟨fun ho => (e.1 ⟨o, ho, rfl, rfl⟩).elim fun _ ⟨h₁, _, h₂⟩ => h₂ ▸ h₁,
    fun ho => (e.2 ⟨o, ho, rfl, rfl⟩).elim fun _ ⟨h₁, _, h₂⟩ => h₂ ▸ h₁⟩

theorem calloutEquiv_refl : CalloutEquiv P Envs k m m := rfl

theorem CalloutEquiv.symm (h : CalloutEquiv P Envs k m m') : CalloutEquiv P Envs k m' m := Eq.symm h

theorem CalloutEquiv.trans {m'' : Module} (h₁ : CalloutEquiv P Envs k m m')
    (h₂ : CalloutEquiv P Envs k m' m'') : CalloutEquiv P Envs k m m'' := Eq.trans h₁ h₂

/-- The byte languages of callout-equivalent modules are equal. -/
theorem bytesLang_eq_of_calloutEquiv (h : CalloutEquiv P UEnvOk 0 m m') (imp : String × String) :
    bytesLang P m imp = bytesLang P m' imp :=
  accepted_eq_of_calloutEquiv h _ imp

/-- More admitted environments, more callouts. -/
theorem callouts_mono (h : ∀ s L, Envs s L → Envs' s L) :
    Callouts P Envs k m ⊆ Callouts P Envs' k m :=
  fun _ ⟨mt, I, c₀, hI, L, q₀, hL, rest⟩ => ⟨mt, I, c₀, hI, L, q₀, h _ _ hL, rest⟩

/-- More admitted environments, more accepted values. -/
theorem accepted_mono (h : ∀ s L, Envs s L → Envs' s L) {α : Type} (dec : Callout → Option α)
    (imp : String × String) : accepted dec P Envs k imp m ⊆ accepted dec P Envs' k imp m :=
  fun _ ⟨o, ho, hi, hd⟩ => ⟨o, callouts_mono h ho, hi, hd⟩

/-! ## Sessions -/

/-- Sessions are closed under runs of the product semantics. -/
theorem Session.of_steps {L : SEnv UImp} {c₀ : Config Nat} {q₀ : L.S} {addrs : List Nat}
    {b : Bool} {x y : Config Nat × L.S} (h : Session P L c₀ q₀ addrs b x)
    (hs : USteps P L x y) : Session P L c₀ q₀ addrs b y := by
  induction hs with
  | refl => exact h
  | tail _ st ih => exact .step ih st

/-- Sessions are closed under host-free Core runs. -/
theorem Session.of_core_steps {L : SEnv UImp} {c₀ : Config Nat} {q₀ : L.S} {addrs : List Nat}
    {b : Bool} {c c' : Config Nat} {q : L.S} (h : Session P L c₀ q₀ addrs b (c, q))
    (hs : Steps P (fun _ _ _ _ => False) c c') : Session P L c₀ q₀ addrs b (c', q) := by
  induction hs with
  | refl => exact h
  | tail _ st ih => exact .step ih (.internal st)

/-! ## Decoders -/

namespace Callout

theorem i32?_eq_some_iff {v : Val} {x : BitVec 32} : i32? v = some x ↔ v = .num ⟨.int .i32, x⟩ := by
  constructor
  · intro h
    unfold i32? at h
    split at h
    · cases h; rfl
    · cases h
  · rintro rfl; rfl

theorem i64?_eq_some_iff {v : Val} {x : BitVec 64} : i64? v = some x ↔ v = .num ⟨.int .i64, x⟩ := by
  constructor
  · intro h
    unfold i64? at h
    split at h
    · cases h; rfl
    · cases h
  · rintro rfl; rfl

theorem args2_eq_some_iff {β : Type} {f : Val → Option β} {vs : List Val} {x y : β} :
    args2 f vs = some (x, y) ↔ ∃ a b, vs = [a, b] ∧ f a = some x ∧ f b = some y := by
  constructor
  · intro h
    match vs, h with
    | [a, b], h =>
      simp only [args2, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨x', hx, y', hy, rfl, rfl⟩ := h
      exact ⟨a, b, rfl, hx, hy⟩
  · rintro ⟨a, b, rfl, ha, hb⟩
    simp [args2, ha, hb]

/-- The arguments of `bytes32` are two `i32` values. -/
theorem args2_i32?_eq_some_iff {vs : List Val} {p n : BitVec 32} :
    args2 i32? vs = some (p, n) ↔ vs = [.num ⟨.int .i32, p⟩, .num ⟨.int .i32, n⟩] := by
  rw [args2_eq_some_iff]
  constructor
  · rintro ⟨a, b, rfl, ha, hb⟩
    rw [i32?_eq_some_iff.1 ha, i32?_eq_some_iff.1 hb]
  · rintro rfl
    exact ⟨_, _, rfl, rfl, rfl⟩

theorem segment_eq_some_iff {o : Callout} {ptr len : Nat} {bs : List UInt8} :
    o.segment ptr len = some bs ↔ ∃ mem b, o.mem = some mem ∧
      Execution.Memory.readBytes mem ptr len = some b ∧ b.data.toList = bs := by
  simp only [segment, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.map_eq_some_iff]
  constructor
  · rintro ⟨mem, hm, b, hb, rfl⟩; exact ⟨mem, b, hm, hb, rfl⟩
  · rintro ⟨mem, b, hm, hb, rfl⟩; exact ⟨mem, hm, b, hb, rfl⟩

theorem bytes32_eq_some_iff {o : Callout} {bs : List UInt8} :
    o.bytes32 = some bs ↔ ∃ p n : BitVec 32,
      o.args = [.num ⟨.int .i32, p⟩, .num ⟨.int .i32, n⟩] ∧ o.segment p.toNat n.toNat = some bs := by
  simp only [bytes32, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists]
  constructor
  · rintro ⟨p, n, ha, hs⟩; exact ⟨p, n, args2_i32?_eq_some_iff.1 ha, hs⟩
  · rintro ⟨p, n, ha, hs⟩; exact ⟨p, n, args2_i32?_eq_some_iff.2 ha, hs⟩

/-- A segment of `len` bytes has `len` bytes. -/
theorem length_of_segment {o : Callout} {ptr len : Nat} {bs : List UInt8}
    (h : o.segment ptr len = some bs) : bs.length = len := by
  obtain ⟨mem, b, -, hb, rfl⟩ := segment_eq_some_iff.1 h
  rw [Array.length_toList]
  exact Execution.Memory.readBytes_size mem b _ _ hb

/-- **The observed bytes are the memory segment, elementwise**: byte `i < len` is the memory's
byte at `ptr + i`. The canonical ABI loads a `list<u8>` the same way: element `i` of a list at
`ptr` with element size `1` is the byte at `ptr + i` (`Canon.loadListFromValidRangeWith`). -/
theorem getElem?_of_segment {o : Callout} {ptr len : Nat} {bs : List UInt8} {mem : ByteArray}
    (h : o.segment ptr len = some bs) (hm : o.mem = some mem) {i : Nat} (hi : i < len) :
    bs[i]? = mem.data.toList[ptr + i]? := by
  obtain ⟨mem', b, hm', hb, rfl⟩ := segment_eq_some_iff.1 h
  rw [hm] at hm'
  cases hm'
  obtain ⟨hbound, rfl⟩ := (Execution.Memory.readBytes_eq_some_iff _ _ _ _).1 hb
  have hsz : mem.size = mem.data.size := rfl
  rw [Array.getElem?_toList, Array.getElem?_toList, ByteArray.data_extract, Array.getElem?_extract,
    ite_eq_left (by omega)]

end Callout

end Silmaril.Wasm.Game.Accept
