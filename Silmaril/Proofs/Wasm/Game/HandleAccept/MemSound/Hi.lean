module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Hi.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Rules

/-!
# Proofs: `hiMod` writes only the symbol `hi`

The instantiated module is checked by kernel evaluation (`hiOk`). Its store invariant `hiInv`:
the functions of the instantiated store and one memory. `hi_body` is the every-run proof of the
body of `run` under the most general host of the contract `closedContract {} {atom hi} hiReply`:
after `i32.store16` the memory holds `68 69` at `[0, 2)` (or the store trapped), so the callout
of `symbol(0, 2)` reads the UTF-8 text `hi`, and every write it decodes to is the atom `hi`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Hi

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)

/-- The shape of the instantiated module. -/
def hiOk : Bool :=
  match prep hiMod with
  | some (c, st) => st.isNone && c.code.isEmpty && c.frame.module.mems == [0] &&
      exportFuncAddrs c.frame.module == [2] && c.store.mems.length == 1 &&
      (match c.store.funcs with
       | [f₀, f₁, f₂] => stubOk 0 2 f₀ && stubOk 1 1 f₁ &&
          fnOk [] hiBody 0 0 [0, 1, 2] [0] [] f₂
       | _ => false)
  | none => false

theorem hiOk_true : hiOk = true := by decide +kernel

theorem hi_facts {c : Config Nat} {st : Option FuncIdx} (hp : prep hiMod = some (c, st)) :
    st = none ∧ c.code = [] ∧ c.frame.module.mems = [0] ∧ exportFuncAddrs c.frame.module = [2] ∧
    c.store.mems.length = 1 ∧ ∃ f₀ f₁ f₂, c.store.funcs = [f₀, f₁, f₂] ∧ stubOk 0 2 f₀ = true ∧
      stubOk 1 1 f₁ = true ∧ fnOk [] hiBody 0 0 [0, 1, 2] [0] [] f₂ = true := by
  have h := hiOk_true
  unfold hiOk at h
  rw [hp] at h
  simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none,
    List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  split at h6
  · rename_i f₀ f₁ f₂ hf
    simp only [Bool.and_eq_true] at h6
    exact ⟨f₀, f₁, f₂, hf, h6.1.1, h6.1.2, h6.2⟩
  · cases h6

/-- The store invariant: the instantiated functions and one memory. -/
def hiInv (s : Store Nat) : Prop :=
  ∃ c st, prep hiMod = some (c, st) ∧ s.funcs = c.store.funcs ∧ s.mems.length = 1

/-- The contract. -/
abbrev hiK : MemContract MemWEv := closedContract {} {.atom hiAtom} hiReply

theorem utf8_hi : utf8? [0x68, 0x69] = some "hi" := by decide +kernel

/-- The callout of `symbol(0, 2)` after the store reads `hi`. -/
theorem hi_pre {s : Store Nat} {mi : MemInst} {b : ByteArray}
    (hst : Memory.store mi.bytes (effAddr (0 : BitVec 32).toNat ⟨0, 0⟩)
      (count := PackSize.i16.width / 8) ((0x6968 : BitVec 32).setWidth _) = some b)
    (hmem : memOf (some 0) s = some b) :
    hiK.pre (calloutIn ⟨"sexp", "symbol", .func ⟨0⟩⟩ (some 0) s [.i32 0, .i32 2]) := by
  intro w op args r hw
  have hseg := segment_of_store hst (calloutIn ⟨"sexp", "symbol", .func ⟨0⟩⟩ (some 0) s
    [.i32 0, .i32 2]) hmem
  have hb : (calloutIn ⟨"sexp", "symbol", .func ⟨0⟩⟩ (some 0) s [.i32 0, .i32 2]).bytes32 =
      some [0x68, 0x69] := by
    rw [Callout.bytes32]
    simp only [calloutIn, Callout.args2, Callout.i32?, Val.i32, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def]
    have e : (Memory.encodeLE (PackSize.i16.width / 8)
        ((0x6968 : BitVec 32).setWidth (8 * (PackSize.i16.width / 8))).toNat).data.toList =
        [0x68, 0x69] := by decide
    rw [← e, ← hseg]
    rfl
  obtain ⟨str, hu, rfl, rfl⟩ := memWrite_symbol rfl hb hw
  rw [utf8_hi] at hu
  cases hu
  intro ts y hl hbuild _
  cases ts with
  | nil => cases hbuild; rfl
  | cons _ _ => cases hl

/-- No write is decoded from a call of `accept`. -/
theorem accept_pre {s : Store Nat} {args : List Val} :
    hiK.pre (calloutIn ⟨"sexp", "accept", .func ⟨1⟩⟩ (some 0) s args) := by
  intro w op args' r hw
  rw [memWrite_eq_none (by show ("sexp", "accept") ≠ ("sexp", "symbol"); decide)
    (by show ("sexp", "accept") ≠ ("sexp", "string"); decide)
    (by show ("sexp", "accept") ≠ ("sexp", "blob"); decide)
    (by show ("sexp", "accept") ≠ ("sexp", "sexp"); decide)] at hw
  cases hw

/-- **The body of `run`.** -/
theorem hi_body {P : Profile} {c : Config Nat} {st : Option FuncIdx}
    (hp : prep hiMod = some (c, st)) {f₀ f₁ f₂ : FuncInst Nat}
    (hf : c.store.funcs = [f₀, f₁, f₂]) (h0 : stubOk 0 2 f₀ = true) (h1 : stubOk 1 1 f₁ = true)
    {F : Frame} (hFf : F.module.funcs = [0, 1, 2]) (hFm : F.module.mems = [0]) {s : Store Nat}
    (hs : hiInv s) {Q : Post Nat} (hQ : BodyExits hiInv Q) :
    HWP P (memHost hiMod (some 0) (memRoles {}) hiK) s F (vals [] ++ expression hiBody) Q := by
  obtain ⟨c', st', hp', hsf, hml⟩ := hs
  have hcc : c' = c := (Prod.mk.inj (Option.some.inj (hp'.symm.trans hp))).1
  rw [hcc, hf] at hsf
  have hs : hiInv s := ⟨c, st, hp, by rw [hsf, hf], hml⟩
  have hinv : ∀ s', s'.funcs = s.funcs → s'.mems.length = s.mems.length → hiInv s' :=
    fun s' h1 h2 => ⟨c, st, hp, by rw [h1, hsf, hf], by rw [h2, hml]⟩
  obtain ⟨mi, hmi⟩ : ∃ mi, s.mems[0]? = some mi :=
    ⟨s.mems[0]'(by omega), List.getElem?_eq_getElem _⟩
  have hm : s.mem? F ⟨0⟩ = some (0, mi) := by
    simp only [Store.mem?, hFm]
    rw [show ([0] : List Nat)[(⟨0⟩ : MemIdx).toNat]? = some 0 from rfl]
    simp [hmi]
  obtain ⟨ps₀, rs₀, hc₀, he₀, hn₀⟩ := stubOk_spec h0
  obtain ⟨ps₁, rs₁, hc₁, he₁, hn₁⟩ := stubOk_spec h1
  unfold hiBody
  refine X.i32Const (us := []) ?_
  refine X.i32Const (us := [] ++ [.i32 0]) ?_
  rcases hst : Memory.store mi.bytes (effAddr (0 : BitVec 32).toNat ⟨0, 0⟩)
    (count := PackSize.i16.width / 8) ((0x6968 : BitVec 32).setWidth _) with _ | b
  · exact Wp.intStorePack_oob (m := .part) (a := .i32) (i := 0) (t := .i32) (c := 0x6968)
      (us := []) hm (store_none_lt hst) ((hQ s hs F).2.2.1)
  refine Wp.intStorePack (m := .part) (a := .i32) (i := 0) (t := .i32) (c := 0x6968)
    (us := []) hm hst ?_
  set s₁ := s.setMem 0 { mi with bytes := b } with hs₁
  have hf₁ : s₁.funcs = [f₀, f₁, f₂] := hsf
  have hl₁ : s₁.mems.length = s.mems.length := by simp [hs₁, Store.setMem]
  have hmem : memOf (some 0) s₁ = some b := by
    simp [hs₁, memOf, Store.setMem, List.getElem?_set, hml]
  show HWP _ _ s₁ F (vals [] ++ expression [.intConst .i32 0, .intConst .i32 2, .call ⟨0⟩,
    .call ⟨1⟩]) Q
  refine X.i32Const (us := []) ?_
  refine X.i32Const (us := [] ++ [.i32 0]) ?_
  refine hwp_call (us := []) (args := [.i32 0, .i32 2]) (x := ⟨0⟩) (k := 0) (fk := f₀)
    (i := ⟨"sexp", "symbol", .func ⟨0⟩⟩) (by rw [hFf]; rfl) (by simp [hf₁]) hc₀ he₀
    (by simp [hn₀]) rfl (hi_pre hst hmem) ?_
  rintro s' r ⟨⟨hfs', hml'⟩, hshape⟩ -
  have hs' : hiInv s' := hinv s' (by rw [hfs']; rfl) (by rw [hml', hl₁])
  refine ⟨fun res hr => ?_, fun _ => (hQ s' hs' F).2.2.1, fun a _ => (hQ s' hs' F).2.2.2 a⟩
  obtain ⟨v, rfl⟩ := (hshape res hr).1 rfl
  refine hwp_call (us := []) (args := [.i32 v]) (x := ⟨1⟩) (k := 1) (fk := f₁)
    (i := ⟨"sexp", "accept", .func ⟨1⟩⟩) (by rw [hFf]; rfl) (by rw [hfs', hf₁]; rfl) hc₁ he₁
    (by simp [hn₁]) rfl accept_pre ?_
  rintro s'' r' ⟨⟨hfs'', hml''⟩, hshape'⟩ -
  have hs'' : hiInv s'' := hinv s'' (by rw [hfs'', hfs']; rfl) (by rw [hml'', hml', hl₁])
  refine ⟨fun res hr => ?_, fun _ => (hQ s'' hs'' F).2.2.1, fun a _ => (hQ s'' hs'' F).2.2.2 a⟩
  obtain rfl := (hshape' res hr).2 rfl
  exact X.done (hQ s'' hs'' F).1

/-- **`hiMod` meets its contract**, for every profile. -/
theorem hi_sat (P : Profile) : MemSat P hiMod 0 (memRoles {}) hiK hiInv := by
  intro mt Is c₀ hI
  obtain ⟨c, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, hexp, hml, f₀, f₁, f₂, hf, h0, h1, h2⟩ := hi_facts hp
  have hmem : (c.withStart none).frame.module.mems[0]? = some 0 := by
    simp [Config.withStart, hmems]
  rw [hmem]
  refine ⟨fun n => Safe.of_exits (o := .normal []) (by simp [Config.withStart, hcode]; rfl)
    (fun _ _ => ⟨c, none, hp, rfl, hml⟩), ?_⟩
  intro a ha
  rw [← haddr, hexp] at ha
  obtain rfl : a = 2 := by simpa using ha
  obtain ⟨code, ps, rs, hcode2, hloc, hbody, he, -, hrs, hfuncs, hmems2, -⟩ := fnOk_spec h2
  refine export_valid (fi := f₂) (fun s hs => ?_) hcode2 he hrs ?_
  · obtain ⟨c', st', hp', hfs, _⟩ := hs
    have hcc : c' = c := (Prod.mk.inj (Option.some.inj (hp'.symm.trans hp))).1
    rw [hfs, hcc, hf]
    rfl
  · intro s args hs _ Q hQ
    rw [hbody]
    exact hi_body hp hf h0 h1 (by simp [Frame.forCall, hfuncs]) (by simp [Frame.forCall, hmems2])
      hs hQ

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Hi
