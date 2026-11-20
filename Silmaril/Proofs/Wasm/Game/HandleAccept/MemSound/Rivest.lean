module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Rivest.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Pair

/-!
# Proofs: `bpairMod` accepts only the list of the byte strings `61` and `62`

The proof of `Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Pair` with `blob` for `symbol`: in
a fixed environment `ρ` (sentinel `none`), the first `blob(16, 1)` observes `61`, so its handle
`r₁` denotes the byte string `61`; the second observes `62` (handle `r₂`); the callout of
`sexp(0, 2)` observes the little-endian handles `r₁ r₂` at `[0, 8)`, so its handle `r₃` denotes
the list, and `accept(r₃)` names it.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Rivest

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.Pair
  Silmaril.Wasm.Game.HandleAccept.MemSound.Rivest
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Pair Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post bytesAt Region)

/-- The shape of the instantiated module. -/
def bpOk : Bool :=
  match prep bpairMod with
  | some (c, st) => st.isNone && c.code.isEmpty && c.frame.module.mems == [0] &&
      exportFuncAddrs c.frame.module == [3] && c.store.mems.length == 1 &&
      (match c.store.funcs with
       | [f₀, f₁, f₂, f₃] => stubOk 0 2 f₀ && stubOk 1 2 f₁ && stubOk 2 1 f₂ &&
          fnOk [.i32, .i32] pairBody 0 0 [0, 1, 2, 3] [0] pairD f₃
       | _ => false)
  | none => false

theorem bpOk_true : bpOk = true := by decide +kernel

theorem bp_facts {c : Config Nat} {st : Option FuncIdx} (hp : prep bpairMod = some (c, st)) :
    st = none ∧ c.code = [] ∧ c.frame.module.mems = [0] ∧ exportFuncAddrs c.frame.module = [3] ∧
    c.store.mems.length = 1 ∧ ∃ f₀ f₁ f₂ f₃, c.store.funcs = [f₀, f₁, f₂, f₃] ∧
      stubOk 0 2 f₀ = true ∧ stubOk 1 2 f₁ = true ∧ stubOk 2 1 f₂ = true ∧
      fnOk [.i32, .i32] pairBody 0 0 [0, 1, 2, 3] [0] pairD f₃ = true := by
  have h := bpOk_true
  unfold bpOk at h
  rw [hp] at h
  simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none,
    List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  split at h6
  · rename_i f₀ f₁ f₂ f₃ hf
    simp only [Bool.and_eq_true] at h6
    exact ⟨f₀, f₁, f₂, f₃, hf, h6.1.1.1, h6.1.1.2, h6.1.2, h6.2⟩
  · cases h6

/-- The store invariant: the instantiated functions and one memory. -/
def bpInv (s : Store Nat) : Prop :=
  ∃ c st, prep bpairMod = some (c, st) ∧ s.funcs = c.store.funcs ∧ s.mems.length = 1

/-- The writer contract in the fixed environment `ρ`. -/
abbrev bpK (ρ : Env (BitVec 32) SymStrBytesSExp) : MemContract MemWEv :=
  writerContract {} none ρ {bpairTree} pairReply

/-- The import `blob`. -/
abbrev impBlob : Import := ⟨"sexp", "blob", .func ⟨0⟩⟩

/-- Calls of other imports than `accept` are always allowed. -/
theorem bp_pre_other {ρ : Env (BitVec 32) SymStrBytesSExp} {i : Import} {s : Store Nat}
    {args : List Val} (hi : (i.moduleName, i.name) ≠ ("sexp", "accept")) :
    (bpK ρ).pre (calloutIn i (some 0) s args) := by
  intro h hd
  rw [memAccept_eq_none hi] at hd
  cases hd

/-- A `blob` write observing the bytes `bs` returns a handle denoting the byte string. -/
theorem blob_ans {ρ : Env (BitVec 32) SymStrBytesSExp} {o : Callout} {mem : Option ByteArray}
    {bs : List UInt8} {r : BitVec 32} (hi : o.imp = ({} : MemImports).blob)
    (hb : o.bytes32 = some bs)
    (hans : ∀ y, memWrite {} o ⟨.values [.i32 r], mem⟩ = some y → (bpK ρ).ans y) :
    ρ r = some (.atom ⟨.bytes, by decide, bs⟩) := by
  have hw : memWrite {} o ⟨.values [.i32 r], mem⟩ =
      some (.write (.atom ⟨.bytes, by decide, bs⟩) [] r) := by
    have hr : replyI32 ⟨.values [.i32 r], mem⟩ = some r := rfl
    simp [memWrite, hr, hi, hb]
  rcases hans _ hw _ _ _ rfl with h | ⟨t, ht, hρ⟩
  · cases h
  · cases ht
    exact hρ

/-- **The body of `run`**, in the fixed environment `ρ`. -/
theorem bp_body {P : Profile} {ρ : Env (BitVec 32) SymStrBytesSExp} {f₀ f₁ f₂ : FuncInst Nat}
    (h0 : stubOk 0 2 f₀ = true) (h1 : stubOk 1 2 f₁ = true) (h2 : stubOk 2 1 f₂ = true)
    {F : Frame} (hFf : F.module.funcs = [0, 1, 2, 3]) (hFm : F.module.mems = [0])
    (hFl : F.locals = pairD) {s : Store Nat} {fs : List (FuncInst Nat)}
    (hfs : fs = [f₀, f₁, f₂] ++ fs.drop 3) (hsf : s.funcs = fs) (hml : s.mems.length = 1)
    (hinv : ∀ s', s'.funcs = fs → s'.mems.length = 1 → bpInv s') {Q : Post Nat}
    (hQ : BodyExits bpInv Q) :
    HWP P (memHost bpairMod (some 0) (memRoles {}) (bpK ρ)) s F
      (vals [] ++ expression pairBody) Q := by
  obtain ⟨ps₀, rs₀, hc₀, he₀, hn₀⟩ := stubOk_spec h0
  obtain ⟨ps₁, rs₁, hc₁, he₁, hn₁⟩ := stubOk_spec h1
  obtain ⟨ps₂, rs₂, hc₂, he₂, hn₂⟩ := stubOk_spec h2
  have hf0 : ∀ s' : Store Nat, s'.funcs = fs → s'.funcs[0]? = some f₀ := fun s' h => by
    rw [h, hfs]; rfl
  have hf1 : ∀ s' : Store Nat, s'.funcs = fs → s'.funcs[1]? = some f₁ := fun s' h => by
    rw [h, hfs]; rfl
  have hf2 : ∀ s' : Store Nat, s'.funcs = fs → s'.funcs[2]? = some f₂ := fun s' h => by
    rw [h, hfs]; rfl
  have htrap : ∀ s' (F' : Frame), s'.funcs = fs → s'.mems.length = 1 → Q s' F' .trap :=
    fun s' F' h h' => (hQ s' (hinv s' h h') F').2.2.1
  have hthrow : ∀ s' (F' : Frame) a, s'.funcs = fs → s'.mems.length = 1 → Q s' F' (.throw a) :=
    fun s' F' a h h' => (hQ s' (hinv s' h h') F').2.2.2 a
  unfold pairBody
  -- "a" at 16
  refine X.i32Const (us := []) ?_
  refine X.i32Const (us := [] ++ [.i32 16]) ?_
  refine X.storePack (us := []) hFm hml (htrap s F hsf hml) fun mi₀ b₀ hmi₀ hst₀ => ?_
  obtain ⟨-, hl₁, hf₁⟩ := setMem_mems (mi := { mi₀ with bytes := b₀ }) hml
  -- blob(16, 1)
  refine X.i32Const (us := []) ?_
  refine X.i32Const (us := [] ++ [.i32 16]) ?_
  refine hwp_call (us := []) (args := [.i32 16, .i32 1]) (x := ⟨0⟩) (k := 0) (fk := f₀)
    (i := impBlob) (by rw [hFf]; rfl) (hf0 _ (hf₁.trans hsf)) hc₀ he₀ (by simp [hn₀]) rfl
    (bp_pre_other (by decide)) ?_
  rintro s₂ r ⟨⟨hfs₂, hml₂⟩, hshape⟩ hans
  have hfs₂' : s₂.funcs = fs := hfs₂.trans (hf₁.trans hsf)
  have hml₂' : s₂.mems.length = 1 := hml₂.trans hl₁
  refine ⟨fun res hr => ?_, fun _ => htrap s₂ F hfs₂' hml₂',
    fun a _ => hthrow s₂ F a hfs₂' hml₂'⟩
  obtain ⟨r₁, rfl⟩ := (hshape res hr).1 (.inl rfl)
  subst hr
  have hρ₁ : ρ r₁ = some (.atom blobA) :=
    blob_ans (bs := [0x61]) rfl (by rw [bytes32_of_store hml hst₀ rfl]; decide) hans
  refine X.localSet (us := []) (x := ⟨0⟩) (by simp [hFl, pairD, Idx.toNat]) ?_
  -- "b" at 16
  refine X.i32Const (us := []) ?_
  refine X.i32Const (us := [] ++ [.i32 16]) ?_
  refine X.storePack (us := []) hFm hml₂' (htrap s₂ _ hfs₂' hml₂') fun mi₂ b₂ hmi₂ hst₂ => ?_
  obtain ⟨-, hl₃, hf₃⟩ := setMem_mems (mi := { mi₂ with bytes := b₂ }) hml₂'
  -- blob(16, 1)
  refine X.i32Const (us := []) ?_
  refine X.i32Const (us := [] ++ [.i32 16]) ?_
  refine hwp_call (us := []) (args := [.i32 16, .i32 1]) (x := ⟨0⟩) (k := 0) (fk := f₀)
    (i := impBlob) (by show F.module.funcs[_]? = _; rw [hFf]; rfl) (hf0 _ (hf₃.trans hfs₂'))
    hc₀ he₀ (by simp [hn₀]) rfl (bp_pre_other (by decide)) ?_
  rintro s₄ r ⟨⟨hfs₄, hml₄⟩, hshape⟩ hans
  have hfs₄' : s₄.funcs = fs := hfs₄.trans (hf₃.trans hfs₂')
  have hml₄' : s₄.mems.length = 1 := hml₄.trans hl₃
  refine ⟨fun res hr => ?_, fun _ => htrap s₄ _ hfs₄' hml₄',
    fun a _ => hthrow s₄ _ a hfs₄' hml₄'⟩
  obtain ⟨r₂, rfl⟩ := (hshape res hr).1 (.inl rfl)
  subst hr
  have hρ₂ : ρ r₂ = some (.atom blobB) :=
    blob_ans (bs := [0x62]) rfl (by rw [bytes32_of_store hml₂' hst₂ rfl]; decide) hans
  refine X.localSet (us := []) (x := ⟨1⟩) (by simp [Frame.setLocal, hFl, pairD, Idx.toNat]) ?_
  -- the handles at 0 and 4
  refine X.i32Const (us := []) ?_
  refine X.localGet (us := [] ++ [.i32 0]) (v := .i32 r₁) ?_ ?_
  · simp [Frame.local?, Frame.setLocal, hFl, pairD, Idx.toNat]
  refine X.store32 (us := []) hFm hml₄' (htrap s₄ _ hfs₄' hml₄') fun mi₄ b₄ hmi₄ hst₄ => ?_
  obtain ⟨hm₅, hl₅, hf₅⟩ := setMem_mems (mi := { mi₄ with bytes := b₄ }) hml₄'
  refine X.i32Const (us := []) ?_
  refine X.localGet (us := [] ++ [.i32 4]) (v := .i32 r₂) ?_ ?_
  · simp [Frame.local?, Frame.setLocal, hFl, pairD, Idx.toNat]
  refine X.store32 (us := []) hFm hl₅ (htrap _ _ (hf₅.trans hfs₄') hl₅)
    fun mi₅ b₅ hmi₅ hst₅ => ?_
  obtain rfl : mi₅ = { mi₄ with bytes := b₄ } := Option.some.inj (hmi₅.symm.trans hm₅)
  obtain ⟨-, hl₆, hf₆⟩ := setMem_mems (mi := { mi₄ with bytes := b₅ }) hl₅
  have hfs₆ : (((s₄.setMem 0 { mi₄ with bytes := b₄ }).setMem 0 { mi₄ with bytes := b₅ })).funcs
      = fs := hf₆.trans (hf₅.trans hfs₄')
  -- sexp(0, 2)
  have h₀ : bytesAt b₅ ⟨0, 4⟩ = (Memory.encodeLE 4 r₁.toNat).data.toList := by
    rw [Silmaril.Wasm.Logic.Core.bytesAt_store_disjoint hst₅ (.inr (by decide))]
    exact bytes_of_store32 hst₄
  have h₄ : bytesAt b₅ ⟨4, 4⟩ = (Memory.encodeLE 4 r₂.toNat).data.toList :=
    bytes_of_store32 hst₅
  have hh : handles32 (calloutIn impSexp (some 0)
      ((s₄.setMem 0 { mi₄ with bytes := b₄ }).setMem 0 { mi₄ with bytes := b₅ })
      [.i32 0, .i32 2]) = some [r₁, r₂] :=
    handles32_pair (memOf_setMem hl₅) (by
      have := store_inBounds hst₅; simp [effAddr, IntType.width] at this ⊢; omega)
      h₀ h₄
  refine X.i32Const (us := []) ?_
  refine X.i32Const (us := [] ++ [.i32 0]) ?_
  refine hwp_call (us := []) (args := [.i32 0, .i32 2]) (x := ⟨1⟩) (k := 1) (fk := f₁)
    (i := impSexp) (by show F.module.funcs[_]? = _; rw [hFf]; rfl) (hf1 _ hfs₆) hc₁ he₁
    (by simp [hn₁]) rfl (bp_pre_other (by decide)) ?_
  rintro s₇ r ⟨⟨hfs₇, hml₇⟩, hshape⟩ hans
  have hfs₇' : s₇.funcs = fs := hfs₇.trans hfs₆
  have hml₇' : s₇.mems.length = 1 := hml₇.trans hl₆
  refine ⟨fun res hr => ?_, fun _ => htrap s₇ _ hfs₇' hml₇',
    fun a _ => hthrow s₇ _ a hfs₇' hml₇'⟩
  obtain ⟨r₃, rfl⟩ := (hshape res hr).1 (.inr rfl)
  subst hr
  have hρ₃ : ρ r₃ = some bpairTree := by
    have hw := memWrite_sexp_eq (ix := {}) (w := ⟨.values [.i32 r₃], memOf (some 0) s₇⟩)
      (r := r₃) rfl (by show ("sexp", "sexp") ≠ ("sexp", "symbol"); decide)
      (by show ("sexp", "sexp") ≠ ("sexp", "string"); decide)
      (by show ("sexp", "sexp") ≠ ("sexp", "blob"); decide) hh rfl
    rcases hans _ hw _ _ _ rfl with h | ⟨t, ht, hρ⟩
    · cases h
    · simp [Writer.built, Env.lookupAll, hρ₁, hρ₂, sexpW] at ht
      rw [hρ, ← ht]
      rfl
  -- accept(r₃)
  refine hwp_call (us := []) (args := [.i32 r₃]) (x := ⟨2⟩) (k := 2) (fk := f₂)
    (i := impAcc) (by show F.module.funcs[_]? = _; rw [hFf]; rfl) (hf2 _ hfs₇') hc₂ he₂
    (by simp [hn₂]) rfl ?_ ?_
  · intro h hd t ht
    obtain rfl := memAccept_inv rfl hd
    rw [hρ₃] at ht
    cases ht
    rfl
  rintro s₈ r ⟨⟨hfs₈, hml₈⟩, hshape⟩ -
  have hfs₈' : s₈.funcs = fs := hfs₈.trans hfs₇'
  have hml₈' : s₈.mems.length = 1 := hml₈.trans hml₇'
  refine ⟨fun res hr => ?_, fun _ => htrap s₈ _ hfs₈' hml₈',
    fun a _ => hthrow s₈ _ a hfs₈' hml₈'⟩
  obtain rfl := (hshape res hr).2 rfl
  exact X.done (hQ s₈ (hinv s₈ hfs₈' hml₈') _).1

/-- **`bpairMod` meets the writer contract** in every fixed environment, for every profile. -/
theorem bp_sat (P : Profile) (ρ : Env (BitVec 32) SymStrBytesSExp) :
    MemSat P bpairMod 0 (memRoles {}) (bpK ρ) bpInv := by
  intro mt Is c₀ hI
  obtain ⟨c, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, hexp, hml, f₀, f₁, f₂, f₃, hf, h0, h1, h2, h3⟩ := bp_facts hp
  have hmem : (c.withStart none).frame.module.mems[0]? = some 0 := by
    simp [Config.withStart, hmems]
  rw [hmem]
  refine ⟨fun n => Safe.of_exits (o := .normal []) (by simp [Config.withStart, hcode]; rfl)
    (fun _ _ => ⟨c, none, hp, rfl, hml⟩), ?_⟩
  intro a ha
  rw [← haddr, hexp] at ha
  obtain rfl : a = 3 := by simpa using ha
  obtain ⟨code, ps, rs, hcode3, hloc, hbody, he, hps, hrs, hfuncs, hmems3, hD⟩ := fnOk_spec h3
  have hinv : ∀ s', s'.funcs = c.store.funcs → s'.mems.length = 1 → bpInv s' :=
    fun s' h h' => ⟨c, none, hp, h, h'⟩
  have hfi : ∀ s, bpInv s → s.funcs = c.store.funcs := by
    rintro s ⟨c', st', hp', hfs, _⟩
    have hcc : c' = c := (Prod.mk.inj (Option.some.inj (hp'.symm.trans hp))).1
    rw [hfs, hcc]
  refine export_valid (fi := f₃) (fun s hs => by rw [hfi s hs, hf]; rfl) hcode3 he hrs ?_
  intro s args hs hok Q hQ
  have hargs : args = [] := by
    have := args_length (by rw [hfi s hs, hf]; rfl) he hok
    rw [hps] at this
    exact List.eq_nil_of_length_eq_zero this
  subst hargs
  rw [hbody, hloc]
  have hml' : s.mems.length = 1 := by obtain ⟨_, _, _, _, h⟩ := hs; exact h
  exact bp_body h0 h1 h2 (by simp [Frame.forCall, hfuncs]) (by simp [Frame.forCall, hmems3])
    (by simp [Frame.forCall, hD]) (fs := c.store.funcs) (by rw [hf]; rfl) (hfi s hs)
    hml' hinv hQ

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Rivest
