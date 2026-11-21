module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Tab.Cons
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.LivePair

/-!
# Proofs: atom tables, the two-element n-ary list

* `tabPair_sat`: in a fixed environment `ρ` (no sentinel), `pairAtomMod name` meets the writer
  contract with `L = {(a b)}` through a table decoding `61` to `a` and `62` to `b` (the proof of
  `pair_sat` with the atom import and its decoder abstracted): the two calls of `<name>(16, 1)`
  return handles denoting `a` and `b`; the callout of `sexp(0, 2)` observes them at `[0, 8)`;
* `tabPair_traces`: the traced session against the counting host `countEnv pairOut`;
* `tabPair_sound`, `tabPair_live`.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Tab

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game
  Silmaril.Wasm.Game.Accept Silmaril.Wasm.Game.IOAccept Silmaril.Accept Silmaril.Accept.Handle
  Silmaril.Accept.IO Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.Pair
  Silmaril.Wasm.Game.HandleAccept.MemSound.Cons
  Silmaril.Wasm.Game.HandleAccept.MemSound.Live Silmaril.Wasm.Game.HandleAccept.MemSound.Tab
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Pair
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.Pair Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post bytesAt Region)

variable {α : Type} {T : AtomTable α} {name : String} {dec : List UInt8 → Option α} {a b : α}

/-- **The facts of the pair example**: `name` is an example import, `T` decodes its bytes `61`
to `a` and `62` to `b` by `dec`, and names neither `sexp` nor `accept`. -/
structure PairSpec (T : AtomTable α) (name : String) (dec : List UInt8 → Option α) (a b : α) :
    Prop where
  hn : name ∈ atomNames
  hT : T.lookup ("sexp", name) = some (.seg dec)
  ha : dec [0x61] = some a
  hb : dec [0x62] = some b
  hsexp : T.lookup ("sexp", "sexp") = none
  hacc : T.lookup ("sexp", "accept") = none

/-! ## The decoder -/

theorem tabWrite_isWrite {o : Callout} {w : HostReply} {e : WEv (SxOp α) (BitVec 32)}
    (h : tabWrite T {} o w = some e) : ∃ op args r, e = .write op args r := by
  unfold tabWrite at h
  rcases hr : replyI32 w with _ | r
  · simp [hr] at h
  · simp only [hr] at h
    split at h
    · simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨_, _, _, _, _, _, rfl⟩ := h
      exact ⟨_, _, _, rfl⟩
    · split_ifs at h
      · simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.some.injEq] at h
        aesop
      · simp at h

theorem tabWrite_bytes_eq {imp : String × String} {bs : List UInt8} {x : α}
    (hT : T.lookup imp = some (.seg dec)) (hd : dec bs = some x) {o : Callout} {q : BitVec 32}
    {mem : Option ByteArray} (hi : o.imp = imp) (hbs : o.bytes32 = some bs) :
    tabWrite T {} o ⟨.values [.i32 q], mem⟩ = some (.write (.atom x) [] q) := by
  have hr : replyI32 ⟨.values [.i32 q], mem⟩ = some q := rfl
  simp [tabWrite, hr, hi, hT, AtomDec.decode, hbs, hd]

theorem tabWrite_sexp_eq (hs : T.lookup ("sexp", "sexp") = none) {o : Callout} {w : HostReply}
    {hs' : List (BitVec 32)} {r : BitVec 32} (hi : o.imp = ("sexp", "sexp"))
    (hh : handles32 o = some hs') (hr : replyI32 w = some r) :
    tabWrite T {} o w = some (.write .list hs' r) := by
  unfold tabWrite
  simp [hr, hi, hs, hh]

theorem tabAccept_inv {Op : Type} {o : Callout} {h h' : BitVec 32}
    (ha : o.args = [.i32 h]) (hd : tabAccept (Op := Op) {} o = some (.accept h')) : h' = h := by
  unfold tabAccept at hd
  split at hd
  · simp [ha, Callout.args1, Callout.i32?, Val.i32] at hd
    exact hd.symm
  · cases hd

/-! ## The instantiated module -/

/-- The shape of the instantiated module. -/
def pairAtomOk (name : String) : Bool :=
  match prep (pairAtomMod name) with
  | some (c, st) => st.isNone && c.code.isEmpty && c.frame.module.mems == [0] &&
      exportFuncAddrs c.frame.module == [3] && c.store.mems.length == 1 &&
      (match c.store.funcs with
       | [f₀, f₁, f₂, f₃] => stubOk 0 2 f₀ && stubOk 1 2 f₁ && stubOk 2 1 f₂ &&
          fnOk [.i32, .i32] pairBody 0 0 [0, 1, 2, 3] [0] pairD f₃
       | _ => false)
  | none => false

theorem pairAtomOk_of (hn : name ∈ atomNames) : pairAtomOk name = true := by
  simp only [atomNames, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl <;> decide +kernel

theorem pairAtomSpec_of (hn : name ∈ atomNames) :
    (Silmaril.Wasm.Verify.specInstance? (pairAtomMod name)).isSome = true := by
  simp only [atomNames, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl <;> decide +kernel

theorem pairAtomMem_of (hn : name ∈ atomNames) : memSizes (pairAtomMod name) = [65536] := by
  simp only [atomNames, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl <;> decide +kernel

theorem pairAtom_facts (hn : name ∈ atomNames) {c : Config Nat} {st : Option FuncIdx}
    (hp : prep (pairAtomMod name) = some (c, st)) :
    st = none ∧ c.code = [] ∧ c.frame.module.mems = [0] ∧ exportFuncAddrs c.frame.module = [3] ∧
    c.store.mems.length = 1 ∧ ∃ f₀ f₁ f₂ f₃, c.store.funcs = [f₀, f₁, f₂, f₃] ∧
      stubOk 0 2 f₀ = true ∧ stubOk 1 2 f₁ = true ∧ stubOk 2 1 f₂ = true ∧
      fnOk [.i32, .i32] pairBody 0 0 [0, 1, 2, 3] [0] pairD f₃ = true := by
  have h := pairAtomOk_of hn
  unfold pairAtomOk at h
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
def pairAtomInv (name : String) (s : Store Nat) : Prop :=
  ∃ c st, prep (pairAtomMod name) = some (c, st) ∧ s.funcs = c.store.funcs ∧ s.mems.length = 1

/-- The writer contract in the fixed environment `ρ`. -/
abbrev tabPairK (T : AtomTable α) (a b : α) (ρ : Env (BitVec 32) (SExp α)) :
    MemContract (WEv (SxOp α) (BitVec 32)) :=
  roleWriterContract (tabRoles T {}) (sexpW α) none ρ {SExp.ofList [.atom a, .atom b]}
    pairReply

/-- Calls of other imports than `accept` are always allowed. -/
theorem tab_pre_other' {ρ : Env (BitVec 32) (SExp α)} {i : Import} {s : Store Nat}
    {args : List Val} (hi : (i.moduleName, i.name) ≠ ("sexp", "accept")) :
    (tabPairK T a b ρ).pre (calloutIn i (some 0) s args) := by
  intro h hd
  change tabAccept {} _ = _ at hd
  rw [tabAccept_none hi] at hd
  cases hd

/-- An atom write observing `bs` returns a handle denoting the atom `dec` decodes. -/
theorem tab_atom_ans {ρ : Env (BitVec 32) (SExp α)} {imp : String × String} {bs : List UInt8}
    {x : α} (hT : T.lookup imp = some (.seg dec)) (hd : dec bs = some x) {o : Callout}
    {mem : Option ByteArray} {r : BitVec 32} (hi : o.imp = imp) (hbs : o.bytes32 = some bs)
    (hans : ∀ y, tabWrite T {} o ⟨.values [.i32 r], mem⟩ = some y → (tabPairK T a b ρ).ans y) :
    ρ r = some (.atom x) := by
  rcases hans _ (tabWrite_bytes_eq hT hd hi hbs) _ _ _ rfl with h | ⟨t, ht, hρ⟩
  · cases h
  · cases ht
    exact hρ

/-- **The body of `run`**, in the fixed environment `ρ`. -/
theorem tabPair_body {P : Profile} (S : PairSpec T name dec a b) {ρ : Env (BitVec 32) (SExp α)}
    {f₀ f₁ f₂ : FuncInst Nat}
    (h0 : stubOk 0 2 f₀ = true) (h1 : stubOk 1 2 f₁ = true) (h2 : stubOk 2 1 f₂ = true)
    {F : Frame} (hFf : F.module.funcs = [0, 1, 2, 3]) (hFm : F.module.mems = [0])
    (hFl : F.locals = pairD) {s : Store Nat} {fs : List (FuncInst Nat)}
    (hfs : fs = [f₀, f₁, f₂] ++ fs.drop 3) (hsf : s.funcs = fs) (hml : s.mems.length = 1)
    (hinv : ∀ s', s'.funcs = fs → s'.mems.length = 1 → (pairAtomInv name) s') {Q : Post Nat}
    (hQ : BodyExits (pairAtomInv name) Q) :
    HWP P (memHost (pairAtomMod name) (some 0) (tabRoles T {}) (tabPairK T a b ρ)) s F
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
  -- symbol(16, 1)
  refine X.i32Const (us := []) ?_
  refine X.i32Const (us := [] ++ [.i32 16]) ?_
  refine hwp_call (us := []) (args := [.i32 16, .i32 1]) (x := ⟨0⟩) (k := 0) (fk := f₀)
    (i := ⟨"sexp", name, .func ⟨0⟩⟩) (by rw [hFf]; rfl) (hf0 _ (hf₁.trans hsf)) hc₀ he₀ (by simp [hn₀]) rfl
    (tab_pre_other' (accept_ne_of S.hn)) ?_
  rintro s₂ r ⟨⟨hfs₂, hml₂⟩, hshape⟩ hans
  have hfs₂' : s₂.funcs = fs := hfs₂.trans (hf₁.trans hsf)
  have hml₂' : s₂.mems.length = 1 := hml₂.trans hl₁
  refine ⟨fun res hr => ?_, fun _ => htrap s₂ F hfs₂' hml₂',
    fun a _ => hthrow s₂ F a hfs₂' hml₂'⟩
  obtain ⟨r₁, rfl⟩ := (hshape res hr).1 (.inl rfl)
  subst hr
  have hρ₁ : ρ r₁ = some (.atom a) :=
    tab_atom_ans S.hT S.ha rfl (by rw [bytes32_of_store hml hst₀ rfl]; decide) hans
  refine X.localSet (us := []) (x := ⟨0⟩) (by simp [hFl, pairD, Idx.toNat]) ?_
  -- "b" at 16
  refine X.i32Const (us := []) ?_
  refine X.i32Const (us := [] ++ [.i32 16]) ?_
  refine X.storePack (us := []) hFm hml₂' (htrap s₂ _ hfs₂' hml₂') fun mi₂ b₂ hmi₂ hst₂ => ?_
  obtain ⟨-, hl₃, hf₃⟩ := setMem_mems (mi := { mi₂ with bytes := b₂ }) hml₂'
  -- symbol(16, 1)
  refine X.i32Const (us := []) ?_
  refine X.i32Const (us := [] ++ [.i32 16]) ?_
  refine hwp_call (us := []) (args := [.i32 16, .i32 1]) (x := ⟨0⟩) (k := 0) (fk := f₀)
    (i := ⟨"sexp", name, .func ⟨0⟩⟩) (by show F.module.funcs[_]? = _; rw [hFf]; rfl) (hf0 _ (hf₃.trans hfs₂'))
    hc₀ he₀ (by simp [hn₀]) rfl (tab_pre_other' (accept_ne_of S.hn)) ?_
  rintro s₄ r ⟨⟨hfs₄, hml₄⟩, hshape⟩ hans
  have hfs₄' : s₄.funcs = fs := hfs₄.trans (hf₃.trans hfs₂')
  have hml₄' : s₄.mems.length = 1 := hml₄.trans hl₃
  refine ⟨fun res hr => ?_, fun _ => htrap s₄ _ hfs₄' hml₄',
    fun a _ => hthrow s₄ _ a hfs₄' hml₄'⟩
  obtain ⟨r₂, rfl⟩ := (hshape res hr).1 (.inl rfl)
  subst hr
  have hρ₂ : ρ r₂ = some (.atom b) :=
    tab_atom_ans S.hT S.hb rfl (by rw [bytes32_of_store hml₂' hst₂ rfl]; decide) hans
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
    (by simp [hn₁]) rfl (tab_pre_other' (by decide)) ?_
  rintro s₇ r ⟨⟨hfs₇, hml₇⟩, hshape⟩ hans
  have hfs₇' : s₇.funcs = fs := hfs₇.trans hfs₆
  have hml₇' : s₇.mems.length = 1 := hml₇.trans hl₆
  refine ⟨fun res hr => ?_, fun _ => htrap s₇ _ hfs₇' hml₇',
    fun a _ => hthrow s₇ _ a hfs₇' hml₇'⟩
  obtain ⟨r₃, rfl⟩ := (hshape res hr).1 (.inr rfl)
  subst hr
  have hρ₃ : ρ r₃ = some (SExp.ofList [.atom a, .atom b]) := by
    have hw := tabWrite_sexp_eq (T := T) (w := ⟨.values [.i32 r₃], memOf (some 0) s₇⟩)
      (r := r₃) S.hsexp rfl hh rfl
    rcases hans _ hw _ _ _ rfl with h | ⟨t, ht, hρ⟩
    · cases h
    · simp [Writer.built, Env.lookupAll, hρ₁, hρ₂, sexpW] at ht
      rw [hρ, ← ht]
  -- accept(r₃)
  refine hwp_call (us := []) (args := [.i32 r₃]) (x := ⟨2⟩) (k := 2) (fk := f₂)
    (i := impAcc) (by show F.module.funcs[_]? = _; rw [hFf]; rfl) (hf2 _ hfs₇') hc₂ he₂
    (by simp [hn₂]) rfl ?_ ?_
  · intro h hd t ht
    obtain rfl := tabAccept_inv (Op := SxOp α) (o := calloutIn impAcc (some 0) s₇ [.i32 r₃]) rfl hd
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

/-- **`pairAtomMod name` meets the writer contract** in every fixed environment, for every profile. -/
theorem tabPair_sat (P : Profile) (S : PairSpec T name dec a b)
    (ρ : Env (BitVec 32) (SExp α)) :
    MemSat P (pairAtomMod name) 0 (tabRoles T {}) (tabPairK T a b ρ) (pairAtomInv name) := by
  intro mt Is c₀ hI
  obtain ⟨c, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, hexp, hml, f₀, f₁, f₂, f₃, hf, h0, h1, h2, h3⟩ := pairAtom_facts S.hn hp
  have hmem : (c.withStart none).frame.module.mems[0]? = some 0 := by
    simp [Config.withStart, hmems]
  rw [hmem]
  refine ⟨fun n => Safe.of_exits (o := .normal []) (by simp [Config.withStart, hcode]; rfl)
    (fun _ _ => ⟨c, none, hp, rfl, hml⟩), ?_⟩
  intro a ha
  rw [← haddr, hexp] at ha
  obtain rfl : a = 3 := by simpa using ha
  obtain ⟨code, ps, rs, hcode3, hloc, hbody, he, hps, hrs, hfuncs, hmems3, hD⟩ := fnOk_spec h3
  have hinv : ∀ s', s'.funcs = c.store.funcs → s'.mems.length = 1 → (pairAtomInv name) s' :=
    fun s' h h' => ⟨c, none, hp, h, h'⟩
  have hfi : ∀ s, (pairAtomInv name) s → s.funcs = c.store.funcs := by
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
  exact tabPair_body S h0 h1 h2 (by simp [Frame.forCall, hfuncs]) (by simp [Frame.forCall, hmems3])
    (by simp [Frame.forCall, hD]) (fs := c.store.funcs) (by rw [hf]; rfl) (hfi s hs)
    hml' hinv hQ


/-- **`pairAtomMod name` writes only `(a b)`** (no sentinel, no undefined behaviour). -/
theorem tabPair_sound (P : Profile) (S : PairSpec T name dec a b) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    tabWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod name) T {} pol ⊆
      {SExp.ofList [.atom a, .atom b]} :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Cons.rolesWriterLang_subset
    (fun _ _ h => tabAccept_isAccept h) (fun _ _ _ h => tabWrite_isWrite h)
    (fun ρ => by rw [hs]; exact tabPair_sat P S ρ) (fun _ _ h => h) hw ha

/-- **The writer trace of the session.** -/
theorem tabPair_traces (P : Profile) (S : PairSpec T name dec a b) (q : BitVec 32) :
    [.enter, .write (.atom a) [] q, .write (.atom b) [] (q + 1),
      .write .list [q, q + 1] (q + 1 + 1), .accept (q + 1 + 1)] ∈
      tabTraces P (ReplyEnvs pairReply) 0 (pairAtomMod name) T {} := by
  obtain ⟨mt, Is, c₀, hI⟩ := spec_exists (pairAtomSpec_of S.hn)
  obtain ⟨c, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, hexp, hml, f₀, f₁, f₂, f₃, hf, h0, h1, h2, h3⟩ := pairAtom_facts S.hn hp
  obtain ⟨mi, hmis, hsize⟩ := one_page (pairAtomMem_of S.hn) hp
  obtain ⟨ps₀, rs₀, hc₀, he₀, hn₀⟩ := stubOk_spec h0
  obtain ⟨ps₁, rs₁, hc₁, he₁, hn₁⟩ := stubOk_spec h1
  obtain ⟨ps₂, rs₂, hc₂, he₂, hn₂⟩ := stubOk_spec h2
  obtain ⟨code, ps, rs, hcode3, hloc, hbody, he, hps, hrs, hfuncs, hmems3, hD⟩ := fnOk_spec h3
  rw [show c.withStart none = c from rfl] at hI
  have hmem0 : c.frame.module.mems[0]? = some 0 := by rw [hmems]; rfl
  have hfs : ∀ s : Store Nat, s.funcs = c.store.funcs → s.funcs[0]? = some f₀ ∧
      s.funcs[1]? = some f₁ ∧ s.funcs[2]? = some f₂ ∧ s.funcs[3]? = some f₃ := by
    intro s h; rw [h, hf]; exact ⟨rfl, rfl, rfl, rfl⟩
  have hmi : c.store.mems[0]? = some mi := by rw [hmis]; rfl
  let L := countEnv pairOut
  let R := tabRoles T {}
  have t₀ : TSession P L (pairAtomMod name) (some 0) R c q Is.addrs .inst false (c, q) [] := .start
  have hok : InvokeOk c.store 3 [] := ⟨f₃, ps, rs, (hfs _ rfl).2.2.2, he, by
    rw [List.eq_nil_of_length_eq_zero (l := ps.toList) hps]; exact .nil⟩
  have ha : 3 ∈ Is.addrs := by rw [← haddr, hexp]; simp
  have t₁ := TSession.invoke t₀ (by decide) ⟨[], hcode⟩ ha hok
  -- enter `run`
  have st₀ : Step P NH (invoke c.store 3 [])
      ⟨c.store, {}, [.frame 0 (Frame.forCall f₃.module [] [.i32, .i32])
        [.label 0 [] (expression pairBody)]]⟩ := by
    have h := Step.callRefFunc (P := P) (host := NH) (s := c.store) (f := {})
      (c := .callRefType ((c.store.funcs[3]?.map FuncInst.type).getD default)) (vs := [])
      (a := 3) (fi := f₃) (code := code) trivial (hfs _ rfl).2.2.2 he (by rw [hps]; rfl) hcode3
    rw [hrs, hloc, hbody] at h
    exact h
  have hFf : (Frame.forCall f₃.module [] [.i32, .i32]).module.funcs = [0, 1, 2, 3] := by
    simp [Frame.forCall, hfuncs]
  have hFm : (Frame.forCall f₃.module [] [.i32, .i32]).module.mems = [0] := by
    simp [Frame.forCall, hmems3]
  have hFl : (Frame.forCall f₃.module [] [.i32, .i32]).locals = pairD := by
    simp [Frame.forCall, hD]
  generalize Frame.forCall f₃.module [] [.i32, .i32] = F at st₀ hFf hFm hFl
  let F₁ := F.setLocal ⟨0⟩ (.i32 q)
  let F₂ := F₁.setLocal ⟨1⟩ (.i32 (q + 1))
  -- "a" at 16
  obtain ⟨b₁, hst₁⟩ := store_some (B := mi.bytes) (a := effAddr (16 : BitVec 32).toNat ⟨0, 0⟩)
    (n := PackSize.i8.width / 8) ((0x61 : BitVec 32).setWidth _) (by rw [hsize]; decide)
  have hz₁ : b₁.size = 65536 := (Silmaril.Wasm.Logic.Core.size_store hst₁).trans hsize
  let mi₁ : MemInst := { mi with bytes := b₁ }
  let s₁ := c.store.setMem 0 mi₁
  obtain ⟨hm₁, hl₁, hf₁⟩ := setMem_mems (mi := mi₁) hml
  have st₁ : Step P NH ⟨c.store, {}, [.frame 0 F [.label 0 [] (expression pairBody)]]⟩
      ⟨s₁, {}, [.frame 0 F [.label 0 [] (expression (pairBody.drop 3))]]⟩ :=
    step_body (step_mid [] _ (step_storePack hFm hmi hst₁))
  -- symbol(16, 1)
  have st₂ : Step P NH ⟨s₁, {}, [.frame 0 F [.label 0 [] (expression (pairBody.drop 3))]]⟩
      ⟨s₁, {}, (bodyCtx F (expression (pairBody.drop 6))).fill
        (vals [.i32 16, .i32 1] ++ [.ref (.func 0), .callRefType f₀.type])⟩ :=
    step_body (step_mid [.i32 16, .i32 1] (expression (pairBody.drop 6))
      (step_call (x := ⟨0⟩) (by rw [hFf]; rfl) (hfs _ hf₁).1))
  have hd₁ : decompose? s₁ ((bodyCtx F (expression (pairBody.drop 6))).fill
      (vals [.i32 16, .i32 1] ++ [.ref (.func 0), .callRefType f₀.type])) =
      some (bodyCtx F (expression (pairBody.drop 6)), 0, 0, [.i32 16, .i32 1]) :=
    decompose_fill _ trivial (hfs _ hf₁).1 he₀ (by rw [hn₀]; rfl) hc₀
  have t₂ := TSession.call (TSession.of_core_steps t₁
    (((st₀.steps.trans st₁.steps).trans st₂.steps))) hd₁
  have t₃ := TSession.answer t₂ hd₁ (a := ⟨s₁, .values [.i32 q]⟩) (q' := q + 1) ⟨rfl, rfl⟩
  -- local.set 0; "b" at 16
  have st₃ : Step P NH ⟨s₁, {}, (bodyCtx F (expression (pairBody.drop 6))).fill
      (Result.values [.i32 q]).toAdmin⟩
      ⟨s₁, {}, [.frame 0 F₁ [.label 0 [] (vals [] ++ [] ++ expression (pairBody.drop 7))]]⟩ :=
    step_body (step_mid [] (expression (pairBody.drop 7))
      (step_localSet (x := ⟨0⟩) (v := .i32 q) (by simp [hFl, pairD, Idx.toNat])))
  obtain ⟨b₂, hst₂⟩ := store_some (B := mi₁.bytes) (a := effAddr (16 : BitVec 32).toNat ⟨0, 0⟩)
    (n := PackSize.i8.width / 8) ((0x62 : BitVec 32).setWidth _) (by rw [hz₁]; decide)
  have hz₂ : b₂.size = 65536 := (Silmaril.Wasm.Logic.Core.size_store hst₂).trans hz₁
  let mi₂ : MemInst := { mi₁ with bytes := b₂ }
  let s₂ := s₁.setMem 0 mi₂
  obtain ⟨hm₂, hl₂, hf₂⟩ := setMem_mems (s := s₁) (mi := mi₂) hl₁
  have hF₁m : F₁.module.mems = [0] := hFm
  have hF₁f : F₁.module.funcs = [0, 1, 2, 3] := hFf
  have st₄ : Step P NH
      ⟨s₁, {}, [.frame 0 F₁ [.label 0 [] (vals [] ++ [] ++ expression (pairBody.drop 7))]]⟩
      ⟨s₂, {}, [.frame 0 F₁ [.label 0 [] (vals [] ++ [] ++ expression (pairBody.drop 10))]]⟩ :=
    step_body (step_mid [] (expression (pairBody.drop 10)) (step_storePack hF₁m hm₁ hst₂))
  -- symbol(16, 1)
  have hs₂f := hfs s₂ (hf₂.trans hf₁)
  have st₅ : Step P NH
      ⟨s₂, {}, [.frame 0 F₁ [.label 0 [] (vals [] ++ [] ++ expression (pairBody.drop 10))]]⟩
      ⟨s₂, {}, (bodyCtx F₁ (expression (pairBody.drop 13))).fill
        (vals [.i32 16, .i32 1] ++ [.ref (.func 0), .callRefType f₀.type])⟩ :=
    step_body (step_mid [.i32 16, .i32 1] (expression (pairBody.drop 13))
      (step_call (x := ⟨0⟩) (by rw [hF₁f]; rfl) hs₂f.1))
  have hd₂ : decompose? s₂ ((bodyCtx F₁ (expression (pairBody.drop 13))).fill
      (vals [.i32 16, .i32 1] ++ [.ref (.func 0), .callRefType f₀.type])) =
      some (bodyCtx F₁ (expression (pairBody.drop 13)), 0, 0, [.i32 16, .i32 1]) :=
    decompose_fill _ trivial hs₂f.1 he₀ (by rw [hn₀]; rfl) hc₀
  have t₄ := TSession.call (TSession.of_core_steps t₃
    ((st₃.steps.trans st₄.steps).trans st₅.steps)) hd₂
  have t₅ := TSession.answer t₄ hd₂ (a := ⟨s₂, .values [.i32 (q + 1)]⟩) (q' := q + 1 + 1)
    ⟨rfl, rfl⟩
  -- local.set 1; the handles at 0 and 4
  have st₆ : Step P NH ⟨s₂, {}, (bodyCtx F₁ (expression (pairBody.drop 13))).fill
      (Result.values [.i32 (q + 1)]).toAdmin⟩
      ⟨s₂, {}, [.frame 0 F₂ [.label 0 [] (vals [] ++ [] ++ expression (pairBody.drop 14))]]⟩ :=
    step_body (step_mid [] (expression (pairBody.drop 14))
      (step_localSet (x := ⟨1⟩) (v := .i32 (q + 1))
        (by simp [F₁, Frame.setLocal, hFl, pairD, Idx.toNat])))
  have hv₀ : F₂.local? ⟨0⟩ = some (some (.i32 q)) := by
    simp [F₂, F₁, Frame.local?, Frame.setLocal, hFl, pairD, Idx.toNat]
  have hv₁ : F₂.local? ⟨1⟩ = some (some (.i32 (q + 1))) := by
    simp [F₂, F₁, Frame.local?, Frame.setLocal, hFl, pairD, Idx.toNat]
  have hF₂m : F₂.module.mems = [0] := hFm
  have hF₂f : F₂.module.funcs = [0, 1, 2, 3] := hFf
  have st₇ : Step P NH
      ⟨s₂, {}, [.frame 0 F₂ [.label 0 [] (vals [] ++ [] ++ expression (pairBody.drop 14))]]⟩
      ⟨s₂, {}, [.frame 0 F₂ [.label 0 [] (vals [.i32 0] ++ [(Val.i32 q).toAdmin] ++
        expression (pairBody.drop 16))]]⟩ :=
    step_body (step_mid [.i32 0] (expression (pairBody.drop 16)) (step_localGet hv₀))
  obtain ⟨b₃, hst₃⟩ := store_some (B := mi₂.bytes) (a := effAddr (0 : BitVec 32).toNat ⟨0, 0⟩)
    (n := IntType.i32.width / 8) (q.setWidth _) (by rw [hz₂]; decide)
  have hz₃ : b₃.size = 65536 := (Silmaril.Wasm.Logic.Core.size_store hst₃).trans hz₂
  let mi₃ : MemInst := { mi₂ with bytes := b₃ }
  let s₃ := s₂.setMem 0 mi₃
  obtain ⟨hm₃, hl₃, hf₃⟩ := setMem_mems (s := s₂) (mi := mi₃) hl₂
  have st₈ : Step P NH
      ⟨s₂, {}, [.frame 0 F₂ [.label 0 [] (vals [.i32 0] ++ [(Val.i32 q).toAdmin] ++
        expression (pairBody.drop 16))]]⟩
      ⟨s₃, {}, [.frame 0 F₂ [.label 0 [] (vals [] ++ [] ++ expression (pairBody.drop 17))]]⟩ :=
    step_body (step_mid [] (expression (pairBody.drop 17)) (step_store32 hF₂m hm₂ hst₃))
  have st₉ : Step P NH
      ⟨s₃, {}, [.frame 0 F₂ [.label 0 [] (vals [] ++ [] ++ expression (pairBody.drop 17))]]⟩
      ⟨s₃, {}, [.frame 0 F₂ [.label 0 [] (vals [.i32 4] ++ [(Val.i32 (q + 1)).toAdmin] ++
        expression (pairBody.drop 19))]]⟩ :=
    step_body (step_mid [.i32 4] (expression (pairBody.drop 19)) (step_localGet hv₁))
  obtain ⟨b₄, hst₄⟩ := store_some (B := mi₃.bytes) (a := effAddr (4 : BitVec 32).toNat ⟨0, 0⟩)
    (n := IntType.i32.width / 8) ((q + 1).setWidth _) (by rw [hz₃]; decide)
  have hz₄ : b₄.size = 65536 := (Silmaril.Wasm.Logic.Core.size_store hst₄).trans hz₃
  let mi₄ : MemInst := { mi₃ with bytes := b₄ }
  let s₄ := s₃.setMem 0 mi₄
  obtain ⟨-, hl₄, hf₄⟩ := setMem_mems (s := s₃) (mi := mi₄) hl₃
  have st₁₀ : Step P NH
      ⟨s₃, {}, [.frame 0 F₂ [.label 0 [] (vals [.i32 4] ++ [(Val.i32 (q + 1)).toAdmin] ++
        expression (pairBody.drop 19))]]⟩
      ⟨s₄, {}, [.frame 0 F₂ [.label 0 [] (vals [] ++ [] ++ expression (pairBody.drop 20))]]⟩ :=
    step_body (step_mid [] (expression (pairBody.drop 20)) (step_store32 hF₂m hm₃ hst₄))
  -- sexp(0, 2)
  have hs₄f := hfs s₄ (hf₄.trans (hf₃.trans (hf₂.trans hf₁)))
  have st₁₁ : Step P NH
      ⟨s₄, {}, [.frame 0 F₂ [.label 0 [] (vals [] ++ [] ++ expression (pairBody.drop 20))]]⟩
      ⟨s₄, {}, (bodyCtx F₂ (expression (pairBody.drop 23))).fill
        (vals [.i32 0, .i32 2] ++ [.ref (.func 1), .callRefType f₁.type])⟩ :=
    step_body (step_mid [.i32 0, .i32 2] (expression (pairBody.drop 23))
      (step_call (x := ⟨1⟩) (by rw [hF₂f]; rfl) hs₄f.2.1))
  have hd₃ : decompose? s₄ ((bodyCtx F₂ (expression (pairBody.drop 23))).fill
      (vals [.i32 0, .i32 2] ++ [.ref (.func 1), .callRefType f₁.type])) =
      some (bodyCtx F₂ (expression (pairBody.drop 23)), 1, 1, [.i32 0, .i32 2]) :=
    decompose_fill _ trivial hs₄f.2.1 he₁ (by rw [hn₁]; rfl) hc₁
  have t₆ := TSession.call (TSession.of_core_steps t₅
    (((((st₆.steps.trans st₇.steps).trans st₈.steps).trans st₉.steps).trans
      st₁₀.steps).trans st₁₁.steps)) hd₃
  have t₇ := TSession.answer t₆ hd₃ (a := ⟨s₄, .values [.i32 (q + 1 + 1)]⟩)
    (q' := q + 1 + 1 + 1) ⟨rfl, rfl⟩
  -- accept
  have st₁₂ : Step P NH ⟨s₄, {}, (bodyCtx F₂ (expression (pairBody.drop 23))).fill
      (Result.values [.i32 (q + 1 + 1)]).toAdmin⟩
      ⟨s₄, {}, (bodyCtx F₂ []).fill
        (vals [.i32 (q + 1 + 1)] ++ [.ref (.func 2), .callRefType f₂.type])⟩ :=
    step_body (step_mid [.i32 (q + 1 + 1)] [] (step_call (x := ⟨2⟩) (by rw [hF₂f]; rfl)
      hs₄f.2.2.1))
  have hd₄ : decompose? s₄ ((bodyCtx F₂ []).fill
      (vals [.i32 (q + 1 + 1)] ++ [.ref (.func 2), .callRefType f₂.type])) =
      some (bodyCtx F₂ [], 2, 2, [.i32 (q + 1 + 1)]) :=
    decompose_fill _ trivial hs₄f.2.2.1 he₂ (by rw [hn₂]; rfl) hc₂
  have t₈ := TSession.call (TSession.of_core_steps t₇ st₁₂.steps) hd₄
  -- the decoded events
  have hco₁ : calloutAt? (pairAtomMod name) (some 0) ⟨s₁, {}, (bodyCtx F (expression (pairBody.drop 6))).fill
      (vals [.i32 16, .i32 1] ++ [.ref (.func 0), .callRefType f₀.type])⟩ =
      some (co name ⟨0⟩ s₁ [.i32 16, .i32 1]) := by
    unfold calloutAt?; rw [hd₁]; rfl
  have hco₂ : calloutAt? (pairAtomMod name) (some 0) ⟨s₂, {}, (bodyCtx F₁ (expression (pairBody.drop 13))).fill
      (vals [.i32 16, .i32 1] ++ [.ref (.func 0), .callRefType f₀.type])⟩ =
      some (co name ⟨0⟩ s₂ [.i32 16, .i32 1]) := by
    unfold calloutAt?; rw [hd₂]; rfl
  have hco₃ : calloutAt? (pairAtomMod name) (some 0) ⟨s₄, {}, (bodyCtx F₂ (expression (pairBody.drop 23))).fill
      (vals [.i32 0, .i32 2] ++ [.ref (.func 1), .callRefType f₁.type])⟩ =
      some (co "sexp" ⟨0⟩ s₄ [.i32 0, .i32 2]) := by
    unfold calloutAt?; rw [hd₃]; rfl
  have hco₄ : calloutAt? (pairAtomMod name) (some 0) ⟨s₄, {}, (bodyCtx F₂ []).fill
      (vals [.i32 (q + 1 + 1)] ++ [.ref (.func 2), .callRefType f₂.type])⟩ =
      some (co "accept" ⟨1⟩ s₄ [.i32 (q + 1 + 1)]) := by
    unfold calloutAt?; rw [hd₄]; rfl
  have hw₁ : tabWrite T {} (co name ⟨0⟩ s₁ [.i32 16, .i32 1])
      ⟨.values [.i32 q], memOf (some 0) s₁⟩ = some (.write (.atom a) [] q) :=
    tabWrite_bytes_eq S.hT S.ha rfl (by rw [bytes32_of_store hml hst₁ rfl]; decide)
  have hw₂ : tabWrite T {} (co name ⟨0⟩ s₂ [.i32 16, .i32 1])
      ⟨.values [.i32 (q + 1)], memOf (some 0) s₂⟩ = some (.write (.atom b) [] (q + 1)) :=
    tabWrite_bytes_eq S.hT S.hb rfl (by rw [bytes32_of_store hl₁ hst₂ rfl]; decide)
  have h₀ : bytesAt b₄ ⟨0, 4⟩ = (Memory.encodeLE 4 q.toNat).data.toList := by
    rw [Silmaril.Wasm.Logic.Core.bytesAt_store_disjoint hst₄ (.inr (by decide))]
    exact bytes_of_store32 hst₃
  have h₄ : bytesAt b₄ ⟨4, 4⟩ = (Memory.encodeLE 4 (q + 1).toNat).data.toList :=
    bytes_of_store32 hst₄
  have hh : handles32 (co "sexp" ⟨0⟩ s₄ [.i32 0, .i32 2]) = some [q, q + 1] :=
    handles32_pair (memOf_setMem hl₃) (by rw [hz₄]; decide) h₀ h₄
  have hw₃ : tabWrite T {} (co "sexp" ⟨0⟩ s₄ [.i32 0, .i32 2])
      ⟨.values [.i32 (q + 1 + 1)], memOf (some 0) s₄⟩ =
      some (.write .list [q, q + 1] (q + 1 + 1)) :=
    tabWrite_sexp_eq S.hsexp rfl hh rfl
  have hna₁ : tabAccept (Op := SxOp α) {} (co name ⟨0⟩ s₁ [.i32 16, .i32 1]) = none :=
    tabAccept_none (accept_ne_of S.hn)
  have hna₂ : tabAccept (Op := SxOp α) {} (co name ⟨0⟩ s₂ [.i32 16, .i32 1]) = none :=
    tabAccept_none (accept_ne_of S.hn)
  have hna₃ : tabAccept (Op := SxOp α) {} (co "sexp" ⟨0⟩ s₄ [.i32 0, .i32 2]) = none :=
    tabAccept_none (by show ("sexp", "sexp") ≠ ("sexp", "accept"); decide)
  have hac : tabAccept (Op := SxOp α) {} (co "accept" ⟨1⟩ s₄ [.i32 (q + 1 + 1)]) =
      some (.accept (q + 1 + 1)) :=
    tabAccept_acc _ _ rfl rfl
  rw [hco₁, hco₂, hco₃, hco₄] at t₈
  refine ⟨_, ⟨mt, Is, c, hI, L, q, countEnv_reply pairOut_shape _, .run, true, _,
    by rw [hmem0]; exact t₈⟩, ?_⟩
  simp only [Option.elim, Roles.callTags, Roles.answerTags, R, tabRoles]
  rw [hna₁, hw₁, hna₂, hw₂, hna₃, hw₃, hac]
  rfl

/-- **`pairAtomMod name` writes `(a b)`**, for every profile and policy. -/
theorem tabPair_live (P : Profile) (S : PairSpec T name dec a b) (pol : Policy (BitVec 32)) :
    SExp.ofList [.atom a, .atom b] ∈
      tabWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod name) T {} pol := by
  let q := base pol
  have hn₀ : pol.sentinel ≠ some q := by simpa using base_ne pol (k := 0) (by decide)
  have hn₁ : pol.sentinel ≠ some (q + 1) := base_ne pol (k := 1) (by decide)
  have hn₂ : pol.sentinel ≠ some (q + 1 + 1) := by
    rw [BitVec.add_assoc]; exact base_ne pol (k := 1 + 1) (by decide)
  have d₁ : q + 1 ≠ q := by bv_omega
  have d₂ : q + 1 + 1 ≠ q := by bv_omega
  have d₃ : q + 1 + 1 ≠ q + 1 := by bv_omega
  have e₁ : Function.update (Env.empty : Env (BitVec 32) (SExp α)) q
      (some (.atom a)) (q + 1) = none := by
    rw [Function.update_of_ne d₁]; rfl
  have e₂ : Function.update (Function.update (Env.empty : Env (BitVec 32) (SExp α)) q
      (some (.atom a))) (q + 1) (some (.atom b)) (q + 1 + 1) = none := by
    rw [Function.update_of_ne d₃, Function.update_of_ne d₂]; rfl
  have hb : (sexpW α).built (Function.update (Function.update
      (Env.empty : Env (BitVec 32) (SExp α)) q (some (.atom a))) (q + 1)
      (some (.atom b))) .list [q, q + 1] = some (SExp.ofList [.atom a, .atom b]) := by
    simp [Writer.built, Env.lookupAll, sexpW]
  simp only [tabWriterLang, writerLang, Host.lang]
  refine Set.mem_biUnion (tabPair_traces P S q) ⟨_, _, .cons .enter
    (.cons (.writeOk (t := .atom a) rfl ⟨hn₀, .inl rfl⟩ fun _ h => by cases h)
    (.cons (.writeOk (t := .atom b) rfl ⟨hn₁, .inl e₁⟩ fun _ h => by cases h)
    (.cons (.writeOk (t := (SExp.ofList [.atom a, .atom b])) hb ⟨hn₂, .inl e₂⟩ fun _ h => by cases h)
    (.cons (.acceptOk (t := (SExp.ofList [.atom a, .atom b])) (by simp)) (.nil _))))), by simp⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Tab
