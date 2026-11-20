module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Items
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Langs

/-!
# Proofs: `listMod` accepts only lists of two children of the child reader's kind

* `itemsList_two`: a returned `list<i32>` of two handles, read off the memory by the decoder,
  is the pair of words at `ptr` and `ptr + 4`, where `ptr` is the word at `[0, 4)`: the words
  the module loads;
* `list_body`: the body of `check` under the most general host of the reader contract in a
  fixed environment `ρ`. The correct read of `items(h, 0)` says that `h` denotes a list whose
  children the decoded handles denote; the module loads those handles into locals before any
  other call; the correct reads of `child` on them say that they denote members of `S`
  (`ChildKind ans S`); so at `accept(h)`, `h` denotes a list of two members of `S`;
* `list_sat`, `listReaderLang_subset` (the reader bridge for the list roles), and the instances
  `symList_sat` (symbols) and `blobList_sat` (blobs).

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept Silmaril.Accept.IO Silmaril.Accept.Handle
  Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.Items
  Silmaril.Wasm.Game.HandleAccept.MemSound.Text Silmaril.Wasm.Game.HandleAccept.MemSound.Readers
  Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Items Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post bytesAt Region leNat)

/-! ## The returned pair -/

/-- **A returned list of two handles is the pair of words at `ptr`**, `ptr` the word at
`[0, 4)`. -/
theorem itemsList_two {mem : ByteArray} {hs : List (BitVec 32)}
    (h : itemsList mem 0 = some hs) (h2 : hs.length = 2) :
    leNat (bytesAt mem ⟨0, 4⟩) % 2 ^ 32 + 8 ≤ mem.size ∧
    hs = [BitVec.ofNat 32 (leNat (bytesAt mem ⟨leNat (bytesAt mem ⟨0, 4⟩) % 2 ^ 32, 4⟩)),
      BitVec.ofNat 32 (leNat (bytesAt mem ⟨leNat (bytesAt mem ⟨0, 4⟩) % 2 ^ 32 + 4, 4⟩))] := by
  unfold itemsList at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨bs₈, h₈, ws, hws, ⟨p, n⟩, hpn, bs, hbs, hhs⟩ := h
  obtain ⟨hb₈, rfl⟩ := segOf_eq h₈
  have hl₀ : (bytesAt mem ⟨0, 4⟩).length = 4 :=
    Silmaril.Wasm.Logic.Core.length_bytesAt (by simp [Region.InBounds, Region.stop]; omega)
  have hl₄ : (bytesAt mem ⟨4, 4⟩).length = 4 :=
    Silmaril.Wasm.Logic.Core.length_bytesAt (by simp [Region.InBounds, Region.stop]; omega)
  rw [show (8 : Nat) = 4 + 4 from rfl, bytesAt_append, Nat.zero_add, le32s_four _ hl₀,
    ← List.append_nil (bytesAt mem ⟨4, 4⟩), le32s_four _ hl₄] at hws
  simp only [le32s, Option.map_some, Option.some.injEq] at hws
  subst hws
  simp only [pair32, Option.some.injEq, Prod.mk.injEq] at hpn
  obtain ⟨rfl, rfl⟩ := hpn
  obtain ⟨hb, rfl⟩ := segOf_eq hbs
  dsimp only at hb hhs
  simp only [BitVec.toNat_ofNat] at hb hhs
  generalize leNat (bytesAt mem ⟨0, 4⟩) % 2 ^ 32 = q at hb hhs ⊢
  generalize leNat (bytesAt mem ⟨4, 4⟩) % 2 ^ 32 = k at hb hhs
  have h1 := le32s_length hhs
  have h2' := Silmaril.Wasm.Logic.Core.length_bytesAt (B := mem) (r := ⟨q, 4 * k⟩)
    (by simp only [Region.InBounds, Region.stop]; exact hb)
  dsimp only at h1 h2'
  obtain rfl : k = 2 := by omega
  rw [show 4 * 2 = 4 + 4 from rfl] at hhs
  refine ⟨hb, ?_⟩
  have hq₀ : (bytesAt mem ⟨q, 4⟩).length = 4 :=
    Silmaril.Wasm.Logic.Core.length_bytesAt (by simp [Region.InBounds, Region.stop]; omega)
  have hq₄ : (bytesAt mem ⟨q + 4, 4⟩).length = 4 :=
    Silmaril.Wasm.Logic.Core.length_bytesAt (by simp [Region.InBounds, Region.stop]; omega)
  rw [bytesAt_append, le32s_four _ hq₀, ← List.append_nil (bytesAt mem ⟨q + 4, 4⟩),
    le32s_four _ hq₄] at hhs
  simp only [le32s, Option.map_some, Option.some.injEq] at hhs
  exact hhs.symm

/-! ## Instance facts -/

/-- The default values of the locals. -/
def listD : List (Option Val) := [some (.i32 0), some (.i32 0)]

/-- The shape of the instantiated module (and distinct `items` and `child` names). -/
def listOk (ix : ListImports) : Bool :=
  ix.child != ix.items &&
  match prep (listMod ix) with
  | some (c, st) => st.isNone && c.code.isEmpty && c.frame.module.mems == [0] &&
      exportFuncAddrs c.frame.module == [3] && c.store.mems.length == 1 &&
      (match c.store.funcs with
       | [f₀, f₁, f₂, f₃] => stubOk 0 2 f₀ && stubOk 1 2 f₁ && stubOk 2 1 f₂ &&
          fnOk [.i32, .i32] listBody 1 0 [0, 1, 2, 3] [0] listD f₃
       | _ => false)
  | none => false

theorem listOk_sym : listOk {} = true := by decide +kernel

theorem listOk_blob : listOk blobImports = true := by decide +kernel

theorem list_facts {ix : ListImports} (hok : listOk ix = true) {c : Config Nat}
    {st : Option FuncIdx} (hp : prep (listMod ix) = some (c, st)) :
    ix.child ≠ ix.items ∧ st = none ∧ c.code = [] ∧ c.frame.module.mems = [0] ∧
    exportFuncAddrs c.frame.module = [3] ∧
    c.store.mems.length = 1 ∧ ∃ f₀ f₁ f₂ f₃, c.store.funcs = [f₀, f₁, f₂, f₃] ∧
      stubOk 0 2 f₀ = true ∧ stubOk 1 2 f₁ = true ∧ stubOk 2 1 f₂ = true ∧
      fnOk [.i32, .i32] listBody 1 0 [0, 1, 2, 3] [0] listD f₃ = true := by
  unfold listOk at hok
  rw [hp] at hok
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, Option.isNone_iff_eq_none,
    List.isEmpty_iff] at hok
  obtain ⟨hne, ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩⟩ := hok
  refine ⟨hne, h1, h2, h3, h4, h5, ?_⟩
  split at h6
  · rename_i f₀ f₁ f₂ f₃ hf
    simp only [Bool.and_eq_true] at h6
    exact ⟨f₀, f₁, f₂, f₃, hf, h6.1.1.1, h6.1.1.2, h6.1.2, h6.2⟩
  · cases h6

/-- The store invariant: the instantiated functions and one memory. -/
def listInv (ix : ListImports) (s : Store Nat) : Prop :=
  ∃ c st, prep (listMod ix) = some (c, st) ∧ s.funcs = c.store.funcs ∧ s.mems.length = 1

/-- The reader contract in the fixed environment `ρ`: accepts name lists of two members of
`S`. -/
abbrev listK (ix : ListImports) (S : Set SymStrBytesSExp) (ρ : Env (BitVec 32) SymStrBytesSExp) :
    MemContract MemREv :=
  readerContract ix.toRead ρ (pairsOf S) itemsReply

/-- **A child reader of kind `S`**: a correct answer `ans w rp` to the query `atom c` says that
`c` denotes a member of `S`. -/
def ChildKind (ans : HostReply → BitVec 32 → SxA MemAtom (BitVec 32))
    (S : Set SymStrBytesSExp) : Prop :=
  ∀ (ρ : Env (BitVec 32) SymStrBytesSExp) c w rp,
    (sexpR MemAtom (BitVec 32)).ok ρ (.atom c) (ans w rp) → ∃ t ∈ S, ρ c = some t

theorem symTextAns_kind : ChildKind symTextAns symbols := by
  intro ρ c w rp hok
  unfold symTextAns at hok
  split at hok
  · exact ⟨_, ⟨_, rfl⟩, hok⟩
  · exact hok.elim

theorem blobAns_kind : ChildKind blobAns blobs := by
  intro ρ c w rp hok
  unfold blobAns at hok
  split at hok
  · exact ⟨_, ⟨_, rfl⟩, hok⟩
  · exact hok.elim

/-! ## The body -/

theorem readAccept_inv' {ix : ReadImports} {o : Callout} {v : Val} {h : BitVec 32}
    (ha : o.args = [v]) (hd : readAccept ix o = some (.accept h)) : v = .i32 h := by
  unfold readAccept at hd
  split at hd
  · simp only [ha, Callout.args1, Option.map_eq_some_iff, REv.accept.injEq] at hd
    obtain ⟨a, hi, rfl⟩ := hd
    exact i32?_some hi
  · cases hd

theorem readAccept_two {ix : ReadImports} {o : Callout} {a b : Val} {h : BitVec 32}
    (ha : o.args = [a, b]) : readAccept ix o ≠ some (.accept h) := by
  unfold readAccept
  split
  · simp [ha, Callout.args1]
  · simp

/-- What the reader contract says after `items(h, 0)` returned in the store `s'`. -/
theorem list_items_ans {ix : ListImports} {ans : HostReply → BitVec 32 → SxA MemAtom (BitVec 32)}
    {S : Set SymStrBytesSExp} {ρ : Env (BitVec 32) SymStrBytesSExp} {s s' : Store Nat}
    {h : BitVec 32} {mi : MemInst} (hmi : s'.mems[0]? = some mi)
    (hans : ∀ y, listRead ix ans (calloutIn ⟨ix.items.1, ix.items.2, .func ⟨0⟩⟩ (some 0) s
      [.i32 h, .i32 0]) ⟨.values [], memOf (some 0) s'⟩ = some y → (listK ix S ρ).ans y) :
    ∃ hs, itemsList mi.bytes 0 = some hs ∧ ∃ cs, ρ h = some (SExp.ofList cs) ∧
      List.Forall₂ (fun h c => ρ h = some c) hs cs := by
  have hm : memOf (some 0) s' = some mi.bytes := by simp [memOf, hmi]
  have hd : listRead ix ans (calloutIn ⟨ix.items.1, ix.items.2, .func ⟨0⟩⟩ (some 0) s
      [.i32 h, .i32 0]) ⟨.values [], memOf (some 0) s'⟩ =
      some (.read (.items h) (itemsAns ⟨.values [], memOf (some 0) s'⟩ 0)) := by
    simp [listRead, itemsRead, calloutIn, Val.i32, ListImports.toRead]
  obtain ⟨-, hok⟩ := hans _ hd _ _ rfl
  unfold itemsAns at hok
  rw [hm] at hok
  simp only [Option.bind_some] at hok
  split at hok
  · rename_i hs hhs
    obtain ⟨cs, hρ, hall⟩ := hok
    exact ⟨hs, by simpa using hhs, cs, hρ, hall⟩
  · exact hok.elim

/-- What the reader contract says after `child(c, 0)` returned in the store `s'`. -/
theorem list_child_ans {ix : ListImports} {ans : HostReply → BitVec 32 → SxA MemAtom (BitVec 32)}
    {S : Set SymStrBytesSExp} (hS : ChildKind ans S) (hne : ix.child ≠ ix.items)
    {ρ : Env (BitVec 32) SymStrBytesSExp} {s s' : Store Nat} {c : BitVec 32}
    (hans : ∀ y, listRead ix ans (calloutIn ⟨ix.child.1, ix.child.2, .func ⟨0⟩⟩ (some 0) s
      [.i32 c, .i32 0]) ⟨.values [], memOf (some 0) s'⟩ = some y → (listK ix S ρ).ans y) :
    ∃ t ∈ S, ρ c = some t := by
  have hd : listRead ix ans (calloutIn ⟨ix.child.1, ix.child.2, .func ⟨0⟩⟩ (some 0) s
      [.i32 c, .i32 0]) ⟨.values [], memOf (some 0) s'⟩ =
      some (.read (.atom c) (ans ⟨.values [], memOf (some 0) s'⟩ 0)) := by
    simp [listRead, childRead, calloutIn, Val.i32, hne]
  exact hS ρ c _ _ (hans _ hd _ _ rfl).2

/-- **The body of `check`**, in the fixed environment `ρ`. -/
theorem list_body {P : Profile} {ix : ListImports}
    {ans : HostReply → BitVec 32 → SxA MemAtom (BitVec 32)} {S : Set SymStrBytesSExp}
    (hS : ChildKind ans S) (hne : ix.child ≠ ix.items) {ρ : Env (BitVec 32) SymStrBytesSExp}
    {f₀ f₁ f₂ : FuncInst Nat}
    (h0 : stubOk 0 2 f₀ = true) (h1 : stubOk 1 2 f₁ = true) (h2 : stubOk 2 1 f₂ = true)
    {v : Val} {F : Frame}
    (hFf : F.module.funcs = [0, 1, 2, 3]) (hFm : F.module.mems = [0])
    (hFl : F.locals = [some v, some (.i32 0), some (.i32 0)])
    {s : Store Nat} {fs : List (FuncInst Nat)}
    (hfs : fs = [f₀, f₁, f₂] ++ fs.drop 3) (hsf : s.funcs = fs) (hml : s.mems.length = 1)
    (hinv : ∀ s', s'.funcs = fs → s'.mems.length = 1 → listInv ix s') {Q : Post Nat}
    (hQ : BodyExits (listInv ix) Q) :
    HWP P (memHost (listMod ix) (some 0) (listRoles ix ans) (listK ix S ρ)) s F
      (vals [] ++ expression listBody) Q := by
  obtain ⟨ps₀, rs₀, hc₀, he₀, hn₀⟩ := stubOk_spec h0
  obtain ⟨ps₁, rs₁, hc₁, he₁, hn₁⟩ := stubOk_spec h1
  obtain ⟨ps₂, rs₂, hc₂, he₂, hn₂⟩ := stubOk_spec h2
  have htrap : ∀ s' (F' : Frame), s'.funcs = fs → s'.mems.length = 1 → Q s' F' .trap :=
    fun s' F' h h' => (hQ s' (hinv s' h h') F').2.2.1
  have hthrow : ∀ s' (F' : Frame) a, s'.funcs = fs → s'.mems.length = 1 →
      Q s' F' (.throw a) :=
    fun s' F' a h h' => (hQ s' (hinv s' h h') F').2.2.2 a
  have hv : F.local? ⟨0⟩ = some (some v) := by simp [Frame.local?, hFl, Idx.toNat]
  unfold listBody
  -- items(h, 0)
  refine X.localGet (us := []) hv ?_
  refine X.i32Const (us := [] ++ [v]) ?_
  refine hwp_call (us := []) (args := [v, .i32 0]) (x := ⟨0⟩) (k := 0) (fk := f₀)
    (i := ⟨ix.items.1, ix.items.2, .func ⟨0⟩⟩) (by rw [hFf]; rfl) (by rw [hsf, hfs]; rfl)
    hc₀ he₀ (by simp [hn₀]) rfl (fun _ hd => absurd hd (readAccept_two rfl)) ?_
  rintro s₁ r ⟨⟨hfs₁, hml₁⟩, hshape⟩ hans
  have hfs₁' : s₁.funcs = fs := hfs₁.trans hsf
  have hml₁' : s₁.mems.length = 1 := hml₁.trans hml
  refine ⟨fun res hr => ?_, fun _ => htrap s₁ F hfs₁' hml₁',
    fun a _ => hthrow s₁ F a hfs₁' hml₁'⟩
  obtain rfl := hshape res hr
  subst hr
  obtain ⟨mi₁, hmi₁⟩ : ∃ mi, s₁.mems[0]? = some mi :=
    ⟨s₁.mems[0]'(by omega), List.getElem?_eq_getElem _⟩
  have hfact : ∀ h, v = .i32 h → ∃ hs, itemsList mi₁.bytes 0 = some hs ∧
      ∃ cs, ρ h = some (SExp.ofList cs) ∧ List.Forall₂ (fun h c => ρ h = some c) hs cs := by
    rintro h rfl
    exact list_items_ans (s := s) hmi₁ hans
  -- the length
  refine X.i32Const (us := []) ?_
  refine X.load32 (us := []) hFm hml₁' (htrap s₁ F hfs₁' hml₁') fun mi c hmi hld => ?_
  have e : mi₁ = mi := (Option.some.inj (hmi.symm.trans hmi₁)).symm
  subst e
  refine X.neConst (us := []) (x := c.setWidth 32) ?_
  refine X.if_ (us := []) (fun _ => ?_) (fun hc => ?_)
  · exact X.return_ (us := []) ((BodyExits.label hQ s₁ (hinv s₁ hfs₁' hml₁') F).1 [])
  have hc2 : c.setWidth 32 = 2 := bne_eq_false_iff_eq.1 (bool32_eq_zero hc)
  -- the first handle
  refine X.i32Const (us := []) ?_
  refine X.load32 (us := []) hFm hml₁' (htrap s₁ F hfs₁' hml₁') fun mi p hmi hldp => ?_
  have e : mi₁ = mi := (Option.some.inj (hmi.symm.trans hmi₁)).symm
  subst e
  refine X.load32 (us := []) (addr := p.setWidth 32) hFm hml₁' (htrap s₁ F hfs₁' hml₁')
    fun mi a₁ hmi hld₁ => ?_
  have e : mi₁ = mi := (Option.some.inj (hmi.symm.trans hmi₁)).symm
  subst e
  refine X.localSet (us := []) (x := ⟨1⟩) (by simp [hFl, Idx.toNat]) ?_
  -- the second handle
  refine X.i32Const (us := []) ?_
  refine X.load32 (us := []) hFm hml₁' (htrap s₁ _ hfs₁' hml₁') fun mi p' hmi hldp' => ?_
  have e : mi₁ = mi := (Option.some.inj (hmi.symm.trans hmi₁)).symm
  subst e
  have e : p = p' := (Option.some.inj (hldp'.symm.trans hldp)).symm
  subst e
  refine X.load32 (us := []) (addr := p.setWidth 32) hFm hml₁' (htrap s₁ _ hfs₁' hml₁')
    fun mi a₂ hmi hld₂ => ?_
  have e : mi₁ = mi := (Option.some.inj (hmi.symm.trans hmi₁)).symm
  subst e
  refine X.localSet (us := []) (x := ⟨2⟩) (by simp [Frame.setLocal, hFl, Idx.toNat]) ?_
  -- what the loaded handles are
  have hpair : ∀ hs, itemsList mi₁.bytes 0 = some hs → hs = [a₁.setWidth 32, a₂.setWidth 32] := by
    intro hs hhs
    obtain ⟨hb8, hlen'⟩ := itemsList_spec hhs
    have hcn := Silmaril.Wasm.Logic.Core.load_eq (B := mi₁.bytes) (a := 4) (n := 4)
      (by omega)
    have hc' : c.toNat = leNat (bytesAt mi₁.bytes ⟨4, 4⟩) % 2 ^ (8 * 4) :=
      (congrArg BitVec.toNat (Option.some.inj (hld.symm.trans hcn))).trans
        (BitVec.toNat_ofNat _ _)
    have h22 : c.toNat % 2 ^ 32 = 2 := by
      have := congrArg BitVec.toNat hc2
      rw [BitVec.toNat_setWidth] at this
      simpa using this
    have hl2 : hs.length = 2 := by
      rw [hlen', BitVec.toNat_ofNat]
      simp only [Nat.reduceMul, Nat.reducePow] at h22 hc' ⊢
      omega
    obtain ⟨hbp, rfl⟩ := itemsList_two hhs hl2
    have hp0 := Silmaril.Wasm.Logic.Core.load_eq (B := mi₁.bytes) (a := 0) (n := 4)
      (by omega)
    have hpn : (p.setWidth 32).toNat = leNat (bytesAt mi₁.bytes ⟨0, 4⟩) % 2 ^ 32 := by
      rw [BitVec.toNat_setWidth,
        (congrArg BitVec.toNat (Option.some.inj (hldp.symm.trans hp0))).trans
          (BitVec.toNat_ofNat _ _)]
      exact Nat.mod_mod _ _
    have e₁ := Silmaril.Wasm.Logic.Core.load_eq (B := mi₁.bytes)
      (a := leNat (bytesAt mi₁.bytes ⟨0, 4⟩) % 2 ^ 32) (n := 4) (by omega)
    have e₂ := Silmaril.Wasm.Logic.Core.load_eq (B := mi₁.bytes)
      (a := leNat (bytesAt mi₁.bytes ⟨0, 4⟩) % 2 ^ 32 + 4) (n := 4) (by omega)
    have ha₁ : a₁.toNat = _ := (congrArg BitVec.toNat (Option.some.inj (hld₁.symm.trans (by
      rw [show effAddr (p.setWidth 32).toNat ⟨0, 0⟩ = leNat (bytesAt mi₁.bytes ⟨0, 4⟩) % 2 ^ 32
        from hpn]; exact e₁)))).trans (BitVec.toNat_ofNat _ _)
    have ha₂ : a₂.toNat = _ := (congrArg BitVec.toNat (Option.some.inj (hld₂.symm.trans (by
      rw [show effAddr (p.setWidth 32).toNat ⟨0, 4⟩ =
        leNat (bytesAt mi₁.bytes ⟨0, 4⟩) % 2 ^ 32 + 4 by
          simp only [effAddr, hpn]; rfl]; exact e₂)))).trans (BitVec.toNat_ofNat _ _)
    simp only [List.cons.injEq, and_true]
    constructor <;> apply BitVec.eq_of_toNat_eq <;>
      rw [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
    · rw [ha₁]; exact (Nat.mod_mod _ _).symm
    · rw [ha₂]; exact (Nat.mod_mod _ _).symm
  generalize hF₂ : (F.setLocal ⟨1⟩ (.num ⟨.int .i32, a₁.setWidth 32⟩)).setLocal ⟨2⟩
    (.num ⟨.int .i32, a₂.setWidth 32⟩) = F₂
  have hF₂f : F₂.module.funcs = [0, 1, 2, 3] := by rw [← hF₂]; exact hFf
  have hv₀ : F₂.local? ⟨0⟩ = some (some v) := by
    simp [← hF₂, Frame.local?, Frame.setLocal, hFl, Idx.toNat]
  have hv₁ : F₂.local? ⟨1⟩ = some (some (.i32 (a₁.setWidth 32))) := by
    simp [← hF₂, Frame.local?, Frame.setLocal, hFl, Idx.toNat, Val.i32]
  have hv₂ : F₂.local? ⟨2⟩ = some (some (.i32 (a₂.setWidth 32))) := by
    simp [← hF₂, Frame.local?, Frame.setLocal, hFl, Idx.toNat, Val.i32]
  -- child(c₁, 0)
  refine X.localGet (us := []) hv₁ ?_
  refine X.i32Const (us := [] ++ [.i32 (a₁.setWidth 32)]) ?_
  refine hwp_call (us := []) (args := [.i32 (a₁.setWidth 32), .i32 0]) (x := ⟨1⟩) (k := 1)
    (fk := f₁) (i := ⟨ix.child.1, ix.child.2, .func ⟨0⟩⟩) (by rw [hF₂f]; rfl)
    (by rw [hfs₁', hfs]; rfl) hc₁ he₁ (by simp [hn₁]) rfl
    (fun _ hd => absurd hd (readAccept_two rfl)) ?_
  rintro s₂ r ⟨⟨hfs₂, hml₂⟩, hshape⟩ hans₁
  have hfs₂' : s₂.funcs = fs := hfs₂.trans hfs₁'
  have hml₂' : s₂.mems.length = 1 := hml₂.trans hml₁'
  refine ⟨fun res hr => ?_, fun _ => htrap s₂ F₂ hfs₂' hml₂',
    fun a _ => hthrow s₂ F₂ a hfs₂' hml₂'⟩
  obtain rfl := hshape res hr
  subst hr
  obtain ⟨t₁, ht₁, hρ₁⟩ := list_child_ans (s := s₁) hS hne hans₁
  -- child(c₂, 0)
  refine X.localGet (us := []) hv₂ ?_
  refine X.i32Const (us := [] ++ [.i32 (a₂.setWidth 32)]) ?_
  refine hwp_call (us := []) (args := [.i32 (a₂.setWidth 32), .i32 0]) (x := ⟨1⟩) (k := 1)
    (fk := f₁) (i := ⟨ix.child.1, ix.child.2, .func ⟨0⟩⟩) (by rw [hF₂f]; rfl)
    (by rw [hfs₂', hfs]; rfl) hc₁ he₁ (by simp [hn₁]) rfl
    (fun _ hd => absurd hd (readAccept_two rfl)) ?_
  rintro s₃ r ⟨⟨hfs₃, hml₃⟩, hshape⟩ hans₂
  have hfs₃' : s₃.funcs = fs := hfs₃.trans hfs₂'
  have hml₃' : s₃.mems.length = 1 := hml₃.trans hml₂'
  refine ⟨fun res hr => ?_, fun _ => htrap s₃ F₂ hfs₃' hml₃',
    fun a _ => hthrow s₃ F₂ a hfs₃' hml₃'⟩
  obtain rfl := hshape res hr
  subst hr
  obtain ⟨t₂, ht₂, hρ₂⟩ := list_child_ans (s := s₂) hS hne hans₂
  -- accept(h)
  refine X.localGet (us := []) hv₀ ?_
  refine hwp_call (us := []) (args := [v]) (x := ⟨2⟩) (k := 2) (fk := f₂)
    (i := ⟨ix.accept.1, ix.accept.2, .func ⟨1⟩⟩) (by rw [hF₂f]; rfl) (by rw [hfs₃', hfs]; rfl)
    hc₂ he₂ (by simp [hn₂]) rfl ?_ ?_
  · intro h hd t ht
    have hvh : v = .i32 h := readAccept_inv' rfl hd
    obtain ⟨hs, hhs, cs, hρ, hall⟩ := hfact h hvh
    rw [hpair hs hhs] at hall
    rw [hρ] at ht
    cases ht
    rcases hall with _ | ⟨e₁, hall⟩
    rcases hall with _ | ⟨e₂, hall⟩
    cases hall
    rw [hρ₁] at e₁
    rw [hρ₂] at e₂
    cases e₁
    cases e₂
    exact ⟨t₁, ht₁, t₂, ht₂, rfl⟩
  rintro s₄ r ⟨⟨hfs₄, hml₄⟩, hshape⟩ -
  have hfs₄' : s₄.funcs = fs := hfs₄.trans hfs₃'
  have hml₄' : s₄.mems.length = 1 := hml₄.trans hml₃'
  refine ⟨fun res hr => ?_, fun _ => htrap s₄ F₂ hfs₄' hml₄',
    fun a _ => hthrow s₄ F₂ a hfs₄' hml₄'⟩
  obtain rfl := hshape res hr
  exact X.done (hQ s₄ (hinv s₄ hfs₄' hml₄') F₂).1

/-- **`listMod ix` meets the reader contract** in every fixed environment, for every profile,
when its child reader is of kind `S`. -/
theorem list_sat (P : Profile) {ix : ListImports} (hok : listOk ix = true)
    {ans : HostReply → BitVec 32 → SxA MemAtom (BitVec 32)} {S : Set SymStrBytesSExp}
    (hS : ChildKind ans S) (ρ : Env (BitVec 32) SymStrBytesSExp) :
    MemSat P (listMod ix) 0 (listRoles ix ans) (listK ix S ρ) (listInv ix) := by
  intro mt Is c₀ hI
  obtain ⟨c, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨hne, rfl, hcode, hmems, hexp, hml, f₀, f₁, f₂, f₃, hf, h0, h1, h2, h3⟩ :=
    list_facts hok hp
  have hmem : (c.withStart none).frame.module.mems[0]? = some 0 := by
    simp [Config.withStart, hmems]
  rw [hmem]
  refine ⟨fun n => Safe.of_exits (o := .normal []) (by simp [Config.withStart, hcode]; rfl)
    (fun _ _ => ⟨c, none, hp, rfl, hml⟩), ?_⟩
  intro a ha
  rw [← haddr, hexp] at ha
  obtain rfl : a = 3 := by simpa using ha
  obtain ⟨code, ps, rs, hcode2, hloc, hbody, he, hps, hrs, hfuncs, hmems2, hD⟩ := fnOk_spec h3
  have hinv : ∀ s', s'.funcs = c.store.funcs → s'.mems.length = 1 → listInv ix s' :=
    fun s' h h' => ⟨c, none, hp, h, h'⟩
  have hfi : ∀ s, listInv ix s → s.funcs = c.store.funcs := by
    rintro s ⟨c', st', hp', hfs, _⟩
    have hcc : c' = c := (Prod.mk.inj (Option.some.inj (hp'.symm.trans hp))).1
    rw [hfs, hcc]
  refine export_valid (fi := f₃) (fun s hs => by rw [hfi s hs, hf]; rfl) hcode2 he hrs ?_
  intro s args hs hok' Q hQ
  have hlen1 : args.length = 1 := by
    have := args_length (by rw [hfi s hs, hf]; rfl) he hok'
    rw [hps] at this
    exact this
  obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp hlen1
  rw [hbody]
  have hml' : s.mems.length = 1 := by obtain ⟨_, _, _, _, h⟩ := hs; exact h
  have hFl : (Frame.forCall f₃.module [v] code.locals).locals =
      [some v, some (.i32 0), some (.i32 0)] := by
    unfold Frame.forCall
    dsimp only
    rw [hloc, hD]
    rfl
  exact list_body (v := v) hS hne h0 h1 h2 (by simp [Frame.forCall, hfuncs])
    (by simp [Frame.forCall, hmems2]) hFl (fs := c.store.funcs) (by rw [hf]; rfl) (hfi s hs)
    hml' hinv hQ

/-! ## The reader bridge -/

theorem listRead_ne_accept {ix : ListImports}
    {ans : HostReply → BitVec 32 → SxA MemAtom (BitVec 32)} {o : Callout} {w : HostReply}
    {h : BitVec 32} : listRead ix ans o w ≠ some (.accept h) := by
  unfold listRead
  split
  · exact itemsRead_ne_accept
  · unfold childRead
    split
    · split <;> simp
    · simp

/-- **The list reader bridge**: under the trapping read policy and no accept UB, the reader
language over every set of fixed environments is included in `L`. -/
theorem listReaderLang_subset {P : Numerics.Profile} {Envs : Store Nat → SEnv UImp → Prop}
    {memIdx : Nat} {m : Module} {ix : ListImports}
    {ans : HostReply → BitVec 32 → SxA MemAtom (BitVec 32)} {L : Set SymStrBytesSExp}
    {reply : UCall Nat → UReply → Prop} {Inv : Store Nat → Prop}
    (hsat : ∀ ρ, MemSat P m memIdx (listRoles ix ans) (readerContract ix.toRead ρ L reply) Inv)
    (hE : ∀ s L, Envs s L → ReplyEnvs reply s L) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (Env (BitVec 32) SymStrBytesSExp)) :
    listReaderLang P Envs memIdx m ix ans .trap oa Rhos ⊆ L := by
  refine readerLang_trap_subset hoa (cert := fun hist h =>
      ∀ ρ : Env (BitVec 32) SymStrBytesSExp,
      (∀ p ∈ hist, (sexpR MemAtom (BitVec 32)).valid ρ p.1 ∧
        (sexpR MemAtom (BitVec 32)).ok ρ p.1 p.2) → ∀ t, ρ h = some t → t ∈ L)
    (fun ρ hist h hh hc => hc ρ hh) ?_ Rhos
  rintro _ ⟨ts, hts, rfl⟩ u v h hu ρ hreads
  obtain ⟨u', v', hd, rfl⟩ := inputsOf_split (e := REv.enter) (by simp) hu
  have hall : ∀ y, Tag.inp y ∈ u' → (readerContract ix.toRead ρ L reply).ans y := by
    rintro y hy q a rfl
    exact hreads (q, a) (mem_reads (mem_inputsOf_of_inp hy))
  obtain ⟨o, hpre, hc | ⟨w, hd'⟩⟩ := tagTraces_pre (hsat ρ) hE hts hd hall
  · exact hpre h hc
  · exact absurd hd' listRead_ne_accept

/-- **`listMod ix` accepts only lists of two members of `S`**, for a child reader of kind
`S`. -/
theorem listMod_sound (P : Profile) {ix : ListImports} (hok : listOk ix = true)
    {ans : HostReply → BitVec 32 → SxA MemAtom (BitVec 32)} {S : Set SymStrBytesSExp}
    (hS : ChildKind ans S) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (Env (BitVec 32) SymStrBytesSExp)) :
    listReaderLang P (ReplyEnvs itemsReply) 0 (listMod ix) ix ans .trap oa Rhos ⊆ pairsOf S :=
  listReaderLang_subset (fun ρ => list_sat P hok hS ρ) (fun _ _ h => h) hoa Rhos

/-- **`symListMod` accepts only lists of two symbols.** -/
theorem symListMod_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (Env (BitVec 32) SymStrBytesSExp)) :
    listReaderLang P (ReplyEnvs itemsReply) 0 symListMod {} symTextAns .trap oa Rhos ⊆
      symPairs :=
  listMod_sound P listOk_sym symTextAns_kind hoa Rhos

/-- **`blobListMod` accepts only lists of two blobs.** -/
theorem blobListMod_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (Env (BitVec 32) SymStrBytesSExp)) :
    listReaderLang P (ReplyEnvs itemsReply) 0 blobListMod blobImports blobAns .trap oa Rhos ⊆
      blobPairs :=
  listMod_sound P listOk_blob blobAns_kind hoa Rhos

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck
