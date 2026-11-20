module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Items.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Rules

/-!
# Proofs: `itemsMod` accepts only lists of two children

* the returned `list<i32>` (`itemsList mem 0`) has as many handles as the little-endian word at
  `[4, 8)` says (`itemsList_spec`): the length the module loads is the length the decoder reads;
* in a fixed environment `ρ`, the reader contract says that the decoded read
  `read (items h) (items hs)` is correct in `ρ`: `h` denotes a list whose children the handles
  `hs` denote, so it has `hs.length` children; `check_body` proves the body under the most
  general host of that contract: `accept(h)` is reached only when that length is `2`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Items

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.Items
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post bytesAt Region leNat)

/-! ## The returned list -/

theorem le32s_length : ∀ {bs : List UInt8} {ws : List (BitVec 32)}, le32s bs = some ws →
    bs.length = 4 * ws.length
  | [], ws, h => by simp only [le32s, Option.some.injEq] at h; subst h; rfl
  | [_], _, h => by simp [le32s] at h
  | [_, _], _, h => by simp [le32s] at h
  | [_, _, _], _, h => by simp [le32s] at h
  | _ :: _ :: _ :: _ :: rest, ws, h => by
      simp only [le32s, Option.map_eq_some_iff] at h
      obtain ⟨hs, hr, rfl⟩ := h
      have := le32s_length hr
      simp only [List.length_cons, this]
      omega

theorem le32s_four : ∀ (l : List UInt8), l.length = 4 → ∀ rest : List UInt8,
    le32s (l ++ rest) = (le32s rest).map (BitVec.ofNat 32 (leNat l) :: ·)
  | [a, b, c, d], _, rest => by
      simp only [List.cons_append, List.nil_append, le32s, leNat, List.foldr]
      congr 1
      funext hs
      congr 2
      omega

theorem segOf_eq {mem : ByteArray} {p n : Nat} {bs : List UInt8} (h : segOf mem p n = some bs) :
    p + n ≤ mem.size ∧ bs = bytesAt mem ⟨p, n⟩ := by
  unfold segOf at h
  by_cases hb : p + n ≤ mem.size
  · rw [readBytes_toList hb] at h
    exact ⟨hb, (Option.some.inj h).symm⟩
  · simp [Memory.readBytes, hb] at h

/-- **The length of the returned list is the word at `[4, 8)`.** -/
theorem itemsList_spec {mem : ByteArray} {hs : List (BitVec 32)}
    (h : itemsList mem 0 = some hs) :
    8 ≤ mem.size ∧ hs.length = (BitVec.ofNat 32 (leNat (bytesAt mem ⟨4, 4⟩))).toNat := by
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
  obtain ⟨-, rfl⟩ := hpn
  obtain ⟨hb, rfl⟩ := segOf_eq hbs
  have h1 := le32s_length hhs
  have h2 := Silmaril.Wasm.Logic.Core.length_bytesAt (B := mem) (r := ⟨_, 4 * _⟩)
    (by simp only [Region.InBounds, Region.stop]; exact hb)
  refine ⟨by simpa using hb₈, ?_⟩
  dsimp only at h1 h2 ⊢
  omega

/-! ## Instance facts -/

/-- The default values of the locals: none. -/
def itemsD : List (Option Val) := []

/-- The shape of the instantiated module. -/
def itemsOk : Bool :=
  match prep itemsMod with
  | some (c, st) => st.isNone && c.code.isEmpty && c.frame.module.mems == [0] &&
      exportFuncAddrs c.frame.module == [2] && c.store.mems.length == 1 &&
      (match c.store.funcs with
       | [f₀, f₁, f₂] => stubOk 0 2 f₀ && stubOk 1 1 f₁ &&
          fnOk [] itemsBody 1 0 [0, 1, 2] [0] itemsD f₂
       | _ => false)
  | none => false

theorem itemsOk_true : itemsOk = true := by decide +kernel

theorem items_facts {c : Config Nat} {st : Option FuncIdx} (hp : prep itemsMod = some (c, st)) :
    st = none ∧ c.code = [] ∧ c.frame.module.mems = [0] ∧ exportFuncAddrs c.frame.module = [2] ∧
    c.store.mems.length = 1 ∧ ∃ f₀ f₁ f₂, c.store.funcs = [f₀, f₁, f₂] ∧
      stubOk 0 2 f₀ = true ∧ stubOk 1 1 f₁ = true ∧
      fnOk [] itemsBody 1 0 [0, 1, 2] [0] itemsD f₂ = true := by
  have h := itemsOk_true
  unfold itemsOk at h
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
def itemsInv (s : Store Nat) : Prop :=
  ∃ c st, prep itemsMod = some (c, st) ∧ s.funcs = c.store.funcs ∧ s.mems.length = 1

/-- The reader contract in the fixed environment `ρ`. -/
abbrev itemsK (ρ : Env (BitVec 32) SymStrBytesSExp) : MemContract MemREv :=
  readerContract {} ρ twoL itemsReply

/-! ## Rules -/

theorem bool32_eq_zero {b : Bool} (h : bool32 b = 0) : b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)

/-- An `i32` load from memory `0` of a store with one memory: it traps, or pushes the word. -/
theorem X.load32 {P : Profile} {host : HostSemantics Nat} {s : Store Nat} {F : Frame}
    {us : List Val} {is : List Instr} {Q : Post Nat} {addr : BitVec 32} {arg : MemArg}
    (hF : F.module.mems = [0]) (hl : s.mems.length = 1) (htrap : Q s F .trap)
    (h : ∀ mi c, s.mems[0]? = some mi →
      Memory.load mi.bytes (effAddr addr.toNat arg) (IntType.i32.width / 8) = some c →
      HWP P host s F (vals (us ++ [.num ⟨.int .i32, c.setWidth 32⟩]) ++ expression is) Q) :
    HWP P host s F (vals (us ++ [.i32 addr]) ++ expression (.intLoad .i32 none ⟨0⟩ arg :: is))
      Q := by
  obtain ⟨mi, hmi⟩ : ∃ mi, s.mems[0]? = some mi :=
    ⟨s.mems[0]'(by omega), List.getElem?_eq_getElem _⟩
  have hm := mem?_of hF hmi
  rcases hld : Memory.load mi.bytes (effAddr addr.toNat arg) (IntType.i32.width / 8) with _ | c
  · refine Wp.intLoad_oob (m := .part) (a := .i32) (i := addr) (t := .i32) hm ?_ htrap
    unfold Memory.load Memory.readBytes at hld
    split at hld
    · cases hld
    · rename_i hb
      exact Nat.lt_of_not_le hb
  · exact Wp.intLoad (m := .part) (a := .i32) (i := addr) (t := .i32) hm hld (h mi c hmi hld)

/-! ## The body -/

theorem i32?_some {v : Val} {h : BitVec 32} (hi : Callout.i32? v = some h) : v = .i32 h := by
  unfold Callout.i32? at hi
  split at hi
  · cases hi; rfl
  · cases hi

theorem readAccept_inv {o : Callout} {v : Val} {h : BitVec 32} (ha : o.args = [v])
    (hd : readAccept {} o = some (.accept h)) : v = .i32 h := by
  unfold readAccept at hd
  split at hd
  · simp only [ha, Callout.args1, Option.map_eq_some_iff, REv.accept.injEq] at hd
    obtain ⟨a, hi, rfl⟩ := hd
    exact i32?_some hi
  · cases hd

/-- What the reader contract says after `items(h, 0)` returned in the store `s'`. -/
theorem items_ans {ρ : Env (BitVec 32) SymStrBytesSExp} {s s' : Store Nat} {h : BitVec 32}
    {mi : MemInst} (hmi : s'.mems[0]? = some mi)
    (hans : ∀ y, itemsRead {} (calloutIn ⟨"sexp", "items", .func ⟨0⟩⟩ (some 0) s [.i32 h, .i32 0])
      ⟨.values [], memOf (some 0) s'⟩ = some y → (itemsK ρ).ans y) :
    ∃ hs, itemsList mi.bytes 0 = some hs ∧ ∃ cs, ρ h = some (SExp.ofList cs) ∧
      hs.length = cs.length := by
  have hm : memOf (some 0) s' = some mi.bytes := by simp [memOf, hmi]
  have hd : itemsRead {} (calloutIn ⟨"sexp", "items", .func ⟨0⟩⟩ (some 0) s [.i32 h, .i32 0])
      ⟨.values [], memOf (some 0) s'⟩ =
      some (.read (.items h) (itemsAns ⟨.values [], memOf (some 0) s'⟩ 0)) := by
    simp [itemsRead, calloutIn, Val.i32]
  obtain ⟨-, hok⟩ := hans _ hd _ _ rfl
  unfold itemsAns at hok
  rw [hm] at hok
  simp only [Option.bind_some] at hok
  split at hok
  · rename_i hs hhs
    obtain ⟨cs, hρ, hall⟩ := hok
    exact ⟨hs, by simpa using hhs, cs, hρ, hall.length_eq⟩
  · exact hok.elim

/-- **The body of `check`**, in the fixed environment `ρ`. -/
theorem check_body {P : Profile} {ρ : Env (BitVec 32) SymStrBytesSExp} {f₀ f₁ : FuncInst Nat}
    (h0 : stubOk 0 2 f₀ = true) (h1 : stubOk 1 1 f₁ = true) {v : Val} {F : Frame}
    (hFf : F.module.funcs = [0, 1, 2]) (hFm : F.module.mems = [0]) (hFl : F.locals = [some v])
    {s : Store Nat} {fs : List (FuncInst Nat)}
    (hfs : fs = [f₀, f₁] ++ fs.drop 2) (hsf : s.funcs = fs) (hml : s.mems.length = 1)
    (hinv : ∀ s', s'.funcs = fs → s'.mems.length = 1 → itemsInv s') {Q : Post Nat}
    (hQ : BodyExits itemsInv Q) :
    HWP P (memHost itemsMod (some 0) (memReadRoles {}) (itemsK ρ)) s F
      (vals [] ++ expression itemsBody) Q := by
  obtain ⟨ps₀, rs₀, hc₀, he₀, hn₀⟩ := stubOk_spec h0
  obtain ⟨ps₁, rs₁, hc₁, he₁, hn₁⟩ := stubOk_spec h1
  have htrap : ∀ s' (F' : Frame), s'.funcs = fs → s'.mems.length = 1 → Q s' F' .trap :=
    fun s' F' h h' => (hQ s' (hinv s' h h') F').2.2.1
  have hthrow : ∀ s' (F' : Frame) a, s'.funcs = fs → s'.mems.length = 1 → Q s' F' (.throw a) :=
    fun s' F' a h h' => (hQ s' (hinv s' h h') F').2.2.2 a
  have hv : F.local? ⟨0⟩ = some (some v) := by simp [Frame.local?, hFl, Idx.toNat]
  unfold itemsBody
  -- items(h, 0)
  refine X.localGet (us := []) hv ?_
  refine X.i32Const (us := [] ++ [v]) ?_
  refine hwp_call (us := []) (args := [v, .i32 0]) (x := ⟨0⟩) (k := 0) (fk := f₀)
    (i := ⟨"sexp", "items", .func ⟨0⟩⟩) (by rw [hFf]; rfl) (by rw [hsf, hfs]; rfl) hc₀ he₀
    (by simp [hn₀]) rfl ?_ ?_
  · intro h hd
    simp [readAccept, calloutIn] at hd
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
      ∃ cs, ρ h = some (SExp.ofList cs) ∧ hs.length = cs.length := by
    rintro h rfl
    exact items_ans (s := s) hmi₁ hans
  -- the length
  refine X.i32Const (us := []) ?_
  refine X.load32 (us := []) hFm hml₁' (htrap s₁ F hfs₁' hml₁') fun mi c hmi hld => ?_
  obtain rfl : mi = mi₁ := Option.some.inj (hmi.symm.trans hmi₁)
  refine X.neConst (us := []) (x := c.setWidth 32) ?_
  refine X.if_ (us := []) (fun _ => ?_) (fun hc => ?_)
  · exact X.return_ (us := []) ((BodyExits.label hQ s₁ (hinv s₁ hfs₁' hml₁') F).1 [])
  -- accept(h)
  have hc2 : c.setWidth 32 = 2 := bne_eq_false_iff_eq.1 (bool32_eq_zero hc)
  refine X.localGet (us := []) hv ?_
  refine hwp_call (us := []) (args := [v]) (x := ⟨1⟩) (k := 1) (fk := f₁)
    (i := ⟨"sexp", "accept", .func ⟨1⟩⟩) (by rw [hFf]; rfl) (by rw [hfs₁', hfs]; rfl) hc₁ he₁
    (by simp [hn₁]) rfl ?_ ?_
  · intro h hd t ht
    have hvh : v = .i32 h := readAccept_inv rfl hd
    obtain ⟨hs, hhs, cs, hρ, hlen⟩ := hfact h hvh
    obtain ⟨-, hlen'⟩ := itemsList_spec hhs
    have hld' := Silmaril.Wasm.Logic.Core.load_eq (B := mi.bytes) (a := 4) (n := 4)
      (by have := (itemsList_spec hhs).1; omega)
    have hcn : c.toNat = leNat (bytesAt mi.bytes ⟨4, 4⟩) % 2 ^ (8 * 4) :=
      (congrArg BitVec.toNat (Option.some.inj (hld.symm.trans hld'))).trans
        (BitVec.toNat_ofNat _ _)
    rw [hρ] at ht
    cases ht
    have h2 : cs.length = 2 := by
      rw [← hlen, hlen']
      have h22 : c.toNat % 2 ^ 32 = 2 := by
        have := congrArg BitVec.toNat hc2
        rw [BitVec.toNat_setWidth] at this
        simpa using this
      rw [BitVec.toNat_ofNat]
      simp only [Nat.reduceMul, Nat.reducePow] at h22 hcn ⊢
      omega
    match cs, h2 with
    | [c₁, c₂], _ => exact ⟨c₁, c₂, rfl⟩
  rintro s₂ r ⟨⟨hfs₂, hml₂⟩, hshape⟩ -
  have hfs₂' : s₂.funcs = fs := hfs₂.trans hfs₁'
  have hml₂' : s₂.mems.length = 1 := hml₂.trans hml₁'
  refine ⟨fun res hr => ?_, fun _ => htrap s₂ F hfs₂' hml₂',
    fun a _ => hthrow s₂ F a hfs₂' hml₂'⟩
  obtain rfl := hshape res hr
  exact X.done (hQ s₂ (hinv s₂ hfs₂' hml₂') F).1

/-- **`itemsMod` meets the reader contract** in every fixed environment, for every profile. -/
theorem items_sat (P : Profile) (ρ : Env (BitVec 32) SymStrBytesSExp) :
    MemSat P itemsMod 0 (memReadRoles {}) (itemsK ρ) itemsInv := by
  intro mt Is c₀ hI
  obtain ⟨c, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, hexp, hml, f₀, f₁, f₂, hf, h0, h1, h2⟩ := items_facts hp
  have hmem : (c.withStart none).frame.module.mems[0]? = some 0 := by
    simp [Config.withStart, hmems]
  rw [hmem]
  refine ⟨fun n => Safe.of_exits (o := .normal []) (by simp [Config.withStart, hcode]; rfl)
    (fun _ _ => ⟨c, none, hp, rfl, hml⟩), ?_⟩
  intro a ha
  rw [← haddr, hexp] at ha
  obtain rfl : a = 2 := by simpa using ha
  obtain ⟨code, ps, rs, hcode2, hloc, hbody, he, hps, hrs, hfuncs, hmems2, hD⟩ := fnOk_spec h2
  have hinv : ∀ s', s'.funcs = c.store.funcs → s'.mems.length = 1 → itemsInv s' :=
    fun s' h h' => ⟨c, none, hp, h, h'⟩
  have hfi : ∀ s, itemsInv s → s.funcs = c.store.funcs := by
    rintro s ⟨c', st', hp', hfs, _⟩
    have hcc : c' = c := (Prod.mk.inj (Option.some.inj (hp'.symm.trans hp))).1
    rw [hfs, hcc]
  refine export_valid (fi := f₂) (fun s hs => by rw [hfi s hs, hf]; rfl) hcode2 he hrs ?_
  intro s args hs hok Q hQ
  have hlen1 : args.length = 1 := by
    have := args_length (by rw [hfi s hs, hf]; rfl) he hok
    rw [hps] at this
    exact this
  obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp hlen1
  rw [hbody, hloc]
  have hml' : s.mems.length = 1 := by obtain ⟨_, _, _, _, h⟩ := hs; exact h
  exact check_body (v := v) h0 h1 (by simp [Frame.forCall, hfuncs]) (by simp [Frame.forCall, hmems2])
    (by simp [Frame.forCall]) (fs := c.store.funcs) (by rw [hf]; rfl) (hfi s hs) hml' hinv hQ

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Items
