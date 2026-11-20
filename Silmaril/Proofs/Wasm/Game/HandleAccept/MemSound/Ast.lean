module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Ast.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Cons

/-!
# Proofs: the tagged-node (AST) writer through linear memory

* Decoding: `astAccept_isAccept`, `astWrite_isWrite` (the roles decode accepts at calls and
  writes at answers, so the generic bridge `rolesWriterLang_subset` applies), `tagNode_eq`,
  `astWrite_eq`; memory facts `segment_nil` (an empty segment in bounds) and
  `segment_of_bytesAt`.
* `ast_sat`: in a fixed environment `ρ` (no sentinel), `astMod` meets the writer contract
  `roleWriterContract (astRoles {}) (astW strSig) none ρ {f(a)} hiReply`: the first
  `tag(16, 1, 0, 0)` observes `61` (the name `a`) and no children, so its handle `r₁` denotes the
  leaf `a`; the module stores `r₁` at `[0, 4)` and `66` at `16`; the second `tag(16, 1, 0, 1)`
  observes the name `f` and the one child handle `r₁` (the store at `16` is disjoint from
  `[0, 4)`), so its handle `r₂` denotes `f(a)`, and `accept(r₂)` names it.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Ast

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept Silmaril.Accept.IO Silmaril.Accept.Handle
  Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.Cons
  Silmaril.Wasm.Game.HandleAccept.MemSound.Ast
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post bytesAt Region)

/-! ## The decoder -/

theorem astAccept_isAccept {ix : AstImports} {o : Callout} {e : AstWEv}
    (h : astAccept ix o = some e) : ∃ h, e = .accept h := by
  unfold astAccept at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨h, -, rfl⟩ := h
    exact ⟨h, rfl⟩
  · cases h

theorem astWrite_isWrite {ix : AstImports} {o : Callout} {w : HostReply} {e : AstWEv}
    (h : astWrite ix o w = some e) : ∃ op args r, e = .write op args r := by
  unfold astWrite at h
  rcases hr : replyI32 w with _ | r
  · simp [hr] at h
  · simp only [hr] at h
    split_ifs at h
    · rcases ht : Callout.tagNode o with _ | ⟨name, hs⟩
      · simp [ht] at h
      · simp only [ht, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
          Option.some.injEq] at h
        exact ⟨_, _, _, h.symm⟩
    · simp at h

theorem astAccept_eq_none {o : Callout} (h : o.imp ≠ ("ast", "accept")) :
    astAccept {} o = none := by
  simp [astAccept, h]

theorem tagNode_eq {o : Callout} {tp tl cp n : BitVec 32} {bs cs : List UInt8} {name : String}
    {hs : List (BitVec 32)} (ha : o.args = [.i32 tp, .i32 tl, .i32 cp, .i32 n])
    (h1 : o.segment tp.toNat tl.toNat = some bs) (h2 : utf8? bs = some name)
    (h3 : o.segment cp.toNat (4 * n.toNat) = some cs) (h4 : le32s cs = some hs) :
    Callout.tagNode o = some (name, hs) := by
  unfold Callout.tagNode
  rw [ha]
  simp only [Val.i32]
  refine Option.bind_eq_some_iff.2 ⟨bs, h1, ?_⟩
  refine Option.bind_eq_some_iff.2 ⟨name, h2, ?_⟩
  refine Option.bind_eq_some_iff.2 ⟨cs, h3, ?_⟩
  rw [h4]
  rfl

theorem astWrite_eq {o : Callout} {w : HostReply} {name : String} {hs : List (BitVec 32)}
    {r : BitVec 32} (hi : o.imp = ("ast", "tag")) (ht : Callout.tagNode o = some (name, hs))
    (hr : replyI32 w = some r) : astWrite {} o w = some (.write ⟨name, ()⟩ hs r) := by
  simp [astWrite, hr, hi, ht]

/-! ## Memory facts -/

/-- An empty segment in bounds. -/
theorem segment_nil {o : Callout} {b : ByteArray} (ho : o.mem = some b) (a : Nat)
    (h : a ≤ b.size) : o.segment a 0 = some [] := by
  unfold Callout.segment
  rw [ho, Option.bind_eq_bind, Option.bind_some, readBytes_toList (by omega)]
  simp [bytesAt]

/-- A segment in bounds is the region's bytes. -/
theorem segment_of_bytesAt {o : Callout} {b : ByteArray} (ho : o.mem = some b) {a n : Nat}
    (h : a + n ≤ b.size) {L : List UInt8} (hL : bytesAt b ⟨a, n⟩ = L) : o.segment a n = some L := by
  unfold Callout.segment
  rw [ho, Option.bind_eq_bind, Option.bind_some, readBytes_toList h, hL]

theorem le32s_one (r : BitVec 32) :
    le32s (Memory.encodeLE 4 r.toNat).data.toList = some [r] := by
  rw [← List.append_nil (Memory.encodeLE 4 r.toNat).data.toList, le32s_encode]
  rfl

theorem utf8_a : utf8? [0x61] = some "a" := by decide +kernel

theorem utf8_f : utf8? [0x66] = some "f" := by decide +kernel

/-! ## The instantiated module -/

/-- The default value of the local. -/
def astD : List (Option Val) := [some (.i32 0)]

/-- The shape of the instantiated module. -/
def astOk : Bool :=
  match prep astMod with
  | some (c, st) => st.isNone && c.code.isEmpty && c.frame.module.mems == [0] &&
      exportFuncAddrs c.frame.module == [2] && c.store.mems.length == 1 &&
      (match c.store.funcs with
       | [f₀, f₁, f₂] => stubOk 0 4 f₀ && stubOk 1 1 f₁ &&
          fnOk [.i32] astBody 0 0 [0, 1, 2] [0] astD f₂
       | _ => false)
  | none => false

theorem astOk_true : astOk = true := by decide +kernel

theorem ast_facts {c : Config Nat} {st : Option FuncIdx} (hp : prep astMod = some (c, st)) :
    st = none ∧ c.code = [] ∧ c.frame.module.mems = [0] ∧ exportFuncAddrs c.frame.module = [2] ∧
    c.store.mems.length = 1 ∧ ∃ f₀ f₁ f₂, c.store.funcs = [f₀, f₁, f₂] ∧
      stubOk 0 4 f₀ = true ∧ stubOk 1 1 f₁ = true ∧
      fnOk [.i32] astBody 0 0 [0, 1, 2] [0] astD f₂ = true := by
  have h := astOk_true
  unfold astOk at h
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
def astInv (s : Store Nat) : Prop :=
  ∃ c st, prep astMod = some (c, st) ∧ s.funcs = c.store.funcs ∧ s.mems.length = 1

/-- The writer contract in the fixed environment `ρ`. -/
abbrev astK (ρ : Env (BitVec 32) (AST strSig)) : MemContract AstWEv :=
  roleWriterContract (astRoles {}) (astW strSig) none ρ {faTree} hiReply

/-- The import `tag`. -/
abbrev impTag : Import := ⟨"ast", "tag", .func ⟨0⟩⟩
/-- The import `accept`. -/
abbrev impAcc : Import := ⟨"ast", "accept", .func ⟨1⟩⟩

/-- Calls of other imports than `accept` are always allowed. -/
theorem pre_other {ρ : Env (BitVec 32) (AST strSig)} {i : Import} {s : Store Nat}
    {args : List Val} (hi : (i.moduleName, i.name) ≠ ("ast", "accept")) :
    (astK ρ).pre (calloutIn i (some 0) s args) := by
  intro h hd
  change astAccept {} _ = _ at hd
  rw [astAccept_eq_none hi] at hd
  cases hd

/-! ## Every-run proof -/

/-- **The body of `run`**, in the fixed environment `ρ`. -/
theorem ast_body {P : Profile} {ρ : Env (BitVec 32) (AST strSig)} {f₀ f₁ : FuncInst Nat}
    (h0 : stubOk 0 4 f₀ = true) (h1 : stubOk 1 1 f₁ = true)
    {F : Frame} (hFf : F.module.funcs = [0, 1, 2]) (hFm : F.module.mems = [0])
    (hFl : F.locals = astD) {s : Store Nat} {fs : List (FuncInst Nat)}
    (hfs : fs = [f₀, f₁] ++ fs.drop 2) (hsf : s.funcs = fs) (hml : s.mems.length = 1)
    (hinv : ∀ s', s'.funcs = fs → s'.mems.length = 1 → astInv s') {Q : Post Nat}
    (hQ : BodyExits astInv Q) :
    HWP P (memHost astMod (some 0) (astRoles {}) (astK ρ)) s F
      (vals [] ++ expression astBody) Q := by
  obtain ⟨ps₀, rs₀, hc₀, he₀, hn₀⟩ := stubOk_spec h0
  obtain ⟨ps₁, rs₁, hc₁, he₁, hn₁⟩ := stubOk_spec h1
  have hf0 : ∀ s' : Store Nat, s'.funcs = fs → s'.funcs[0]? = some f₀ := fun s' h => by
    rw [h, hfs]; rfl
  have hf1 : ∀ s' : Store Nat, s'.funcs = fs → s'.funcs[1]? = some f₁ := fun s' h => by
    rw [h, hfs]; rfl
  have htrap : ∀ s' (F' : Frame), s'.funcs = fs → s'.mems.length = 1 → Q s' F' .trap :=
    fun s' F' h h' => (hQ s' (hinv s' h h') F').2.2.1
  have hthrow : ∀ s' (F' : Frame) a, s'.funcs = fs → s'.mems.length = 1 → Q s' F' (.throw a) :=
    fun s' F' a h h' => (hQ s' (hinv s' h h') F').2.2.2 a
  unfold astBody
  -- "a" at 16
  refine X.i32Const (us := []) ?_
  refine X.i32Const (us := [] ++ [.i32 16]) ?_
  refine X.storePack (us := []) hFm hml (htrap s F hsf hml) fun mi₀ b₀ hmi₀ hst₀ => ?_
  obtain ⟨-, hl₁, hf₁⟩ := setMem_mems (mi := { mi₀ with bytes := b₀ }) hml
  -- tag(16, 1, 0, 0)
  refine X.i32Const (us := []) ?_
  refine X.i32Const (us := [] ++ [.i32 16]) ?_
  refine X.i32Const (us := [] ++ [.i32 16] ++ [.i32 1]) ?_
  refine X.i32Const (us := [] ++ [.i32 16] ++ [.i32 1] ++ [.i32 0]) ?_
  have htn₁ : Callout.tagNode (calloutIn impTag (some 0) (s.setMem 0 { mi₀ with bytes := b₀ })
      [.i32 16, .i32 1, .i32 0, .i32 0]) = some ("a", []) :=
    tagNode_eq rfl ((segment_of_store hst₀ _ (memOf_setMem hml)).trans (by decide)) utf8_a
      (segment_nil (memOf_setMem hml) 0 (Nat.zero_le _)) rfl
  refine hwp_call (us := []) (args := [.i32 16, .i32 1, .i32 0, .i32 0]) (x := ⟨0⟩) (k := 0)
    (fk := f₀) (i := impTag) (by rw [hFf]; rfl) (hf0 _ (hf₁.trans hsf)) hc₀ he₀ (by simp [hn₀])
    rfl (pre_other (by decide)) ?_
  rintro s₂ r ⟨⟨hfs₂, hml₂⟩, hshape⟩ hans
  have hfs₂' : s₂.funcs = fs := hfs₂.trans (hf₁.trans hsf)
  have hml₂' : s₂.mems.length = 1 := hml₂.trans hl₁
  refine ⟨fun res hr => ?_, fun _ => htrap s₂ F hfs₂' hml₂',
    fun a _ => hthrow s₂ F a hfs₂' hml₂'⟩
  obtain ⟨r₁, rfl⟩ := (hshape res hr).1 rfl
  subst hr
  have hρ₁ : ρ r₁ = some leafA := by
    rcases hans _ (astWrite_eq rfl htn₁ rfl) _ _ _ rfl with h | ⟨t, ht, hρ⟩
    · cases h
    · have hb : (astW strSig).built ρ ⟨"a", ()⟩ [] = some leafA := rfl
      rw [hb] at ht
      rw [hρ]
      exact ht.symm
  refine X.localSet (us := []) (x := ⟨0⟩) (by simp [hFl, astD, Idx.toNat]) ?_
  -- the handle at 0
  refine X.i32Const (us := []) ?_
  refine X.localGet (us := [] ++ [.i32 0]) (v := .i32 r₁) ?_ ?_
  · simp [Frame.local?, Frame.setLocal, hFl, astD, Idx.toNat]
  refine X.store32 (us := []) hFm hml₂' (htrap s₂ _ hfs₂' hml₂') fun mi₂ b₂ hmi₂ hst₂ => ?_
  obtain ⟨hm₃, hl₃, hf₃⟩ := setMem_mems (mi := { mi₂ with bytes := b₂ }) hml₂'
  -- "f" at 16
  refine X.i32Const (us := []) ?_
  refine X.i32Const (us := [] ++ [.i32 16]) ?_
  refine X.storePack (us := []) hFm hl₃ (htrap _ _ (hf₃.trans hfs₂') hl₃)
    fun mi₃ b₃ hmi₃ hst₃ => ?_
  obtain rfl : mi₃ = { mi₂ with bytes := b₂ } := Option.some.inj (hmi₃.symm.trans hm₃)
  obtain ⟨-, hl₄, hf₄⟩ := setMem_mems (mi := { mi₂ with bytes := b₃ }) hl₃
  have hfs₄ : ((s₂.setMem 0 { mi₂ with bytes := b₂ }).setMem 0 { mi₂ with bytes := b₃ }).funcs
      = fs := hf₄.trans (hf₃.trans hfs₂')
  -- tag(16, 1, 0, 1)
  have h₀ : bytesAt b₃ ⟨0, 4⟩ = (Memory.encodeLE 4 r₁.toNat).data.toList := by
    rw [Silmaril.Wasm.Logic.Core.bytesAt_store_disjoint hst₃ (.inr (by decide))]
    exact bytes_of_store32 hst₂
  have hz : 0 + 4 ≤ b₃.size := by
    have := store_inBounds hst₃; simp [effAddr, PackSize.width] at this ⊢; omega
  have htn₂ : Callout.tagNode (calloutIn impTag (some 0)
      ((s₂.setMem 0 { mi₂ with bytes := b₂ }).setMem 0 { mi₂ with bytes := b₃ })
      [.i32 16, .i32 1, .i32 0, .i32 1]) = some ("f", [r₁]) :=
    tagNode_eq rfl ((segment_of_store hst₃ _ (memOf_setMem hl₃)).trans (by decide)) utf8_f
      (segment_of_bytesAt (memOf_setMem hl₃) hz h₀) (le32s_one r₁)
  refine X.i32Const (us := []) ?_
  refine X.i32Const (us := [] ++ [.i32 16]) ?_
  refine X.i32Const (us := [] ++ [.i32 16] ++ [.i32 1]) ?_
  refine X.i32Const (us := [] ++ [.i32 16] ++ [.i32 1] ++ [.i32 0]) ?_
  refine hwp_call (us := []) (args := [.i32 16, .i32 1, .i32 0, .i32 1]) (x := ⟨0⟩) (k := 0)
    (fk := f₀) (i := impTag) (by show F.module.funcs[_]? = _; rw [hFf]; rfl) (hf0 _ hfs₄) hc₀
    he₀ (by simp [hn₀]) rfl (pre_other (by decide)) ?_
  rintro s₅ r ⟨⟨hfs₅, hml₅⟩, hshape⟩ hans
  have hfs₅' : s₅.funcs = fs := hfs₅.trans hfs₄
  have hml₅' : s₅.mems.length = 1 := hml₅.trans hl₄
  refine ⟨fun res hr => ?_, fun _ => htrap s₅ _ hfs₅' hml₅',
    fun a _ => hthrow s₅ _ a hfs₅' hml₅'⟩
  obtain ⟨r₂, rfl⟩ := (hshape res hr).1 rfl
  subst hr
  have hρ₂ : ρ r₂ = some faTree := by
    rcases hans _ (astWrite_eq rfl htn₂ rfl) _ _ _ rfl with h | ⟨t, ht, hρ⟩
    · cases h
    · have hb : (astW strSig).built ρ ⟨"f", ()⟩ [r₁] = some faTree := by
        unfold Writer.built Env.lookupAll
        rw [List.mapM_cons, List.mapM_nil, hρ₁]
        rfl
      rw [hb] at ht
      rw [hρ]
      exact ht.symm
  -- accept(r₂)
  refine hwp_call (us := []) (args := [.i32 r₂]) (x := ⟨1⟩) (k := 1) (fk := f₁)
    (i := impAcc) (by show F.module.funcs[_]? = _; rw [hFf]; rfl) (hf1 _ hfs₅') hc₁ he₁
    (by simp [hn₁]) rfl ?_ ?_
  · intro h hd t ht
    simp [astRoles, astAccept, calloutIn, Callout.args1, Callout.i32?, Val.i32] at hd
    subst hd
    rw [hρ₂] at ht
    cases ht
    rfl
  rintro s₆ r ⟨⟨hfs₆, hml₆⟩, hshape⟩ -
  have hfs₆' : s₆.funcs = fs := hfs₆.trans hfs₅'
  have hml₆' : s₆.mems.length = 1 := hml₆.trans hml₅'
  refine ⟨fun res hr => ?_, fun _ => htrap s₆ _ hfs₆' hml₆',
    fun a _ => hthrow s₆ _ a hfs₆' hml₆'⟩
  obtain rfl := (hshape res hr).2 rfl
  exact X.done (hQ s₆ (hinv s₆ hfs₆' hml₆') _).1

/-- **`astMod` meets the writer contract** in every fixed environment, for every profile. -/
theorem ast_sat (P : Profile) (ρ : Env (BitVec 32) (AST strSig)) :
    MemSat P astMod 0 (astRoles {}) (astK ρ) astInv := by
  intro mt Is c₀ hI
  obtain ⟨c, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, hexp, hml, f₀, f₁, f₂, hf, h0, h1, h2⟩ := ast_facts hp
  have hmem : (c.withStart none).frame.module.mems[0]? = some 0 := by
    simp [Config.withStart, hmems]
  rw [hmem]
  refine ⟨fun n => Safe.of_exits (o := .normal []) (by simp [Config.withStart, hcode]; rfl)
    (fun _ _ => ⟨c, none, hp, rfl, hml⟩), ?_⟩
  intro a ha
  rw [← haddr, hexp] at ha
  obtain rfl : a = 2 := by simpa using ha
  obtain ⟨code, ps, rs, hcode2, hloc, hbody, he, hps, hrs, hfuncs, hmems2, hD⟩ := fnOk_spec h2
  have hinv : ∀ s', s'.funcs = c.store.funcs → s'.mems.length = 1 → astInv s' :=
    fun s' h h' => ⟨c, none, hp, h, h'⟩
  have hfi : ∀ s, astInv s → s.funcs = c.store.funcs := by
    rintro s ⟨c', st', hp', hfs, _⟩
    have hcc : c' = c := (Prod.mk.inj (Option.some.inj (hp'.symm.trans hp))).1
    rw [hfs, hcc]
  refine export_valid (fi := f₂) (fun s hs => by rw [hfi s hs, hf]; rfl) hcode2 he hrs ?_
  intro s args hs hok Q hQ
  have hargs : args = [] := by
    have := args_length (by rw [hfi s hs, hf]; rfl) he hok
    rw [hps] at this
    exact List.eq_nil_of_length_eq_zero this
  subst hargs
  rw [hbody, hloc]
  have hml' : s.mems.length = 1 := by obtain ⟨_, _, _, _, h⟩ := hs; exact h
  exact ast_body h0 h1 (by simp [Frame.forCall, hfuncs]) (by simp [Frame.forCall, hmems2])
    (by simp [Frame.forCall, hD]) (fs := c.store.funcs) (by rw [hf]; rfl) (hfi s hs)
    hml' hinv hQ

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Ast
