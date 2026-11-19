module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitPayload

/-!
# Proofs: string payloads through memory, `appMod`

* `strRef_pair`: the `i64` `strRef` stored little-endian is the pair `(24, 1)`;
* `var_node`: a `node(0, 16, 0, 0)` call whose memory holds the pair at `[16, 24)` (the last
  store) and one byte `b` at `[24, 25)` (the store before) decodes to `var str` with no
  children, when `utf8? [b] = some str`;
* `app_sat`: in a fixed environment `ρ` (no sentinel), `appMod` meets the writer contract
  `roleWriterContract (witRoles appSig appTagOf {}) (astW appSig.toAstSig) none ρ {appTree}
  hiReply`: the first `node` reads the string `"f"` through its pair (handle `r₁` denotes
  `var "f"`), the second `"x"` (handle `r₂`), the module stores `r₁`, `r₂` at `[0, 8)` and
  `node(1, 0, 0, 2)` reads no payload and the two handles, so its handle denotes
  `app(var "f", var "x")`, which `accept` names.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitApp

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept Silmaril.Accept.IO Silmaril.Accept.Handle
  Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.Cons
  Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Ast
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WordAtom
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post bytesAt Region)

/-! ## Decoding the string payload -/

/-- The stored `strRef` is the pair `(24, 1)`. -/
theorem strRef_pair :
    readPtrLen ((Memory.encodeLE (IntType.i64.width / 8)
      (BitVec.setWidth (8 * (IntType.i64.width / 8)) strRef).toNat).data.toList.take
        (PTy.width .string)) = some (24, 1, []) := by
  decide +kernel

theorem byte_f : (Memory.encodeLE (PackSize.i8.width / 8)
    (BitVec.setWidth (8 * (PackSize.i8.width / 8)) (0x66 : BitVec 32)).toNat).data.toList =
    [0x66] := by
  decide +kernel

theorem byte_x : (Memory.encodeLE (PackSize.i8.width / 8)
    (BitVec.setWidth (8 * (PackSize.i8.width / 8)) (0x78 : BitVec 32)).toNat).data.toList =
    [0x78] := by
  decide +kernel

theorem utf8_x : utf8? [0x78] = some "x" := by decide +kernel

/-- **A `var` node**: the pair `(24, 1)` stored last at `16`, the byte `b` stored before at
`24`. -/
theorem var_node {o : Callout} {B B₀ B₁ : ByteArray} {c : BitVec 32} {b : UInt8} {str : String}
    (hst₀ : Memory.store B (effAddr (24 : BitVec 32).toNat ⟨0, 0⟩)
      (count := PackSize.i8.width / 8) (c.setWidth _) = some B₀)
    (hst₁ : Memory.store B₀ (effAddr (16 : BitVec 32).toNat ⟨0, 0⟩)
      (count := IntType.i64.width / 8) (strRef.setWidth _) = some B₁)
    (ho : o.mem = some B₁) (ha : o.args = [.i32 0, .i32 16, .i32 0, .i32 0])
    (hb : (Memory.encodeLE (PackSize.i8.width / 8)
      (BitVec.setWidth (8 * (PackSize.i8.width / 8)) c).toNat).data.toList = [b])
    (hu : utf8? [b] = some str) :
    Callout.witNode appSig appTagOf o = some (⟨AppTag.var, (str, ())⟩, []) := by
  have hpay := segment_of_store hst₁ o ho
  have hseg : o.segment 24 1 = some [b] := by
    refine segment_of_bytesAt ho ?_ ?_
    · have h1 := store_inBounds hst₀
      have h2 := Silmaril.Wasm.Logic.Core.size_store hst₁
      simp [effAddr, PackSize.width] at h1
      omega
    · rw [Silmaril.Wasm.Logic.Core.bytesAt_store_disjoint hst₁ (.inl (by decide))]
      have := Silmaril.Wasm.Logic.Core.bytesAt_store_same hst₀
      rw [hb] at this
      exact this
  have hv : readVals o.segment (appSig.params AppTag.var)
      (Memory.encodeLE (IntType.i64.width / 8)
        (BitVec.setWidth (8 * (IntType.i64.width / 8)) strRef).toNat).data.toList =
      some (str, ()) := by
    refine (readVals_single o.segment .string _).trans ?_
    rw [readVal_string strRef_pair hseg hu]
    rfl
  exact witNode_eq ha rfl hpay hv (segment_nil ho 0 (Nat.zero_le _)) rfl rfl

/-! ## The instantiated module -/

/-- The default values of the locals. -/
def appD : List (Option Val) := [some (.i32 0), some (.i32 0)]

/-- The shape of the instantiated module. -/
def appOk : Bool :=
  match prep appMod with
  | some (c, st) => st.isNone && c.code.isEmpty && c.frame.module.mems == [0] &&
      exportFuncAddrs c.frame.module == [2] && c.store.mems.length == 1 &&
      (match c.store.funcs with
       | [f₀, f₁, f₂] => stubOk 0 4 f₀ && stubOk 1 1 f₁ &&
          fnOk [.i32, .i32] appBody 0 0 [0, 1, 2] [0] appD f₂
       | _ => false)
  | none => false

theorem appOk_true : appOk = true := by decide +kernel

theorem app_facts {c : Config Nat} {st : Option FuncIdx} (hp : prep appMod = some (c, st)) :
    st = none ∧ c.code = [] ∧ c.frame.module.mems = [0] ∧ exportFuncAddrs c.frame.module = [2] ∧
    c.store.mems.length = 1 ∧ ∃ f₀ f₁ f₂, c.store.funcs = [f₀, f₁, f₂] ∧
      stubOk 0 4 f₀ = true ∧ stubOk 1 1 f₁ = true ∧
      fnOk [.i32, .i32] appBody 0 0 [0, 1, 2] [0] appD f₂ = true := by
  have h := appOk_true
  unfold appOk at h
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
def appInv (s : Store Nat) : Prop :=
  ∃ c st, prep appMod = some (c, st) ∧ s.funcs = c.store.funcs ∧ s.mems.length = 1

/-- The roles of the example. -/
abbrev appRoles : Roles Unit (WitWEv appSig) Unit Unit := witRoles appSig appTagOf {}

/-- The writer contract in the fixed environment `ρ`. -/
abbrev appK (ρ : Env (BitVec 32) (AST appSig.toAstSig)) : MemContract (WitWEv appSig) :=
  roleWriterContract appRoles (astW appSig.toAstSig) none ρ {appTree} hiReply

/-- Calls of other imports than `accept` are always allowed. -/
theorem pre_other {ρ : Env (BitVec 32) (AST appSig.toAstSig)} {i : Import} {s : Store Nat}
    {args : List Val} (hi : (i.moduleName, i.name) ≠ ("wit", "accept")) :
    (appK ρ).pre (calloutIn i (some 0) s args) := by
  intro h hd
  change witAccept appSig {} _ = _ at hd
  rw [witAccept_eq_none hi] at hd
  cases hd

/-- `var x` from its payload. -/
theorem built_var (ρ : Env (BitVec 32) (AST appSig.toAstSig)) (x : String) :
    (astW appSig.toAstSig).built ρ ⟨AppTag.var, (x, ())⟩ [] = some (varTree x) := rfl

/-- `app(x, y)` from the handles of `x` and `y`. -/
theorem built_app {ρ : Env (BitVec 32) (AST appSig.toAstSig)} {r₁ r₂ : BitVec 32}
    {x y : AST appSig.toAstSig} (h₁ : ρ r₁ = some x) (h₂ : ρ r₂ = some y) :
    (astW appSig.toAstSig).built ρ ⟨AppTag.app, ()⟩ [r₁, r₂] =
      some (AST.node (S := appSig.toAstSig) AppTag.app () [x, y]) := by
  unfold Writer.built Env.lookupAll
  rw [List.mapM_cons, List.mapM_cons, List.mapM_nil, h₁, h₂]
  rfl

/-! ## Every-run proof -/

/-- **The body of `run`**, in the fixed environment `ρ`. -/
theorem app_body {P : Profile} {ρ : Env (BitVec 32) (AST appSig.toAstSig)}
    {f₀ f₁ : FuncInst Nat} (h0 : stubOk 0 4 f₀ = true) (h1 : stubOk 1 1 f₁ = true)
    {F : Frame} (hFf : F.module.funcs = [0, 1, 2]) (hFm : F.module.mems = [0])
    (hFl : F.locals = appD) {s : Store Nat} {fs : List (FuncInst Nat)}
    (hfs : fs = [f₀, f₁] ++ fs.drop 2) (hsf : s.funcs = fs) (hml : s.mems.length = 1)
    (hinv : ∀ s', s'.funcs = fs → s'.mems.length = 1 → appInv s') {Q : Post Nat}
    (hQ : BodyExits appInv Q) :
    HWP P (memHost appMod (some 0) appRoles (appK ρ)) s F
      (vals [] ++ expression appBody) Q := by
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
  unfold appBody
  -- "f" at 24, the pair at 16
  refine X.i32Const (us := []) ?_
  refine X.i32Const (us := [] ++ [.i32 24]) ?_
  refine X.storePack (us := []) hFm hml (htrap s F hsf hml) fun mi₀ b₀ hmi₀ hst₀ => ?_
  obtain ⟨hm₀, hl₀, hf₀⟩ := setMem_mems (mi := { mi₀ with bytes := b₀ }) hml
  refine X.i32Const (us := []) ?_
  refine X.i64Const (us := [] ++ [.i32 16]) ?_
  refine X.store64 (us := []) hFm hl₀ (htrap _ F (hf₀.trans hsf) hl₀)
    fun mi₁ b₁ hmi₁ hst₁ => ?_
  obtain rfl : mi₁ = { mi₀ with bytes := b₀ } := Option.some.inj (hmi₁.symm.trans hm₀)
  obtain ⟨-, hl₁, hf₁⟩ := setMem_mems (mi := { mi₀ with bytes := b₁ }) hl₀
  have hsf₁ : ((s.setMem 0 { mi₀ with bytes := b₀ }).setMem 0 { mi₀ with bytes := b₁ }).funcs
      = fs := hf₁.trans (hf₀.trans hsf)
  -- node(0, 16, 0, 0)
  refine X.i32Const (us := []) ?_
  refine X.i32Const (us := [] ++ [.i32 0]) ?_
  refine X.i32Const (us := [] ++ [.i32 0] ++ [.i32 16]) ?_
  refine X.i32Const (us := [] ++ [.i32 0] ++ [.i32 16] ++ [.i32 0]) ?_
  have hd₁ : Callout.witNode appSig appTagOf (calloutIn impNode (some 0)
      ((s.setMem 0 { mi₀ with bytes := b₀ }).setMem 0 { mi₀ with bytes := b₁ })
      [.i32 0, .i32 16, .i32 0, .i32 0]) =
      some (⟨AppTag.var, ("f", ())⟩, []) :=
    var_node hst₀ hst₁ (memOf_setMem hl₀) rfl byte_f utf8_f
  refine hwp_call (us := []) (args := [.i32 0, .i32 16, .i32 0, .i32 0]) (x := ⟨0⟩) (k := 0)
    (fk := f₀) (i := impNode) (by rw [hFf]; rfl) (hf0 _ hsf₁) hc₀ he₀ (by simp [hn₀])
    rfl (pre_other (by decide)) ?_
  rintro s₂ r ⟨⟨hfs₂, hml₂⟩, hshape⟩ hans
  have hfs₂' : s₂.funcs = fs := hfs₂.trans hsf₁
  have hml₂' : s₂.mems.length = 1 := hml₂.trans hl₁
  refine ⟨fun res hr => ?_, fun _ => htrap s₂ F hfs₂' hml₂',
    fun a _ => hthrow s₂ F a hfs₂' hml₂'⟩
  obtain ⟨r₁, rfl⟩ := (hshape res hr).1 rfl
  subst hr
  have hρ₁ : ρ r₁ = some (varTree "f") := by
    rcases hans _ (witWrite_eq rfl hd₁ rfl) _ _ _ rfl with h | ⟨t, ht, hρ⟩
    · cases h
    · rw [built_var] at ht
      rw [hρ]
      exact ht.symm
  refine X.localSet (us := []) (x := ⟨0⟩) (by simp [hFl, appD, Idx.toNat]) ?_
  let F₁ := F.setLocal ⟨0⟩ (.i32 r₁)
  have hF₁f : F₁.module.funcs = [0, 1, 2] := hFf
  have hF₁m : F₁.module.mems = [0] := hFm
  -- "x" at 24, the pair at 16
  refine X.i32Const (us := []) ?_
  refine X.i32Const (us := [] ++ [.i32 24]) ?_
  refine X.storePack (us := []) hF₁m hml₂' (htrap s₂ _ hfs₂' hml₂') fun mi₂ b₂ hmi₂ hst₂ => ?_
  obtain ⟨hm₂, hl₂, hf₂⟩ := setMem_mems (mi := { mi₂ with bytes := b₂ }) hml₂'
  refine X.i32Const (us := []) ?_
  refine X.i64Const (us := [] ++ [.i32 16]) ?_
  refine X.store64 (us := []) hF₁m hl₂ (htrap _ _ (hf₂.trans hfs₂') hl₂)
    fun mi₃ b₃ hmi₃ hst₃ => ?_
  obtain rfl : mi₃ = { mi₂ with bytes := b₂ } := Option.some.inj (hmi₃.symm.trans hm₂)
  obtain ⟨-, hl₃, hf₃⟩ := setMem_mems (mi := { mi₂ with bytes := b₃ }) hl₂
  have hsf₃ : ((s₂.setMem 0 { mi₂ with bytes := b₂ }).setMem 0 { mi₂ with bytes := b₃ }).funcs
      = fs := hf₃.trans (hf₂.trans hfs₂')
  -- node(0, 16, 0, 0)
  refine X.i32Const (us := []) ?_
  refine X.i32Const (us := [] ++ [.i32 0]) ?_
  refine X.i32Const (us := [] ++ [.i32 0] ++ [.i32 16]) ?_
  refine X.i32Const (us := [] ++ [.i32 0] ++ [.i32 16] ++ [.i32 0]) ?_
  have hd₂ : Callout.witNode appSig appTagOf (calloutIn impNode (some 0)
      ((s₂.setMem 0 { mi₂ with bytes := b₂ }).setMem 0 { mi₂ with bytes := b₃ })
      [.i32 0, .i32 16, .i32 0, .i32 0]) =
      some (⟨AppTag.var, ("x", ())⟩, []) :=
    var_node hst₂ hst₃ (memOf_setMem hl₂) rfl byte_x utf8_x
  refine hwp_call (us := []) (args := [.i32 0, .i32 16, .i32 0, .i32 0]) (x := ⟨0⟩) (k := 0)
    (fk := f₀) (i := impNode) (by rw [hF₁f]; rfl) (hf0 _ hsf₃) hc₀ he₀
    (by simp [hn₀]) rfl (pre_other (by decide)) ?_
  rintro s₄ r ⟨⟨hfs₄, hml₄⟩, hshape⟩ hans
  have hfs₄' : s₄.funcs = fs := hfs₄.trans hsf₃
  have hml₄' : s₄.mems.length = 1 := hml₄.trans hl₃
  refine ⟨fun res hr => ?_, fun _ => htrap s₄ _ hfs₄' hml₄',
    fun a _ => hthrow s₄ _ a hfs₄' hml₄'⟩
  obtain ⟨r₂, rfl⟩ := (hshape res hr).1 rfl
  subst hr
  have hρ₂ : ρ r₂ = some (varTree "x") := by
    rcases hans _ (witWrite_eq rfl hd₂ rfl) _ _ _ rfl with h | ⟨t, ht, hρ⟩
    · cases h
    · rw [built_var] at ht
      rw [hρ]
      exact ht.symm
  refine X.localSet (us := []) (x := ⟨1⟩) (by simp [Frame.setLocal, hFl, appD, Idx.toNat])
    ?_
  let F₂ := F₁.setLocal ⟨1⟩ (.i32 r₂)
  have hF₂f : F₂.module.funcs = [0, 1, 2] := hFf
  have hF₂m : F₂.module.mems = [0] := hFm
  -- the handles at 0 and 4
  refine X.i32Const (us := []) ?_
  refine X.localGet (us := [] ++ [.i32 0]) (v := .i32 r₁) ?_ ?_
  · simp [Frame.local?, Frame.setLocal, hFl, appD, Idx.toNat]
  refine X.store32 (us := []) hF₂m hml₄' (htrap s₄ _ hfs₄' hml₄') fun mi₄ b₄ hmi₄ hst₄ => ?_
  obtain ⟨hm₅, hl₅, hf₅⟩ := setMem_mems (mi := { mi₄ with bytes := b₄ }) hml₄'
  refine X.i32Const (us := []) ?_
  refine X.localGet (us := [] ++ [.i32 4]) (v := .i32 r₂) ?_ ?_
  · simp [Frame.local?, Frame.setLocal, hFl, appD, Idx.toNat]
  refine X.store32 (us := []) hF₂m hl₅ (htrap _ _ (hf₅.trans hfs₄') hl₅)
    fun mi₅ b₅ hmi₅ hst₅ => ?_
  obtain rfl : mi₅ = { mi₄ with bytes := b₄ } := Option.some.inj (hmi₅.symm.trans hm₅)
  obtain ⟨-, hl₆, hf₆⟩ := setMem_mems (mi := { mi₄ with bytes := b₅ }) hl₅
  have hfs₆ : ((s₄.setMem 0 { mi₄ with bytes := b₄ }).setMem 0 { mi₄ with bytes := b₅ }).funcs
      = fs := hf₆.trans (hf₅.trans hfs₄')
  -- node(1, 0, 0, 2)
  have h₀ : bytesAt b₅ ⟨0, 4⟩ = (Memory.encodeLE 4 r₁.toNat).data.toList := by
    rw [Silmaril.Wasm.Logic.Core.bytesAt_store_disjoint hst₅ (.inr (by decide))]
    exact bytes_of_store32 hst₄
  have h₄ : bytesAt b₅ ⟨4, 4⟩ = (Memory.encodeLE 4 r₂.toNat).data.toList :=
    bytes_of_store32 hst₅
  have h8 : 8 ≤ b₅.size := by
    have := store_inBounds hst₅; simp [effAddr, IntType.width] at this ⊢; omega
  obtain ⟨cs, hcs, hle⟩ := children_pair (o := calloutIn impNode (some 0)
      ((s₄.setMem 0 { mi₄ with bytes := b₄ }).setMem 0 { mi₄ with bytes := b₅ })
      [.i32 1, .i32 0, .i32 0, .i32 2]) (memOf_setMem hl₅) h8 h₀ h₄
  have hd₃ : Callout.witNode appSig appTagOf (calloutIn impNode (some 0)
      ((s₄.setMem 0 { mi₄ with bytes := b₄ }).setMem 0 { mi₄ with bytes := b₅ })
      [.i32 1, .i32 0, .i32 0, .i32 2]) = some (⟨AppTag.app, ()⟩, [r₁, r₂]) :=
    witNode_eq rfl rfl (segment_nil (memOf_setMem hl₅) 0 (Nat.zero_le _)) rfl hcs hle rfl
  refine X.i32Const (us := []) ?_
  refine X.i32Const (us := [] ++ [.i32 1]) ?_
  refine X.i32Const (us := [] ++ [.i32 1] ++ [.i32 0]) ?_
  refine X.i32Const (us := [] ++ [.i32 1] ++ [.i32 0] ++ [.i32 0]) ?_
  refine hwp_call (us := []) (args := [.i32 1, .i32 0, .i32 0, .i32 2]) (x := ⟨0⟩) (k := 0)
    (fk := f₀) (i := impNode) (by show F₂.module.funcs[_]? = _; rw [hF₂f]; rfl) (hf0 _ hfs₆)
    hc₀ he₀ (by simp [hn₀]) rfl (pre_other (by decide)) ?_
  rintro s₇ r ⟨⟨hfs₇, hml₇⟩, hshape⟩ hans
  have hfs₇' : s₇.funcs = fs := hfs₇.trans hfs₆
  have hml₇' : s₇.mems.length = 1 := hml₇.trans hl₆
  refine ⟨fun res hr => ?_, fun _ => htrap s₇ _ hfs₇' hml₇',
    fun a _ => hthrow s₇ _ a hfs₇' hml₇'⟩
  obtain ⟨r₃, rfl⟩ := (hshape res hr).1 rfl
  subst hr
  have hρ₃ : ρ r₃ = some appTree := by
    rcases hans _ (witWrite_eq rfl hd₃ rfl) _ _ _ rfl with h | ⟨t, ht, hρ⟩
    · cases h
    · rw [built_app hρ₁ hρ₂] at ht
      rw [hρ]
      exact ht.symm
  -- accept(r₃)
  refine hwp_call (us := []) (args := [.i32 r₃]) (x := ⟨1⟩) (k := 1) (fk := f₁)
    (i := WitAst.impAcc) (by show F₂.module.funcs[_]? = _; rw [hF₂f]; rfl) (hf1 _ hfs₇') hc₁ he₁
    (by simp [hn₁]) rfl ?_ ?_
  · intro h hd t ht
    simp [appRoles, witRoles, witAccept, calloutIn, Callout.args1, Callout.i32?, Val.i32] at hd
    subst hd
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

/-- **`appMod` meets the writer contract** in every fixed environment, for every profile. -/
theorem app_sat (P : Profile) (ρ : Env (BitVec 32) (AST appSig.toAstSig)) :
    MemSat P appMod 0 appRoles (appK ρ) appInv := by
  intro mt Is c₀ hI
  obtain ⟨c, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, hexp, hml, f₀, f₁, f₂, hf, h0, h1, h2⟩ := app_facts hp
  have hmem : (c.withStart none).frame.module.mems[0]? = some 0 := by
    simp [Config.withStart, hmems]
  rw [hmem]
  refine ⟨fun n => Safe.of_exits (o := .normal []) (by simp [Config.withStart, hcode]; rfl)
    (fun _ _ => ⟨c, none, hp, rfl, hml⟩), ?_⟩
  intro a ha
  rw [← haddr, hexp] at ha
  obtain rfl : a = 2 := by simpa using ha
  obtain ⟨code, ps, rs, hcode2, hloc, hbody, he, hps, hrs, hfuncs, hmems2, hD⟩ := fnOk_spec h2
  have hinv : ∀ s', s'.funcs = c.store.funcs → s'.mems.length = 1 → appInv s' :=
    fun s' h h' => ⟨c, none, hp, h, h'⟩
  have hfi : ∀ s, appInv s → s.funcs = c.store.funcs := by
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
  exact app_body h0 h1 (by simp [Frame.forCall, hfuncs]) (by simp [Frame.forCall, hmems2])
    (by simp [Frame.forCall, hD]) (fs := c.store.funcs) (by rw [hf]; rfl) (hfi s hs)
    hml' hinv hQ

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitApp
