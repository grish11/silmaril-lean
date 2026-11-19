module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitPayload
public import Silmaril.Wasm.Verify.Kernel.Defs

/-!
# Proofs: record, option and char payloads through memory, `glyphMod`

* `readVals_glyphA`, `readVals_glyphB`: the `i64`s `glyphA`, `glyphB` stored little-endian are
  the payload vectors `({ ch: 'a', size: some(7) })` and `({ ch: 'λ', size: none })` of
  `glyphSig`'s `glyph` tag (one `record { ch: char, size: option<u8> }`: the `char` at `0`, the
  `option` discriminant at `4`, its payload at `5`);
* `glyph_sat`: in a fixed environment `ρ` (no sentinel), `glyphMod` meets the writer contract
  `roleWriterContract (witRoles glyphSig glyphTagOf {}) (astW glyphSig.toAstSig) none ρ
  {glyphPairTree} hiReply`: the first `node(0, 16, 0, 0)` reads the record `glyphA` stored at
  `[16, 24)` right before it (handle `r₁` denotes `glyph { 'a', some(7) }`), the second reads
  `glyphB` (handle `r₂`, `glyph { 'λ', none }`); the module stores `r₁`, `r₂` at `[0, 8)` and
  `node(1, 0, 0, 2)` reads no payload and the two child handles, so its handle denotes
  `pair(glyph { 'a', some(7) }, glyph { 'λ', none })`, which `accept` names.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitGlyph

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

/-! ## Decoding the record payloads -/

/-- The stored `glyphA` is the record `{ ch: 'a', size: some(7) }`. -/
theorem readVals_glyphA (seg : Nat → Nat → Option (List UInt8)) :
    readVals seg [glyphTy] (Memory.encodeLE (IntType.i64.width / 8)
      (BitVec.setWidth (8 * (IntType.i64.width / 8)) glyphA).toNat).data.toList =
      some (((('a', (some 7 : Option UInt8), ()) : Char × Option UInt8 × Unit), ())) := by
  kernel_rfl

/-- The stored `glyphB` is the record `{ ch: 'λ', size: none }`. -/
theorem readVals_glyphB (seg : Nat → Nat → Option (List UInt8)) :
    readVals seg [glyphTy] (Memory.encodeLE (IntType.i64.width / 8)
      (BitVec.setWidth (8 * (IntType.i64.width / 8)) glyphB).toNat).data.toList =
      some (((('λ', (none : Option UInt8), ()) : Char × Option UInt8 × Unit), ())) := by
  kernel_rfl

/-! ## The instantiated module -/

/-- The default values of the locals. -/
def glyphD : List (Option Val) := [some (.i32 0), some (.i32 0)]

/-- The shape of the instantiated module. -/
def glyphOk : Bool :=
  match prep glyphMod with
  | some (c, st) => st.isNone && c.code.isEmpty && c.frame.module.mems == [0] &&
      exportFuncAddrs c.frame.module == [2] && c.store.mems.length == 1 &&
      (match c.store.funcs with
       | [f₀, f₁, f₂] => stubOk 0 4 f₀ && stubOk 1 1 f₁ &&
          fnOk [.i32, .i32] glyphBody 0 0 [0, 1, 2] [0] glyphD f₂
       | _ => false)
  | none => false

theorem glyphOk_true : glyphOk = true := by decide +kernel

theorem glyph_facts {c : Config Nat} {st : Option FuncIdx} (hp : prep glyphMod = some (c, st)) :
    st = none ∧ c.code = [] ∧ c.frame.module.mems = [0] ∧ exportFuncAddrs c.frame.module = [2] ∧
    c.store.mems.length = 1 ∧ ∃ f₀ f₁ f₂, c.store.funcs = [f₀, f₁, f₂] ∧
      stubOk 0 4 f₀ = true ∧ stubOk 1 1 f₁ = true ∧
      fnOk [.i32, .i32] glyphBody 0 0 [0, 1, 2] [0] glyphD f₂ = true := by
  have h := glyphOk_true
  unfold glyphOk at h
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
def glyphInv (s : Store Nat) : Prop :=
  ∃ c st, prep glyphMod = some (c, st) ∧ s.funcs = c.store.funcs ∧ s.mems.length = 1

/-- The roles of the example. -/
abbrev glyphRoles : Roles Unit (WitWEv glyphSig) Unit Unit := witRoles glyphSig glyphTagOf {}

/-- The writer contract in the fixed environment `ρ`. -/
abbrev glyphK (ρ : Env (BitVec 32) (AST glyphSig.toAstSig)) : MemContract (WitWEv glyphSig) :=
  roleWriterContract glyphRoles (astW glyphSig.toAstSig) none ρ {glyphPairTree} hiReply


/-- Calls of other imports than `accept` are always allowed. -/
theorem pre_other {ρ : Env (BitVec 32) (AST glyphSig.toAstSig)} {i : Import} {s : Store Nat}
    {args : List Val} (hi : (i.moduleName, i.name) ≠ ("wit", "accept")) :
    (glyphK ρ).pre (calloutIn i (some 0) s args) := by
  intro h hd
  change witAccept glyphSig {} _ = _ at hd
  rw [witAccept_eq_none hi] at hd
  cases hd

/-- `glyph { ch: c, size: k }` from its payload. -/
theorem built_glyph (ρ : Env (BitVec 32) (AST glyphSig.toAstSig)) (c : Char) (k : Option UInt8) :
    (astW glyphSig.toAstSig).built ρ ⟨GlyphTag.glyph, ((c, k, ()), ())⟩ [] =
      some (glyphTree c k) := rfl

/-- `pair(x, y)` from the handles of `x` and `y`. -/
theorem built_pair {ρ : Env (BitVec 32) (AST glyphSig.toAstSig)} {r₁ r₂ : BitVec 32}
    {x y : AST glyphSig.toAstSig} (h₁ : ρ r₁ = some x) (h₂ : ρ r₂ = some y) :
    (astW glyphSig.toAstSig).built ρ ⟨GlyphTag.pair, ()⟩ [r₁, r₂] =
      some (AST.node (S := glyphSig.toAstSig) GlyphTag.pair () [x, y]) := by
  unfold Writer.built Env.lookupAll
  rw [List.mapM_cons, List.mapM_cons, List.mapM_nil, h₁, h₂]
  rfl

/-! ## Every-run proof -/

/-- **The body of `run`**, in the fixed environment `ρ`. -/
theorem glyph_body {P : Profile} {ρ : Env (BitVec 32) (AST glyphSig.toAstSig)}
    {f₀ f₁ : FuncInst Nat} (h0 : stubOk 0 4 f₀ = true) (h1 : stubOk 1 1 f₁ = true)
    {F : Frame} (hFf : F.module.funcs = [0, 1, 2]) (hFm : F.module.mems = [0])
    (hFl : F.locals = glyphD) {s : Store Nat} {fs : List (FuncInst Nat)}
    (hfs : fs = [f₀, f₁] ++ fs.drop 2) (hsf : s.funcs = fs) (hml : s.mems.length = 1)
    (hinv : ∀ s', s'.funcs = fs → s'.mems.length = 1 → glyphInv s') {Q : Post Nat}
    (hQ : BodyExits glyphInv Q) :
    HWP P (memHost glyphMod (some 0) glyphRoles (glyphK ρ)) s F
      (vals [] ++ expression glyphBody) Q := by
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
  unfold glyphBody
  -- the record `glyphA` at 16
  refine X.i32Const (us := []) ?_
  refine X.i64Const (us := [] ++ [.i32 16]) ?_
  refine X.store64 (us := []) hFm hml (htrap s F hsf hml) fun mi₀ b₀ hmi₀ hst₀ => ?_
  obtain ⟨-, hl₁, hf₁⟩ := setMem_mems (mi := { mi₀ with bytes := b₀ }) hml
  -- node(0, 16, 0, 0)
  refine X.i32Const (us := []) ?_
  refine X.i32Const (us := [] ++ [.i32 0]) ?_
  refine X.i32Const (us := [] ++ [.i32 0] ++ [.i32 16]) ?_
  refine X.i32Const (us := [] ++ [.i32 0] ++ [.i32 16] ++ [.i32 0]) ?_
  have hd₁ : Callout.witNode glyphSig glyphTagOf (calloutIn impNode (some 0)
      (s.setMem 0 { mi₀ with bytes := b₀ }) [.i32 0, .i32 16, .i32 0, .i32 0]) =
      some (⟨GlyphTag.glyph, ((('a', (some 7 : Option UInt8), ()) : Char × Option UInt8 × Unit), ())⟩, []) :=
    witNode_eq rfl rfl (segment_of_store hst₀ _ (memOf_setMem hml)) (readVals_glyphA _)
      (segment_nil (memOf_setMem hml) 0 (Nat.zero_le _)) rfl rfl
  refine hwp_call (us := []) (args := [.i32 0, .i32 16, .i32 0, .i32 0]) (x := ⟨0⟩) (k := 0)
    (fk := f₀) (i := impNode) (by rw [hFf]; rfl) (hf0 _ (hf₁.trans hsf)) hc₀ he₀ (by simp [hn₀])
    rfl (pre_other (by decide)) ?_
  rintro s₂ r ⟨⟨hfs₂, hml₂⟩, hshape⟩ hans
  have hfs₂' : s₂.funcs = fs := hfs₂.trans (hf₁.trans hsf)
  have hml₂' : s₂.mems.length = 1 := hml₂.trans hl₁
  refine ⟨fun res hr => ?_, fun _ => htrap s₂ F hfs₂' hml₂',
    fun a _ => hthrow s₂ F a hfs₂' hml₂'⟩
  obtain ⟨r₁, rfl⟩ := (hshape res hr).1 rfl
  subst hr
  have hρ₁ : ρ r₁ = some (glyphTree 'a' (some 7)) := by
    rcases hans _ (witWrite_eq rfl hd₁ rfl) _ _ _ rfl with h | ⟨t, ht, hρ⟩
    · cases h
    · change some (glyphTree 'a' (some 7)) = some _ at ht
      rw [hρ]
      exact ht.symm
  refine X.localSet (us := []) (x := ⟨0⟩) (by simp [hFl, glyphD, Idx.toNat]) ?_
  let F₁ := F.setLocal ⟨0⟩ (.i32 r₁)
  have hF₁f : F₁.module.funcs = [0, 1, 2] := hFf
  have hF₁m : F₁.module.mems = [0] := hFm
  -- the record `glyphB` at 16
  refine X.i32Const (us := []) ?_
  refine X.i64Const (us := [] ++ [.i32 16]) ?_
  refine X.store64 (us := []) hF₁m hml₂' (htrap s₂ _ hfs₂' hml₂') fun mi₂ b₂ hmi₂ hst₂ => ?_
  obtain ⟨-, hl₃, hf₃⟩ := setMem_mems (mi := { mi₂ with bytes := b₂ }) hml₂'
  -- node(0, 16, 0, 0)
  refine X.i32Const (us := []) ?_
  refine X.i32Const (us := [] ++ [.i32 0]) ?_
  refine X.i32Const (us := [] ++ [.i32 0] ++ [.i32 16]) ?_
  refine X.i32Const (us := [] ++ [.i32 0] ++ [.i32 16] ++ [.i32 0]) ?_
  have hd₂ : Callout.witNode glyphSig glyphTagOf (calloutIn impNode (some 0)
      (s₂.setMem 0 { mi₂ with bytes := b₂ }) [.i32 0, .i32 16, .i32 0, .i32 0]) =
      some (⟨GlyphTag.glyph, ((('λ', (none : Option UInt8), ()) : Char × Option UInt8 × Unit), ())⟩, []) :=
    witNode_eq rfl rfl (segment_of_store hst₂ _ (memOf_setMem hml₂')) (readVals_glyphB _)
      (segment_nil (memOf_setMem hml₂') 0 (Nat.zero_le _)) rfl rfl
  refine hwp_call (us := []) (args := [.i32 0, .i32 16, .i32 0, .i32 0]) (x := ⟨0⟩) (k := 0)
    (fk := f₀) (i := impNode) (by rw [hF₁f]; rfl) (hf0 _ (hf₃.trans hfs₂')) hc₀ he₀
    (by simp [hn₀]) rfl (pre_other (by decide)) ?_
  rintro s₄ r ⟨⟨hfs₄, hml₄⟩, hshape⟩ hans
  have hfs₄' : s₄.funcs = fs := hfs₄.trans (hf₃.trans hfs₂')
  have hml₄' : s₄.mems.length = 1 := hml₄.trans hl₃
  refine ⟨fun res hr => ?_, fun _ => htrap s₄ _ hfs₄' hml₄',
    fun a _ => hthrow s₄ _ a hfs₄' hml₄'⟩
  obtain ⟨r₂, rfl⟩ := (hshape res hr).1 rfl
  subst hr
  have hρ₂ : ρ r₂ = some (glyphTree 'λ' none) := by
    rcases hans _ (witWrite_eq rfl hd₂ rfl) _ _ _ rfl with h | ⟨t, ht, hρ⟩
    · cases h
    · change some (glyphTree 'λ' none) = some _ at ht
      rw [hρ]
      exact ht.symm
  refine X.localSet (us := []) (x := ⟨1⟩) (by simp [Frame.setLocal, hFl, glyphD, Idx.toNat])
    ?_
  let F₂ := F₁.setLocal ⟨1⟩ (.i32 r₂)
  have hF₂f : F₂.module.funcs = [0, 1, 2] := hFf
  have hF₂m : F₂.module.mems = [0] := hFm
  -- the handles at 0 and 4
  refine X.i32Const (us := []) ?_
  refine X.localGet (us := [] ++ [.i32 0]) (v := .i32 r₁) ?_ ?_
  · simp [Frame.local?, Frame.setLocal, hFl, glyphD, Idx.toNat]
  refine X.store32 (us := []) hF₂m hml₄' (htrap s₄ _ hfs₄' hml₄') fun mi₄ b₄ hmi₄ hst₄ => ?_
  obtain ⟨hm₅, hl₅, hf₅⟩ := setMem_mems (mi := { mi₄ with bytes := b₄ }) hml₄'
  refine X.i32Const (us := []) ?_
  refine X.localGet (us := [] ++ [.i32 4]) (v := .i32 r₂) ?_ ?_
  · simp [Frame.local?, Frame.setLocal, hFl, glyphD, Idx.toNat]
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
  have hd₃ : Callout.witNode glyphSig glyphTagOf (calloutIn impNode (some 0)
      ((s₄.setMem 0 { mi₄ with bytes := b₄ }).setMem 0 { mi₄ with bytes := b₅ })
      [.i32 1, .i32 0, .i32 0, .i32 2]) = some (⟨GlyphTag.pair, ()⟩, [r₁, r₂]) :=
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
  have hρ₃ : ρ r₃ = some glyphPairTree := by
    rcases hans _ (witWrite_eq rfl hd₃ rfl) _ _ _ rfl with h | ⟨t, ht, hρ⟩
    · cases h
    · rw [built_pair hρ₁ hρ₂] at ht
      rw [hρ]
      exact ht.symm
  -- accept(r₃)
  refine hwp_call (us := []) (args := [.i32 r₃]) (x := ⟨1⟩) (k := 1) (fk := f₁)
    (i := WitAst.impAcc) (by show F₂.module.funcs[_]? = _; rw [hF₂f]; rfl) (hf1 _ hfs₇') hc₁ he₁
    (by simp [hn₁]) rfl ?_ ?_
  · intro h hd t ht
    simp [glyphRoles, witRoles, witAccept, calloutIn, Callout.args1, Callout.i32?, Val.i32] at hd
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

/-- **`glyphMod` meets the writer contract** in every fixed environment, for every profile. -/
theorem glyph_sat (P : Profile) (ρ : Env (BitVec 32) (AST glyphSig.toAstSig)) :
    MemSat P glyphMod 0 glyphRoles (glyphK ρ) glyphInv := by
  intro mt Is c₀ hI
  obtain ⟨c, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, hexp, hml, f₀, f₁, f₂, hf, h0, h1, h2⟩ := glyph_facts hp
  have hmem : (c.withStart none).frame.module.mems[0]? = some 0 := by
    simp [Config.withStart, hmems]
  rw [hmem]
  refine ⟨fun n => Safe.of_exits (o := .normal []) (by simp [Config.withStart, hcode]; rfl)
    (fun _ _ => ⟨c, none, hp, rfl, hml⟩), ?_⟩
  intro a ha
  rw [← haddr, hexp] at ha
  obtain rfl : a = 2 := by simpa using ha
  obtain ⟨code, ps, rs, hcode2, hloc, hbody, he, hps, hrs, hfuncs, hmems2, hD⟩ := fnOk_spec h2
  have hinv : ∀ s', s'.funcs = c.store.funcs → s'.mems.length = 1 → glyphInv s' :=
    fun s' h h' => ⟨c, none, hp, h, h'⟩
  have hfi : ∀ s, glyphInv s → s.funcs = c.store.funcs := by
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
  exact glyph_body h0 h1 (by simp [Frame.forCall, hfuncs]) (by simp [Frame.forCall, hmems2])
    (by simp [Frame.forCall, hD]) (fs := c.store.funcs) (by rw [hf]; rfl) (hfi s hs)
    hml' hinv hQ

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitGlyph
