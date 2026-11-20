module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.KwText.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Text

/-!
# Proofs: the keyword text reader and `kwTextMod`

The proofs of `Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Text` with the keyword decoder
(`keyword_text`, atoms `KwAtom`): `kwText_sat` (the reader contract in every fixed environment:
`accept(h)` is reached only when the length word is `2`, so `h` denotes a keyword of two UTF-8
bytes), `kwTextReaderLang_subset` (the reader bridge for the keyword text roles) and
`kwTextMod_sound`. `bytesList_spec` is reused.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.KwText

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept Silmaril.Accept.IO Silmaril.Accept.Handle
  Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.Items
  Silmaril.Wasm.Game.HandleAccept.MemSound.Text Silmaril.Wasm.Game.HandleAccept.MemSound.KwText
  Silmaril.Wasm.Game.HandleAccept.MemSound.Atoms
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Text
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Items Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post bytesAt Region leNat)

/-! ## Instance facts -/

/-- The shape of the instantiated module. -/
def kwTextOk : Bool :=
  match prep kwTextMod with
  | some (c, st) => st.isNone && c.code.isEmpty && c.frame.module.mems == [0] &&
      exportFuncAddrs c.frame.module == [2] && c.store.mems.length == 1 &&
      (match c.store.funcs with
       | [f₀, f₁, f₂] => stubOk 0 2 f₀ && stubOk 1 1 f₁ &&
          fnOk [] itemsBody 1 0 [0, 1, 2] [0] itemsD f₂
       | _ => false)
  | none => false

theorem kwTextOk_true : kwTextOk = true := by decide +kernel

theorem kwText_facts {c : Config Nat} {st : Option FuncIdx} (hp : prep kwTextMod = some (c, st)) :
    st = none ∧ c.code = [] ∧ c.frame.module.mems = [0] ∧
      exportFuncAddrs c.frame.module = [2] ∧
    c.store.mems.length = 1 ∧ ∃ f₀ f₁ f₂, c.store.funcs = [f₀, f₁, f₂] ∧
      stubOk 0 2 f₀ = true ∧ stubOk 1 1 f₁ = true ∧
      fnOk [] itemsBody 1 0 [0, 1, 2] [0] itemsD f₂ = true := by
  have h := kwTextOk_true
  unfold kwTextOk at h
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
def kwTextInv (s : Store Nat) : Prop :=
  ∃ c st, prep kwTextMod = some (c, st) ∧ s.funcs = c.store.funcs ∧ s.mems.length = 1

/-- The reader contract in the fixed environment `ρ`. -/
abbrev kwTextK (ρ : Env (BitVec 32) SymStrKwBytesSExp) : MemContract KwREv :=
  kwTextContract {} ρ twoByteKws itemsReply

/-! ## The body -/

theorem kwTextAccept_inv {o : Callout} {v : Val} {h : BitVec 32} (ha : o.args = [v])
    (hd : kwTextAccept {} o = some (.accept h)) : v = .i32 h := by
  unfold kwTextAccept at hd
  split at hd
  · simp only [ha, Callout.args1, Option.map_eq_some_iff, REv.accept.injEq] at hd
    obtain ⟨a, hi, rfl⟩ := hd
    exact i32?_some hi
  · cases hd

/-- What the reader contract says after `keyword_text(h, 0)` returned in the store `s'`. -/
theorem kwText_ans {ρ : Env (BitVec 32) SymStrKwBytesSExp} {s s' : Store Nat} {h : BitVec 32}
    {mi : MemInst} (hmi : s'.mems[0]? = some mi)
    (hans : ∀ y, kwTextRead {} (calloutIn ⟨"sexp", "keyword_text", .func ⟨0⟩⟩ (some 0) s
      [.i32 h, .i32 0]) ⟨.values [], memOf (some 0) s'⟩ = some y → (kwTextK ρ).ans y) :
    ∃ bs, bytesList mi.bytes 0 = some bs ∧ ∃ str, utf8? bs = some str ∧
      ρ h = some (.atom ⟨.keyword, by decide, str⟩) := by
  have hm : memOf (some 0) s' = some mi.bytes := by simp [memOf, hmi]
  have hd : kwTextRead {} (calloutIn ⟨"sexp", "keyword_text", .func ⟨0⟩⟩ (some 0) s
      [.i32 h, .i32 0]) ⟨.values [], memOf (some 0) s'⟩ =
      some (.read (.atom h) (kwTextAns ⟨.values [], memOf (some 0) s'⟩ 0)) := by
    simp [kwTextRead, calloutIn, Val.i32]
  obtain ⟨-, hok⟩ := hans _ hd _ _ rfl
  unfold kwTextAns at hok
  rw [hm] at hok
  simp only [Option.bind_some] at hok
  split at hok
  · rename_i str hstr
    rcases hbl : bytesList mi.bytes (0 : BitVec 32).toNat with _ | bs
    · rw [hbl] at hstr; cases hstr
    · rw [hbl] at hstr
      exact ⟨bs, by simpa using hbl, str, hstr, hok⟩
  · exact hok.elim

/-- **The body of `check`**, in the fixed environment `ρ`. -/
theorem kwText_body {P : Profile} {ρ : Env (BitVec 32) SymStrKwBytesSExp}
    {f₀ f₁ : FuncInst Nat}
    (h0 : stubOk 0 2 f₀ = true) (h1 : stubOk 1 1 f₁ = true) {v : Val} {F : Frame}
    (hFf : F.module.funcs = [0, 1, 2]) (hFm : F.module.mems = [0]) (hFl : F.locals = [some v])
    {s : Store Nat} {fs : List (FuncInst Nat)}
    (hfs : fs = [f₀, f₁] ++ fs.drop 2) (hsf : s.funcs = fs) (hml : s.mems.length = 1)
    (hinv : ∀ s', s'.funcs = fs → s'.mems.length = 1 → kwTextInv s') {Q : Post Nat}
    (hQ : BodyExits kwTextInv Q) :
    HWP P (memHost kwTextMod (some 0) (kwTextRoles {}) (kwTextK ρ)) s F
      (vals [] ++ expression itemsBody) Q := by
  obtain ⟨ps₀, rs₀, hc₀, he₀, hn₀⟩ := stubOk_spec h0
  obtain ⟨ps₁, rs₁, hc₁, he₁, hn₁⟩ := stubOk_spec h1
  have htrap : ∀ s' (F' : Frame), s'.funcs = fs → s'.mems.length = 1 → Q s' F' .trap :=
    fun s' F' h h' => (hQ s' (hinv s' h h') F').2.2.1
  have hthrow : ∀ s' (F' : Frame) a, s'.funcs = fs → s'.mems.length = 1 →
      Q s' F' (.throw a) :=
    fun s' F' a h h' => (hQ s' (hinv s' h h') F').2.2.2 a
  have hv : F.local? ⟨0⟩ = some (some v) := by simp [Frame.local?, hFl, Idx.toNat]
  unfold itemsBody
  -- items(h, 0)
  refine X.localGet (us := []) hv ?_
  refine X.i32Const (us := [] ++ [v]) ?_
  refine hwp_call (us := []) (args := [v, .i32 0]) (x := ⟨0⟩) (k := 0) (fk := f₀)
    (i := ⟨"sexp", "keyword_text", .func ⟨0⟩⟩) (by rw [hFf]; rfl) (by rw [hsf, hfs]; rfl)
    hc₀ he₀
    (by simp [hn₀]) rfl ?_ ?_
  · intro h hd
    simp [kwTextAccept, calloutIn] at hd
  rintro s₁ r ⟨⟨hfs₁, hml₁⟩, hshape⟩ hans
  have hfs₁' : s₁.funcs = fs := hfs₁.trans hsf
  have hml₁' : s₁.mems.length = 1 := hml₁.trans hml
  refine ⟨fun res hr => ?_, fun _ => htrap s₁ F hfs₁' hml₁',
    fun a _ => hthrow s₁ F a hfs₁' hml₁'⟩
  obtain rfl := hshape res hr
  subst hr
  obtain ⟨mi₁, hmi₁⟩ : ∃ mi, s₁.mems[0]? = some mi :=
    ⟨s₁.mems[0]'(by omega), List.getElem?_eq_getElem _⟩
  have hfact : ∀ h, v = .i32 h → ∃ bs, bytesList mi₁.bytes 0 = some bs ∧
      ∃ str, utf8? bs = some str ∧ ρ h = some (.atom ⟨.keyword, by decide, str⟩) := by
    rintro h rfl
    exact kwText_ans (s := s) hmi₁ hans
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
    (i := ⟨"sexp", "accept", .func ⟨1⟩⟩) (by rw [hFf]; rfl) (by rw [hfs₁', hfs]; rfl)
    hc₁ he₁
    (by simp [hn₁]) rfl ?_ ?_
  · intro h hd t ht
    have hvh : v = .i32 h := kwTextAccept_inv rfl hd
    obtain ⟨bs, hbs, str, hstr, hρ⟩ := hfact h hvh
    obtain ⟨-, hlen'⟩ := bytesList_spec hbs
    have hld' := Silmaril.Wasm.Logic.Core.load_eq (B := mi.bytes) (a := 4) (n := 4)
      (by have := (bytesList_spec hbs).1; omega)
    have hcn : c.toNat = leNat (bytesAt mi.bytes ⟨4, 4⟩) % 2 ^ (8 * 4) :=
      (congrArg BitVec.toNat (Option.some.inj (hld.symm.trans hld'))).trans
        (BitVec.toNat_ofNat _ _)
    rw [hρ] at ht
    cases ht
    refine ⟨bs, str, ?_, hstr, rfl⟩
    rw [hlen']
    have h22 : c.toNat % 2 ^ 32 = 2 := by
      have := congrArg BitVec.toNat hc2
      rw [BitVec.toNat_setWidth] at this
      simpa using this
    rw [BitVec.toNat_ofNat]
    simp only [Nat.reduceMul, Nat.reducePow] at h22 hcn ⊢
    omega
  rintro s₂ r ⟨⟨hfs₂, hml₂⟩, hshape⟩ -
  have hfs₂' : s₂.funcs = fs := hfs₂.trans hfs₁'
  have hml₂' : s₂.mems.length = 1 := hml₂.trans hml₁'
  refine ⟨fun res hr => ?_, fun _ => htrap s₂ F hfs₂' hml₂',
    fun a _ => hthrow s₂ F a hfs₂' hml₂'⟩
  obtain rfl := hshape res hr
  exact X.done (hQ s₂ (hinv s₂ hfs₂' hml₂') F).1

/-- **`kwTextMod` meets the reader contract** in every fixed environment, for every profile. -/
theorem kwText_sat (P : Profile) (ρ : Env (BitVec 32) SymStrKwBytesSExp) :
    MemSat P kwTextMod 0 (kwTextRoles {}) (kwTextK ρ) kwTextInv := by
  intro mt Is c₀ hI
  obtain ⟨c, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, hexp, hml, f₀, f₁, f₂, hf, h0, h1, h2⟩ := kwText_facts hp
  have hmem : (c.withStart none).frame.module.mems[0]? = some 0 := by
    simp [Config.withStart, hmems]
  rw [hmem]
  refine ⟨fun n => Safe.of_exits (o := .normal []) (by simp [Config.withStart, hcode]; rfl)
    (fun _ _ => ⟨c, none, hp, rfl, hml⟩), ?_⟩
  intro a ha
  rw [← haddr, hexp] at ha
  obtain rfl : a = 2 := by simpa using ha
  obtain ⟨code, ps, rs, hcode2, hloc, hbody, he, hps, hrs, hfuncs, hmems2, hD⟩ := fnOk_spec h2
  have hinv : ∀ s', s'.funcs = c.store.funcs → s'.mems.length = 1 → kwTextInv s' :=
    fun s' h h' => ⟨c, none, hp, h, h'⟩
  have hfi : ∀ s, kwTextInv s → s.funcs = c.store.funcs := by
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
  exact kwText_body (v := v) h0 h1 (by simp [Frame.forCall, hfuncs])
    (by simp [Frame.forCall, hmems2])
    (by simp [Frame.forCall]) (fs := c.store.funcs) (by rw [hf]; rfl) (hfi s hs) hml' hinv hQ

/-! ## The reader bridge -/

theorem kwTextRead_ne_accept {ix : KwTextImports} {o : Callout} {w : HostReply} {h : BitVec 32} :
    kwTextRead ix o w ≠ some (.accept h) := by
  unfold kwTextRead
  split
  · split <;> simp
  · simp

/-- **The text reader bridge**: under the trapping read policy and no accept UB, the reader
language over every set of fixed environments is included in `L`. -/
theorem kwTextReaderLang_subset {P : Numerics.Profile} {Envs : Store Nat → SEnv UImp → Prop}
    {memIdx : Nat} {m : Module} {ix : KwTextImports} {L : Set SymStrKwBytesSExp}
    {reply : UCall Nat → UReply → Prop} {Inv : Store Nat → Prop}
    (hsat : ∀ ρ, MemSat P m memIdx (kwTextRoles ix) (kwTextContract ix ρ L reply) Inv)
    (hE : ∀ s L, Envs s L → ReplyEnvs reply s L) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (Env (BitVec 32) SymStrKwBytesSExp)) :
    kwTextReaderLang P Envs memIdx m ix .trap oa Rhos ⊆ L := by
  refine readerLang_trap_subset hoa (cert := fun hist h =>
      ∀ ρ : Env (BitVec 32) SymStrKwBytesSExp,
      (∀ p ∈ hist, (sexpR KwAtom (BitVec 32)).valid ρ p.1 ∧
        (sexpR KwAtom (BitVec 32)).ok ρ p.1 p.2) → ∀ t, ρ h = some t → t ∈ L)
    (fun ρ hist h hh hc => hc ρ hh) ?_ Rhos
  rintro _ ⟨ts, hts, rfl⟩ u v h hu ρ hreads
  obtain ⟨u', v', hd, rfl⟩ := inputsOf_split (e := REv.enter) (by simp) hu
  have hall : ∀ y, Tag.inp y ∈ u' → (kwTextContract ix ρ L reply).ans y := by
    rintro y hy q a rfl
    exact hreads (q, a) (mem_reads (mem_inputsOf_of_inp hy))
  obtain ⟨o, hpre, hc | ⟨w, hd'⟩⟩ := tagTraces_pre (hsat ρ) hE hts hd hall
  · exact hpre h hc
  · exact absurd hd' kwTextRead_ne_accept

/-- **`kwTextMod` accepts only keywords of two UTF-8 bytes**, over every set of fixed
environments. -/
theorem kwTextMod_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (Env (BitVec 32) SymStrKwBytesSExp)) :
    kwTextReaderLang P (ReplyEnvs itemsReply) 0 kwTextMod {} .trap oa Rhos ⊆ twoByteKws :=
  kwTextReaderLang_subset (fun ρ => kwText_sat P ρ) (fun _ _ h => h) hoa Rhos

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.KwText
