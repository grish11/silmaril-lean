module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.PullMix.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Pull
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Langs
public import Silmaril.Semantics.Accept.Mixed.Thms

/-!
# Proofs: memory mixed sessions and `blobEcho`

* `mixCall_p`, `mixAnswer_p`, `mixAnswer_w`: the parsing events of the mixed roles are the pull
  decoders' (`finish` at calls, `feed` at answers), the writer events at answers are
  `memWrite`'s.
* `beK sent σ`: the contract of `blobEcho` for the writer store `σ`: decoded writes agree with
  `σ` (`Silmaril.Accept.Mixed.WriteAgrees`, the answer assumption) and every `finish(n, h)`
  call has `n ≤ 16` and `h` the sentinel or a handle denoting in `σ` a byte atom of `n` bytes
  (the guarantee).
* `be_sat`: `blobEcho` meets `beK sent σ` for every `σ` (Hoare logic: `n` is what `read(0, 16)`
  returned, at most `16`; the callout of `blob(0, n)` observes the `n` bytes at `0` of a memory
  of at least `16` bytes, so the write it decodes to is the byte atom of `n` bytes, and the
  answer assumption makes its handle denote that atom in `σ`).
* `len_of_sat`: assume/guarantee in the store semantics
  (`Silmaril.Accept.Mixed.mixedRel_subset_of_AG`, the witness `σ` being the final store of the
  run) with the bridge `tagTraces_pre`: every pair of the mixed relation is in `lenRel`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.PullMix

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept Silmaril.Accept.Handle Silmaril.Accept.IO
  Silmaril.Accept.Parse Silmaril.Accept.Mixed Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.Pull
  Silmaril.Wasm.Game.HandleAccept.MemSound.PullMix
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Pull
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post bytesAt Region)

/-! ## Decoders -/

theorem mixCall_p {o : Callout} {e : PullEv} (h : mixCall {} {} o = some (.p e)) :
    pullFinish {} o = some e := by
  unfold mixCall at h
  split at h
  · cases h
  · obtain ⟨e', he', heq⟩ := Option.map_eq_some_iff.1 h
    cases heq
    exact he'

theorem mixAnswer_p {o : Callout} {w : HostReply} {e : PullEv}
    (h : mixAnswer {} {} o w = some (.p e)) : pullRead {} o w = some e := by
  unfold mixAnswer at h
  split at h
  · cases h
  · obtain ⟨e', he', heq⟩ := Option.map_eq_some_iff.1 h
    cases heq
    exact he'

theorem mixAnswer_w {o : Callout} {w : HostReply} {e : MemWEv} (h : memWrite {} o w = some e) :
    mixAnswer {} {} o w = some (.w e) := by
  unfold mixAnswer
  rw [h]

/-! ## The contract -/

/-- **The contract of `blobEcho`** for the writer store `σ` and the writer sentinel `sent`. -/
abbrev beK (sent : Option (BitVec 32)) (σ : Env (BitVec 32) SymStrBytesSExp) :
    MemContract MixEv where
  pre o := ∀ n h, pullFinish {} o = some (.finish n h) →
    n ≤ 16 ∧ (sent = some h ∨ ∃ c : List UInt8, c.length = n ∧ σ h = some (bytesAtom c))
  ans x := ∀ op args r, x = .w (.write op args r) → WriteAgrees (sexpW MemAtom) sent σ op args r
  reply := blobReply

/-- **The length relation from the contract**, for every module meeting it in every store. -/
theorem len_of_sat {P : Profile} {Envs : Store Nat → SEnv UImp → Prop} {m : Module}
    {Inv : Store Nat → Prop} {pol : Policy (BitVec 32)} {ppol : PPolicy (BitVec 32)}
    (hsat : ∀ σ, MemSat P m 0 (mixRoles {} {}) (beK pol.sentinel σ) Inv)
    (hE : ∀ s L, Envs s L → ReplyEnvs blobReply s L) (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub)
    (hs : pol.sentinel = none ∨ pol.sentinel = some ppol.sentinel) :
    memMixedRel P Envs 0 m {} {} pol ppol ⊆ lenRel := by
  refine mixedRel_subset_of_AG hw ha hb ho ?_
  rintro _ ⟨ts, hts, rfl⟩ σ hWA e he ps w h ps' hR hne x hx
  obtain ⟨u0, v0, hu0⟩ := List.append_of_mem he
  obtain ⟨u, v, hd, -⟩ := inputsOf_split (e := (MEv.w WEv.enter : MixEv))
    (fun h => by cases h) hu0
  have hans : ∀ y, Tag.inp y ∈ u → (beK pol.sentinel σ).ans y := by
    rintro y hy op args r rfl
    refine hWA op args r ?_
    exact mem_inputsOf_of_inp (by rw [hd]; exact List.mem_append_left _ hy)
  obtain ⟨o, hpre, hc | ⟨w', hd'⟩⟩ := tagTraces_pre (hsat σ) hE hts hd hans
  · have hf := mixCall_p hc
    obtain ⟨n, h₀, rfl⟩ := pullFinish_finish hf
    obtain ⟨hn16, hpre⟩ := hpre n h₀ hf
    simp only [Returns] at hR
    obtain ⟨hnb, rfl, rfl, -⟩ := hR
    have hlen : (ps.buf.take n).length = n := by
      rw [List.length_take]; omega
    rcases hpre with hsent | ⟨c, hc, hσ⟩
    · rcases hs with hs | hs
      · rw [hs] at hsent; cases hsent
      · rw [hs] at hsent; exact absurd (Option.some.inj hsent).symm hne
    · rw [hσ] at hx
      cases hx
      exact ⟨by rw [hlen]; exact hn16, c, by rw [hlen, hc], rfl⟩
  · obtain ⟨c, rfl⟩ := pullRead_feed (mixAnswer_p hd')
    exact hR.elim

/-! ## The instantiated module -/

/-- The default value of the local. -/
def beD : List (Option Val) := [some (.i32 0)]

/-- The shape of the instantiated module. -/
def beOk : Bool :=
  match prep blobEcho with
  | some (c, st) => st.isNone && c.code.isEmpty && c.frame.module.mems == [0] &&
      exportFuncAddrs c.frame.module == [3] && c.store.mems.length == 1 &&
      (match c.store.funcs with
       | [f₀, f₁, f₂, f₃] => stubOk 0 2 f₀ && stubOk 1 2 f₁ && stubOk 2 2 f₂ &&
          fnOk [.i32] blobEchoBody 0 0 [0, 1, 2, 3] [0] beD f₃
       | _ => false)
  | none => false

theorem beOk_true : beOk = true := by decide +kernel

theorem be_facts {c : Config Nat} {st : Option FuncIdx} (hp : prep blobEcho = some (c, st)) :
    st = none ∧ c.code = [] ∧ c.frame.module.mems = [0] ∧ exportFuncAddrs c.frame.module = [3] ∧
    c.store.mems.length = 1 ∧ ∃ f₀ f₁ f₂ f₃, c.store.funcs = [f₀, f₁, f₂, f₃] ∧
      stubOk 0 2 f₀ = true ∧ stubOk 1 2 f₁ = true ∧ stubOk 2 2 f₂ = true ∧
      fnOk [.i32] blobEchoBody 0 0 [0, 1, 2, 3] [0] beD f₃ = true := by
  have h := beOk_true
  unfold beOk at h
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

theorem beMem : memSizes blobEcho = [65536] := by decide +kernel

/-- The store invariant: the instantiated functions, one memory of at least `16` bytes. -/
def beInv (s : Store Nat) : Prop :=
  ∃ c st, prep blobEcho = some (c, st) ∧ s.funcs = c.store.funcs ∧ s.mems.length = 1 ∧
    ∃ mi, s.mems[0]? = some mi ∧ 16 ≤ mi.bytes.size

/-! ## Observations -/

/-- What `blob(0, n)` observes in a memory of at least `16` bytes, for `n ≤ 16`. -/
theorem blob_bytes {i : Import} {s : Store Nat} {mi : MemInst} (hmi : s.mems[0]? = some mi)
    (hsz : 16 ≤ mi.bytes.size) {n : BitVec 32} (hn : n.toNat ≤ 16) :
    ∃ c : List UInt8, c.length = n.toNat ∧
      (calloutIn i (some 0) s [.i32 0, .i32 n]).bytes32 = some c := by
  refine ⟨bytesAt mi.bytes ⟨0, n.toNat⟩, Silmaril.Wasm.Logic.Core.length_bytesAt (by
    simp only [Region.InBounds, Region.stop]; omega), ?_⟩
  have hm : memOf (some 0) s = some mi.bytes := by simp [memOf, hmi]
  simp only [Callout.bytes32, calloutIn, Callout.args2, Callout.i32?, Val.i32,
    Option.bind_eq_bind, Option.bind_some, Callout.segment, hm]
  exact readBytes_toList (by simp; omega)

theorem memWrite_blob {o : Callout} {mem : Option ByteArray} {c : List UInt8} {h : BitVec 32}
    (hi : o.imp = ("sexp", "blob")) (hb : o.bytes32 = some c) :
    memWrite {} o ⟨.values [.i32 h], mem⟩ =
      some (.write (.atom ⟨.bytes, by decide, c⟩) [] h) := by
  have hr : replyI32 ⟨.values [.i32 h], mem⟩ = some h := rfl
  simp [memWrite, hr, hi, hb]

theorem finish_args {s : Store Nat} {v h h' : BitVec 32} {n : Nat}
    (hd : pullFinish {} (calloutIn ⟨"input", "finish", .func ⟨1⟩⟩ (some 0) s [.i32 v, .i32 h]) =
      some (.finish n h')) : n = v.toNat ∧ h' = h := by
  simp only [pullFinish, calloutIn, Val.i32, ↓reduceIte, usedOfI32, Option.map_eq_some_iff] at hd
  obtain ⟨n', hn', he⟩ := hd
  cases he
  split_ifs at hn'
  cases hn'
  exact ⟨rfl, rfl⟩

/-! ## The Hoare-logic proof -/

/-- **The body of `run`** under `beK sent σ`. -/
theorem be_body {P : Profile} {sent : Option (BitVec 32)} {σ : Env (BitVec 32) SymStrBytesSExp}
    {f₀ f₁ f₂ : FuncInst Nat}
    (h0 : stubOk 0 2 f₀ = true) (h1 : stubOk 1 2 f₁ = true) (h2 : stubOk 2 2 f₂ = true)
    {F : Frame} (hFf : F.module.funcs = [0, 1, 2, 3]) (hFl : F.locals = beD)
    {s : Store Nat} {fs : List (FuncInst Nat)} (hfs : fs = [f₀, f₁, f₂] ++ fs.drop 3)
    (hsf : s.funcs = fs) (hml : s.mems.length = 1) {mi : MemInst}
    (hmi : s.mems[0]? = some mi) (hsz : 16 ≤ mi.bytes.size)
    (hinv : ∀ s', s'.funcs = fs → s'.mems.length = 1 → ∀ mi', s'.mems[0]? = some mi' →
      16 ≤ mi'.bytes.size → beInv s') {Q : Post Nat} (hQ : BodyExits beInv Q) :
    HWP P (memHost blobEcho (some 0) (mixRoles {} {}) (beK sent σ)) s F
      (vals [] ++ expression blobEchoBody) Q := by
  obtain ⟨ps₀, rs₀, hc₀, he₀, hn₀⟩ := stubOk_spec h0
  obtain ⟨ps₁, rs₁, hc₁, he₁, hn₁⟩ := stubOk_spec h1
  obtain ⟨ps₂, rs₂, hc₂, he₂, hn₂⟩ := stubOk_spec h2
  have hf0 : ∀ s' : Store Nat, s'.funcs = fs → s'.funcs[0]? = some f₀ := fun s' h => by
    rw [h, hfs]; rfl
  have hf1 : ∀ s' : Store Nat, s'.funcs = fs → s'.funcs[1]? = some f₁ := fun s' h => by
    rw [h, hfs]; rfl
  have hf2 : ∀ s' : Store Nat, s'.funcs = fs → s'.funcs[2]? = some f₂ := fun s' h => by
    rw [h, hfs]; rfl
  unfold blobEchoBody
  -- read(0, 16)
  refine X.i32Const (us := []) ?_
  refine X.i32Const (us := [] ++ [.i32 0]) ?_
  refine hwp_call (us := []) (args := [.i32 0, .i32 16]) (x := ⟨0⟩) (k := 0) (fk := f₀)
    (i := ⟨"input", "read", .func ⟨0⟩⟩) (by rw [hFf]; rfl) (hf0 _ hsf) hc₀ he₀
    (by simp [hn₀]) rfl (fun n h hd => by simp [pullFinish, calloutIn] at hd) ?_
  rintro s₁ r ⟨⟨hfs₁, hml₁⟩, hg₁, hshape⟩ -
  obtain ⟨mi₁, hmi₁, hsz₁⟩ := hg₁ mi hmi
  have hfs₁' : s₁.funcs = fs := hfs₁.trans hsf
  have hml₁' : s₁.mems.length = 1 := hml₁.trans hml
  have hi₁ : beInv s₁ := hinv s₁ hfs₁' hml₁' mi₁ hmi₁ (by omega)
  refine ⟨fun res hr => ?_, fun _ => (hQ s₁ hi₁ F).2.2.1, fun a _ => (hQ s₁ hi₁ F).2.2.2 a⟩
  obtain ⟨n, rfl, hn⟩ := (hshape res hr).1 rfl
  have hn16 : n.toNat ≤ 16 := hn 0 16 rfl
  refine X.localSet (us := []) (x := ⟨0⟩) (by simp [hFl, beD, Idx.toNat]) ?_
  have hv : (F.setLocal ⟨0⟩ (.i32 n)).local? ⟨0⟩ = some (some (.i32 n)) := by
    simp [Frame.local?, Frame.setLocal, hFl, beD, Idx.toNat]
  refine X.localGet (us := []) hv ?_
  refine X.i32Const (us := [] ++ [.i32 n]) ?_
  refine X.localGet (us := [] ++ [.i32 n] ++ [.i32 0]) hv ?_
  -- blob(0, n)
  obtain ⟨c, hcl, hcb⟩ := blob_bytes (i := ⟨"sexp", "blob", .func ⟨0⟩⟩) hmi₁ (by omega) hn16
  show HWP _ _ _ _ (vals ([.i32 n] ++ [.i32 0, .i32 n]) ++ _) _
  refine hwp_call (us := [.i32 n]) (args := [.i32 0, .i32 n]) (x := ⟨1⟩) (k := 1) (fk := f₁)
    (i := ⟨"sexp", "blob", .func ⟨0⟩⟩) (by show F.module.funcs[_]? = _; rw [hFf]; rfl)
    (hf1 _ hfs₁') hc₁ he₁ (by simp [hn₁]) rfl
    (fun n h hd => by simp [pullFinish, calloutIn] at hd) ?_
  rintro s₂ r ⟨⟨hfs₂, hml₂⟩, hg₂, hshape⟩ hans
  obtain ⟨mi₂, hmi₂, hsz₂⟩ := hg₂ mi₁ hmi₁
  have hfs₂' : s₂.funcs = fs := hfs₂.trans hfs₁'
  have hml₂' : s₂.mems.length = 1 := hml₂.trans hml₁'
  have hi₂ : beInv s₂ := hinv s₂ hfs₂' hml₂' mi₂ hmi₂ (by omega)
  refine ⟨fun res hr => ?_, fun _ => (hQ s₂ hi₂ _).2.2.1, fun a _ => (hQ s₂ hi₂ _).2.2.2 a⟩
  obtain ⟨h, rfl⟩ := (hshape res hr).2.1 rfl
  subst hr
  have hagree : sent = some h ∨ σ h = some (bytesAtom c) := by
    have hw := mixAnswer_w (memWrite_blob (h := h) (mem := memOf (some 0) s₂) rfl hcb)
    rcases hans _ hw _ _ _ rfl with hs | ⟨t, ht, hσ⟩
    · exact .inl hs
    · simp only [Writer.built, Env.lookupAll, sexpW, List.mapM_nil] at ht
      rw [hσ, ← ht]
      exact .inr rfl
  -- finish(n, h)
  show HWP _ _ _ _ (vals ([] ++ [.i32 n, .i32 h]) ++ _) _
  refine hwp_call (us := []) (args := [.i32 n, .i32 h]) (x := ⟨2⟩) (k := 2) (fk := f₂)
    (i := ⟨"input", "finish", .func ⟨1⟩⟩) (by show F.module.funcs[_]? = _; rw [hFf]; rfl)
    (hf2 _ hfs₂') hc₂ he₂ (by simp [hn₂]) rfl (fun n' h' hd => ?_) ?_
  · obtain ⟨rfl, rfl⟩ := finish_args hd
    exact ⟨hn16, hagree.imp id fun hσ => ⟨c, hcl, hσ⟩⟩
  rintro s₃ r ⟨⟨hfs₃, hml₃⟩, hg₃, hshape⟩ -
  obtain ⟨mi₃, hmi₃, hsz₃⟩ := hg₃ mi₂ hmi₂
  have hi₃ : beInv s₃ := hinv s₃ (hfs₃.trans hfs₂') (hml₃.trans hml₂') mi₃ hmi₃ (by omega)
  refine ⟨fun res hr => ?_, fun _ => (hQ s₃ hi₃ _).2.2.1, fun a _ => (hQ s₃ hi₃ _).2.2.2 a⟩
  obtain rfl := (hshape res hr).2.2 rfl
  exact X.done (hQ s₃ hi₃ _).1

/-- **`blobEcho` meets `beK sent σ`**, for every profile, sentinel and store. -/
theorem be_sat (P : Profile) (sent : Option (BitVec 32)) (σ : Env (BitVec 32) SymStrBytesSExp) :
    MemSat P blobEcho 0 (mixRoles {} {}) (beK sent σ) beInv := by
  intro mt Is c₀ hI
  obtain ⟨c, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, hexp, hml, f₀, f₁, f₂, f₃, hf, h0, h1, h2, h3⟩ := be_facts hp
  obtain ⟨mi, hmis, hsize⟩ := one_page beMem hp
  have hmem : (c.withStart none).frame.module.mems[0]? = some 0 := by
    simp [Config.withStart, hmems]
  rw [hmem]
  have hinv : ∀ s', s'.funcs = c.store.funcs → s'.mems.length = 1 → ∀ mi', s'.mems[0]? = some mi' →
      16 ≤ mi'.bytes.size → beInv s' :=
    fun s' h h' mi' hm hz => ⟨c, none, hp, h, h', mi', hm, hz⟩
  refine ⟨fun n => Safe.of_exits (o := .normal []) (by simp [Config.withStart, hcode]; rfl)
    (fun _ _ => hinv _ rfl hml mi (by show c.store.mems[0]? = some mi; rw [hmis]; rfl)
      (by omega)), ?_⟩
  intro a ha
  rw [← haddr, hexp] at ha
  obtain rfl : a = 3 := by simpa using ha
  obtain ⟨code, ps, rs, hcode3, hloc, hbody, he, hps, hrs, hfuncs, -, hD⟩ := fnOk_spec h3
  have hfi : ∀ s, beInv s → s.funcs = c.store.funcs := by
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
  have hfs := hfi s hs
  obtain ⟨_, _, _, _, hml', mi', hmi', hsz'⟩ := hs
  exact be_body h0 h1 h2 (by simp [Frame.forCall, hfuncs]) (by simp [Frame.forCall, hD])
    (fs := c.store.funcs) (by rw [hf]; rfl) hfs hml' hmi' hsz' hinv hQ

/-- **Every pair `blobEcho` relates is in `lenRel`.** -/
theorem blobEcho_len (P : Profile) {pol : Policy (BitVec 32)} {ppol : PPolicy (BitVec 32)}
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) (hb : ppol.onBadHandle ≠ .ub)
    (ho : ppol.onOverrun ≠ .ub) (hs : pol.sentinel = none ∨ pol.sentinel = some ppol.sentinel) :
    memMixedRel P (ReplyEnvs blobReply) 0 blobEcho {} {} pol ppol ⊆ lenRel :=
  len_of_sat (fun σ => be_sat P pol.sentinel σ) (fun _ _ h => h) hw ha hb ho hs

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.PullMix
