module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Atoms

/-!
# Proofs: `atomMod name` accepts its atom

The traced session of `Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.Hi.hi_traces` with
the import name and the decoder abstracted (`atom_traces`): against the counting host
`countEnv hiOut` started at `q`, every roles decoding the answer `q` to `sexp.<name>(0, 2)` over
`68 69` as `ev q` and the call `accept(q)` as `acc q` gives the inputs `[enter, ev q, acc q]`.
A writer trace `[enter, write (atom a) [] q, accept q]` with `q` not the sentinel accepts
`atom a` (`atom_accepts`). Instances: strings, byte strings (`memRoles`), keywords (`kwRoles`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Atoms

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game
  Silmaril.Wasm.Game.Accept Silmaril.Wasm.Game.IOAccept Silmaril.Accept Silmaril.Accept.Handle
  Silmaril.Accept.IO Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.Live
  Silmaril.Wasm.Game.HandleAccept.MemSound.Atoms
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live

theorem hiOut_shape (k : Nat) (q : BitVec 32) : hiShape k (hiOut k q) := by
  rcases k with _ | _ | k <;> simp [hiShape, hiOut]

/-- **The traced session of `atomMod name`**, for every decoder. -/
theorem atom_traces {I : Type} {name : String}
    (hspec : (Silmaril.Wasm.Verify.specInstance? (atomMod name)).isSome = true)
    (hmz : memSizes (atomMod name) = [65536]) (hok : atomOk name = true)
    (R : Roles Unit I Unit Unit) (ent : I) (ev acc : BitVec 32 → I)
    (hout : ∀ o, R.callOut o = none)
    (hsymIn : ∀ o : Callout, o.imp = ("sexp", name) → R.callIn o = none)
    (hsymAns : ∀ (o : Callout) (q : BitVec 32) (mem : Option ByteArray), o.imp = ("sexp", name) →
      o.bytes32 = some [0x68, 0x69] → R.answerIn o ⟨.values [.i32 q], mem⟩ = some (ev q))
    (haccIn : ∀ (o : Callout) (q : BitVec 32), o.imp = ("sexp", "accept") →
      o.args = [.i32 q] → R.callIn o = some (acc q))
    (P : Profile) (q : BitVec 32) :
    [ent, ev q, acc q] ∈
      inputsOf (some ent) '' tagTraces P (ReplyEnvs hiReply) 0 (atomMod name) R := by
  obtain ⟨mt, Is, c₀, hI⟩ := spec_exists hspec
  obtain ⟨c, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, hexp, hml, f₀, f₁, f₂, hf, h0, h1, h2⟩ := atom_facts hok hp
  obtain ⟨mi, hmis, hsize⟩ := one_page hmz hp
  obtain ⟨ps₀, rs₀, hc₀, he₀, hn₀⟩ := stubOk_spec h0
  obtain ⟨ps₁, rs₁, hc₁, he₁, hn₁⟩ := stubOk_spec h1
  obtain ⟨code, ps, rs, hcode2, hloc, hbody, he, hps, hrs, hfuncs, hmems2, -⟩ := fnOk_spec h2
  rw [show c.withStart none = c from rfl] at hI
  have hmem0 : c.frame.module.mems[0]? = some 0 := by rw [hmems]; rfl
  have hf0 : c.store.funcs[0]? = some f₀ := by rw [hf]; rfl
  have hf1 : c.store.funcs[1]? = some f₁ := by rw [hf]; rfl
  have hf2 : c.store.funcs[2]? = some f₂ := by rw [hf]; rfl
  have hmi : c.store.mems[0]? = some mi := by rw [hmis]; rfl
  let F : Frame := Frame.forCall f₂.module [] []
  have hFf : F.module.funcs = [0, 1, 2] := by simp [F, Frame.forCall, hfuncs]
  have hFm : F.module.mems = [0] := by simp [F, Frame.forCall, hmems2]
  let L := countEnv hiOut
  have t₀ : TSession P L (atomMod name) (some 0) R c q Is.addrs .inst false (c, q) [] := .start
  have hok' : InvokeOk c.store 2 [] := ⟨f₂, ps, rs, hf2, he, by
    rw [List.eq_nil_of_length_eq_zero (l := ps.toList) hps]; exact .nil⟩
  have ha : 2 ∈ Is.addrs := by rw [← haddr, hexp]; simp
  have t₁ := TSession.invoke t₀ (by decide) ⟨[], hcode⟩ ha hok'
  have st₀ : Step P NH (invoke c.store 2 [])
      ⟨c.store, {}, [.frame 0 F [.label 0 [] (expression hiBody)]]⟩ := by
    have h := Step.callRefFunc (P := P) (host := NH) (s := c.store) (f := {})
      (c := .callRefType ((c.store.funcs[2]?.map FuncInst.type).getD default)) (vs := [])
      (a := 2) (fi := f₂) (code := code) trivial hf2 he (by rw [hps]; rfl) hcode2
    rw [hrs, hloc, hbody] at h
    exact h
  obtain ⟨b, hst⟩ := store_some (B := mi.bytes) (a := effAddr (0 : BitVec 32).toNat ⟨0, 0⟩)
    (n := PackSize.i16.width / 8) ((0x6968 : BitVec 32).setWidth _) (by rw [hsize]; decide)
  let s₁ := c.store.setMem 0 { mi with bytes := b }
  obtain ⟨-, hl₁, hfs₁⟩ := setMem_mems (mi := { mi with bytes := b }) hml
  have hf0' : s₁.funcs[0]? = some f₀ := by rw [hfs₁]; exact hf0
  have hf1' : s₁.funcs[1]? = some f₁ := by rw [hfs₁]; exact hf1
  have st₁ : Step P NH ⟨c.store, {}, [.frame 0 F [.label 0 [] (expression hiBody)]]⟩
      ⟨s₁, {}, [.frame 0 F [.label 0 [] (expression [.intConst .i32 0, .intConst .i32 2,
        .call ⟨0⟩, .call ⟨1⟩])]]⟩ :=
    step_body (step_mid [] _ (step_storePack hFm hmi hst))
  have st₂ : Step P NH ⟨s₁, {}, [.frame 0 F [.label 0 [] (expression [.intConst .i32 0,
      .intConst .i32 2, .call ⟨0⟩, .call ⟨1⟩])]]⟩
      ⟨s₁, {}, (bodyCtx F [.plain (.call ⟨1⟩)]).fill
        (vals [.i32 0, .i32 2] ++ [.ref (.func 0), .callRefType f₀.type])⟩ :=
    step_body (step_mid [.i32 0, .i32 2] [.plain (.call ⟨1⟩)]
      (step_call (x := ⟨0⟩) (by rw [hFf]; rfl) hf0'))
  have hd₁ : decompose? s₁ ((bodyCtx F [.plain (.call ⟨1⟩)]).fill
      (vals [.i32 0, .i32 2] ++ [.ref (.func 0), .callRefType f₀.type])) =
      some (bodyCtx F [.plain (.call ⟨1⟩)], 0, 0, [.i32 0, .i32 2]) :=
    decompose_fill _ trivial hf0' he₀ (by rw [hn₀]; rfl) hc₀
  have t₂ := TSession.call (TSession.of_core_steps t₁
    ((st₀.steps.trans st₁.steps).trans st₂.steps)) hd₁
  have t₃ := TSession.answer t₂ hd₁ (a := ⟨s₁, .values [.i32 q]⟩) (q' := q + 1) ⟨rfl, rfl⟩
  have st₃ : Step P NH ⟨s₁, {}, (bodyCtx F [.plain (.call ⟨1⟩)]).fill
      (Result.values [.i32 q]).toAdmin⟩
      ⟨s₁, {}, (bodyCtx F []).fill (vals [.i32 q] ++ [.ref (.func 1), .callRefType f₁.type])⟩ :=
    step_body (step_mid [.i32 q] [] (step_call (x := ⟨1⟩) (by rw [hFf]; rfl) hf1'))
  have hd₂ : decompose? s₁ ((bodyCtx F []).fill
      (vals [.i32 q] ++ [.ref (.func 1), .callRefType f₁.type])) =
      some (bodyCtx F [], 1, 1, [.i32 q]) :=
    decompose_fill _ trivial hf1' he₁ (by rw [hn₁]; rfl) hc₁
  have t₄ := TSession.call (TSession.of_core_steps t₃ st₃.steps) hd₂
  have hco₁ : calloutAt? (atomMod name) (some 0) ⟨s₁, {}, (bodyCtx F [.plain (.call ⟨1⟩)]).fill
      (vals [.i32 0, .i32 2] ++ [.ref (.func 0), .callRefType f₀.type])⟩ =
      some (calloutIn ⟨"sexp", name, .func ⟨0⟩⟩ (some 0) s₁ [.i32 0, .i32 2]) := by
    unfold calloutAt?; rw [hd₁]; rfl
  have hco₂ : calloutAt? (atomMod name) (some 0) ⟨s₁, {}, (bodyCtx F []).fill
      (vals [.i32 q] ++ [.ref (.func 1), .callRefType f₁.type])⟩ =
      some (calloutIn ⟨"sexp", "accept", .func ⟨1⟩⟩ (some 0) s₁ [.i32 q]) := by
    unfold calloutAt?; rw [hd₂]; rfl
  have hb : (calloutIn ⟨"sexp", name, .func ⟨0⟩⟩ (some 0) s₁ [.i32 0, .i32 2]).bytes32 =
      some [0x68, 0x69] := by
    rw [bytes32_of_store hml hst rfl]
    decide
  rw [hco₁, hco₂] at t₄
  refine ⟨_, ⟨mt, Is, c, hI, L, q, countEnv_reply hiOut_shape _, .run, true, _,
    by rw [hmem0]; exact t₄⟩, ?_⟩
  simp only [Option.elim, Roles.callTags, Roles.answerTags]
  rw [hout, hout, hsymIn _ rfl, hsymAns _ q _ rfl hb, haccIn _ q rfl rfl]
  rfl

/-- A writer trace writing and accepting one atom accepts it, for every policy. -/
theorem atom_accepts {α : Type} (pol : Policy (BitVec 32)) (a : α)
    {T : Set (List (WEv (SxOp α) (BitVec 32)))}
    (hT : [.enter, .write (.atom a) [] (base pol), .accept (base pol)] ∈ T) :
    .atom a ∈ writerLang (sexpW α) pol T := by
  have hne : pol.sentinel ≠ some (base pol) := by
    simpa using base_ne pol (k := 0) (by decide)
  simp only [writerLang, Host.lang]
  exact Set.mem_biUnion hT ⟨_, _, .cons .enter
    (.cons (.writeOk rfl ⟨hne, .inl rfl⟩ fun _ h => by cases h)
      (.cons (.acceptOk (t := .atom a) (by simp)) (.nil _))), by simp⟩

/-! ## Instances -/

theorem spec_string : (Silmaril.Wasm.Verify.specInstance? (atomMod "string")).isSome = true := by
  decide +kernel
theorem spec_blob : (Silmaril.Wasm.Verify.specInstance? (atomMod "blob")).isSome = true := by
  decide +kernel
theorem spec_keyword :
    (Silmaril.Wasm.Verify.specInstance? (atomMod "keyword")).isSome = true := by
  decide +kernel
theorem mem_string : memSizes (atomMod "string") = [65536] := by decide +kernel
theorem mem_blob : memSizes (atomMod "blob") = [65536] := by decide +kernel
theorem mem_keyword : memSizes (atomMod "keyword") = [65536] := by decide +kernel

theorem memAccept_acc (o : Callout) (q : BitVec 32) (hi : o.imp = ("sexp", "accept"))
    (ha : o.args = [.i32 q]) : (memRoles {}).callIn o = some (.accept q) := by
  simp [memRoles, memAccept, hi, ha, Callout.args1, Callout.i32?, Val.i32]

theorem kwAccept_acc (o : Callout) (q : BitVec 32) (hi : o.imp = ("sexp", "accept"))
    (ha : o.args = [.i32 q]) : (kwRoles {}).callIn o = some (.accept q) := by
  simp [kwRoles, kwAccept, hi, ha, Callout.args1, Callout.i32?, Val.i32]

/-- `atomMod "string"` accepts the string `"hi"`. -/
theorem str_live (P : Profile) (pol : Policy (BitVec 32)) :
    .atom strAtom ∈ memWriterLang P (ReplyEnvs hiReply) 0 (atomMod "string") {} pol :=
  atom_accepts pol strAtom (atom_traces spec_string mem_string atomOk_string (memRoles {}) .enter
    (fun q => .write (.atom strAtom) [] q) .accept (fun _ => rfl)
    (fun _ hi => memAccept_eq_none (by rw [hi]; decide))
    (fun o q mem hi hb => by
      have hr : replyI32 ⟨.values [.i32 q], mem⟩ = some q := rfl
      simp [memRoles, memWrite, hr, hi, hb, utf8_hi, strAtom])
    memAccept_acc P (base pol))

/-- `atomMod "blob"` accepts the byte string `68 69`. -/
theorem blob_live (P : Profile) (pol : Policy (BitVec 32)) :
    .atom blobAtom ∈ memWriterLang P (ReplyEnvs hiReply) 0 (atomMod "blob") {} pol :=
  atom_accepts pol blobAtom (atom_traces spec_blob mem_blob atomOk_blob (memRoles {}) .enter
    (fun q => .write (.atom blobAtom) [] q) .accept (fun _ => rfl)
    (fun _ hi => memAccept_eq_none (by rw [hi]; decide))
    (fun o q mem hi hb => by
      have hr : replyI32 ⟨.values [.i32 q], mem⟩ = some q := rfl
      simp [memRoles, memWrite, hr, hi, hb, blobAtom])
    memAccept_acc P (base pol))

/-- `atomMod "keyword"` accepts the keyword `hi`. -/
theorem kw_live (P : Profile) (pol : Policy (BitVec 32)) :
    .atom kwAtom ∈ kwWriterLang P (ReplyEnvs hiReply) 0 (atomMod "keyword") {} pol :=
  atom_accepts pol kwAtom (atom_traces spec_keyword mem_keyword atomOk_keyword (kwRoles {})
    .enter (fun q => .write (.atom kwAtom) [] q) .accept (fun _ => rfl)
    (fun o hi => by simp [kwRoles, kwAccept, hi])
    (fun o q mem hi hb => by
      have hr : replyI32 ⟨.values [.i32 q], mem⟩ = some q := rfl
      simp [kwRoles, kwWrite, hr, hi, hb, utf8_hi, kwAtom])
    kwAccept_acc P (base pol))

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Atoms
