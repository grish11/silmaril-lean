module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.LiveRun
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Cons

/-!
# Proofs: `consMod` accepts the list `(hi)`

Against the counting host `countEnv consOut` started at `q` (it answers `symbol`, `nil` and
`cons` with the next handle, `accept` with nothing, in the caller's store), the traced session of
`consMod` invokes `run` and runs its body to `accept(q + 2)`: `symbol(0, 2)` observes `68 69`
(handle `q`), `nil()` returns `q + 1`, `cons(q, q + 1)` returns `q + 2`. Its writer trace is
`[enter, write hi [] q, write nil [] (q+1), write cons [q, q+1] (q+2), accept (q+2)]`, which
accepts `(hi)` in the store semantics when none of the three handles is the policy's sentinel.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Cons

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game
  Silmaril.Wasm.Game.Accept Silmaril.Wasm.Game.IOAccept Silmaril.Accept Silmaril.Accept.Handle
  Silmaril.Accept.IO Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.Cons
  Silmaril.Wasm.Game.HandleAccept.MemSound.Live
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live

theorem consSpec_some : (Silmaril.Wasm.Verify.specInstance? consMod).isSome = true := by
  decide +kernel

theorem consMem : memSizes consMod = [65536] := by decide +kernel

theorem consOut_shape (k : Nat) (q : BitVec 32) : consShape k (consOut k q) := by
  rcases k with _ | _ | _ | _ | k <;> simp [consShape, consOut]

/-- The callout of `name(args)` in the store `s` (memory `0`). -/
abbrev co (name : String) (k : TypeIdx) (s : Store Nat) (args : List Val) : Callout :=
  calloutIn ⟨"sexp", name, .func k⟩ (some 0) s args

/-- **The writer trace of the session.** -/
theorem cons_traces (P : Profile) (q : BitVec 32) :
    [.enter, .write (.atom hiAtom) [] q, .write .nil [] (q + 1),
      .write .cons [q, q + 1] (q + 1 + 1), .accept (q + 1 + 1)] ∈
      consTraces P (ReplyEnvs consReply) 0 consMod {} := by
  obtain ⟨mt, Is, c₀, hI⟩ := spec_exists consSpec_some
  obtain ⟨c, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, hexp, hml, f₀, f₁, f₂, f₃, f₄, hf, h0, h1, h2, h3, h4⟩ :=
    cons_facts hp
  obtain ⟨mi, hmis, hsize⟩ := one_page consMem hp
  obtain ⟨ps₀, rs₀, hc₀, he₀, hn₀⟩ := stubOk_spec h0
  obtain ⟨ps₁, rs₁, hc₁, he₁, hn₁⟩ := stubOk_spec h1
  obtain ⟨ps₂, rs₂, hc₂, he₂, hn₂⟩ := stubOk_spec h2
  obtain ⟨ps₃, rs₃, hc₃, he₃, hn₃⟩ := stubOk_spec h3
  obtain ⟨code, ps, rs, hcode4, hloc, hbody, he, hps, hrs, hfuncs, hmems4, -⟩ := fnOk_spec h4
  rw [show c.withStart none = c from rfl] at hI
  have hmem0 : c.frame.module.mems[0]? = some 0 := by rw [hmems]; rfl
  have hmi : c.store.mems[0]? = some mi := by rw [hmis]; rfl
  let L := countEnv consOut
  let R := consRoles {}
  have t₀ : TSession P L consMod (some 0) R c q Is.addrs .inst false (c, q) [] := .start
  have hf4 : c.store.funcs[4]? = some f₄ := by rw [hf]; rfl
  have hok : InvokeOk c.store 4 [] := ⟨f₄, ps, rs, hf4, he, by
    rw [List.eq_nil_of_length_eq_zero (l := ps.toList) hps]; exact .nil⟩
  have ha : 4 ∈ Is.addrs := by rw [← haddr, hexp]; simp
  have t₁ := TSession.invoke t₀ (by decide) ⟨[], hcode⟩ ha hok
  let F : Frame := Frame.forCall f₄.module [] []
  have hFf : F.module.funcs = [0, 1, 2, 3, 4] := by simp [F, Frame.forCall, hfuncs]
  have hFm : F.module.mems = [0] := by simp [F, Frame.forCall, hmems4]
  have st₀ : Step P NH (invoke c.store 4 [])
      ⟨c.store, {}, [.frame 0 F [.label 0 [] (expression consBody)]]⟩ := by
    have h := Step.callRefFunc (P := P) (host := NH) (s := c.store) (f := {})
      (c := .callRefType ((c.store.funcs[4]?.map FuncInst.type).getD default)) (vs := [])
      (a := 4) (fi := f₄) (code := code) trivial hf4 he (by rw [hps]; rfl) hcode4
    rw [hrs, hloc, hbody] at h
    exact h
  -- "hi" at 0
  obtain ⟨b, hst⟩ := store_some (B := mi.bytes) (a := effAddr (0 : BitVec 32).toNat ⟨0, 0⟩)
    (n := PackSize.i16.width / 8) ((0x6968 : BitVec 32).setWidth _) (by rw [hsize]; decide)
  let s₁ := c.store.setMem 0 { mi with bytes := b }
  obtain ⟨-, hl₁, hfs₁⟩ := setMem_mems (mi := { mi with bytes := b }) hml
  have hfk : s₁.funcs[0]? = some f₀ ∧ s₁.funcs[1]? = some f₁ ∧ s₁.funcs[2]? = some f₂ ∧
      s₁.funcs[3]? = some f₃ := by rw [hfs₁, hf]; exact ⟨rfl, rfl, rfl, rfl⟩
  have st₁ : Step P NH ⟨c.store, {}, [.frame 0 F [.label 0 [] (expression consBody)]]⟩
      ⟨s₁, {}, [.frame 0 F [.label 0 [] (expression (consBody.drop 3))]]⟩ :=
    step_body (step_mid [] _ (step_storePack hFm hmi hst))
  -- symbol(0, 2)
  have st₂ : Step P NH ⟨s₁, {}, [.frame 0 F [.label 0 [] (expression (consBody.drop 3))]]⟩
      ⟨s₁, {}, (bodyCtx F (expression (consBody.drop 6))).fill
        (vals [.i32 0, .i32 2] ++ [.ref (.func 0), .callRefType f₀.type])⟩ :=
    step_body (step_mid [.i32 0, .i32 2] (expression (consBody.drop 6))
      (step_call (x := ⟨0⟩) (by rw [hFf]; rfl) hfk.1))
  have hd₁ : decompose? s₁ ((bodyCtx F (expression (consBody.drop 6))).fill
      (vals [.i32 0, .i32 2] ++ [.ref (.func 0), .callRefType f₀.type])) =
      some (bodyCtx F (expression (consBody.drop 6)), 0, 0, [.i32 0, .i32 2]) :=
    decompose_fill _ trivial hfk.1 he₀ (by rw [hn₀]; rfl) hc₀
  have t₂ := TSession.call (TSession.of_core_steps t₁
    ((st₀.steps.trans st₁.steps).trans st₂.steps)) hd₁
  have t₃ := TSession.answer t₂ hd₁ (a := ⟨s₁, .values [.i32 q]⟩) (q' := q + 1) ⟨rfl, rfl⟩
  -- nil()
  let E₂ : Ctx := .frame [] 0 F (.label [] 0 [] (.top [.i32 q] (expression (consBody.drop 7)))
    []) []
  have st₃ : Step P NH ⟨s₁, {}, (bodyCtx F (expression (consBody.drop 6))).fill
      (Result.values [.i32 q]).toAdmin⟩
      ⟨s₁, {}, E₂.fill (vals [] ++ [.ref (.func 1), .callRefType f₁.type])⟩ :=
    step_body (step_mid [.i32 q] (expression (consBody.drop 7))
      (step_call (x := ⟨1⟩) (by rw [hFf]; rfl) hfk.2.1))
  have hd₂ : decompose? s₁ (E₂.fill (vals [] ++ [.ref (.func 1), .callRefType f₁.type])) =
      some (E₂, 1, 1, []) :=
    decompose_fill _ trivial hfk.2.1 he₁ (by rw [hn₁]; rfl) hc₁
  have t₄ := TSession.call (TSession.of_core_steps t₃ st₃.steps) hd₂
  have t₅ := TSession.answer t₄ hd₂ (a := ⟨s₁, .values [.i32 (q + 1)]⟩) (q' := q + 1 + 1)
    ⟨rfl, rfl⟩
  -- cons(q, q + 1)
  have st₄ : Step P NH ⟨s₁, {}, E₂.fill (Result.values [.i32 (q + 1)]).toAdmin⟩
      ⟨s₁, {}, (bodyCtx F (expression (consBody.drop 8))).fill
        (vals [.i32 q, .i32 (q + 1)] ++ [.ref (.func 2), .callRefType f₂.type])⟩ :=
    step_body (step_mid [.i32 q, .i32 (q + 1)] (expression (consBody.drop 8))
      (step_call (x := ⟨2⟩) (by rw [hFf]; rfl) hfk.2.2.1))
  have hd₃ : decompose? s₁ ((bodyCtx F (expression (consBody.drop 8))).fill
      (vals [.i32 q, .i32 (q + 1)] ++ [.ref (.func 2), .callRefType f₂.type])) =
      some (bodyCtx F (expression (consBody.drop 8)), 2, 2, [.i32 q, .i32 (q + 1)]) :=
    decompose_fill _ trivial hfk.2.2.1 he₂ (by rw [hn₂]; rfl) hc₂
  have t₆ := TSession.call (TSession.of_core_steps t₅ st₄.steps) hd₃
  have t₇ := TSession.answer t₆ hd₃ (a := ⟨s₁, .values [.i32 (q + 1 + 1)]⟩)
    (q' := q + 1 + 1 + 1) ⟨rfl, rfl⟩
  -- accept(q + 2)
  have st₅ : Step P NH ⟨s₁, {}, (bodyCtx F (expression (consBody.drop 8))).fill
      (Result.values [.i32 (q + 1 + 1)]).toAdmin⟩
      ⟨s₁, {}, (bodyCtx F []).fill
        (vals [.i32 (q + 1 + 1)] ++ [.ref (.func 3), .callRefType f₃.type])⟩ :=
    step_body (step_mid [.i32 (q + 1 + 1)] [] (step_call (x := ⟨3⟩) (by rw [hFf]; rfl)
      hfk.2.2.2))
  have hd₄ : decompose? s₁ ((bodyCtx F []).fill
      (vals [.i32 (q + 1 + 1)] ++ [.ref (.func 3), .callRefType f₃.type])) =
      some (bodyCtx F [], 3, 3, [.i32 (q + 1 + 1)]) :=
    decompose_fill _ trivial hfk.2.2.2 he₃ (by rw [hn₃]; rfl) hc₃
  have t₈ := TSession.call (TSession.of_core_steps t₇ st₅.steps) hd₄
  -- the decoded events
  have hco₁ : calloutAt? consMod (some 0) ⟨s₁, {}, (bodyCtx F (expression (consBody.drop 6))).fill
      (vals [.i32 0, .i32 2] ++ [.ref (.func 0), .callRefType f₀.type])⟩ =
      some (co "symbol" ⟨0⟩ s₁ [.i32 0, .i32 2]) := by
    unfold calloutAt?; rw [hd₁]; rfl
  have hco₂ : calloutAt? consMod (some 0)
      ⟨s₁, {}, E₂.fill (vals [] ++ [.ref (.func 1), .callRefType f₁.type])⟩ =
      some (co "nil" ⟨3⟩ s₁ []) := by
    unfold calloutAt?; rw [hd₂]; rfl
  have hco₃ : calloutAt? consMod (some 0) ⟨s₁, {}, (bodyCtx F (expression (consBody.drop 8))).fill
      (vals [.i32 q, .i32 (q + 1)] ++ [.ref (.func 2), .callRefType f₂.type])⟩ =
      some (co "cons" ⟨0⟩ s₁ [.i32 q, .i32 (q + 1)]) := by
    unfold calloutAt?; rw [hd₃]; rfl
  have hco₄ : calloutAt? consMod (some 0) ⟨s₁, {}, (bodyCtx F []).fill
      (vals [.i32 (q + 1 + 1)] ++ [.ref (.func 3), .callRefType f₃.type])⟩ =
      some (co "accept" ⟨1⟩ s₁ [.i32 (q + 1 + 1)]) := by
    unfold calloutAt?; rw [hd₄]; rfl
  have hb : (co "symbol" ⟨0⟩ s₁ [.i32 0, .i32 2]).bytes32 = some [0x68, 0x69] := by
    rw [bytes32_of_store hml hst rfl]
    decide
  have hw₁ := consWrite_symbol (r := q) (mem := memOf (some 0) s₁) rfl hb
  have hw₂ := consWrite_nil (o := co "nil" ⟨3⟩ s₁ []) (r := q + 1) (mem := memOf (some 0) s₁)
    rfl rfl
  have hw₃ := consWrite_cons (o := co "cons" ⟨0⟩ s₁ [.i32 q, .i32 (q + 1)]) (r := q + 1 + 1)
    (mem := memOf (some 0) s₁) rfl rfl
  have hna₁ : consAccept {} (co "symbol" ⟨0⟩ s₁ [.i32 0, .i32 2]) = none :=
    consAccept_eq_none (by show ("sexp", "symbol") ≠ ("sexp", "accept"); decide)
  have hna₂ : consAccept {} (co "nil" ⟨3⟩ s₁ []) = none :=
    consAccept_eq_none (by show ("sexp", "nil") ≠ ("sexp", "accept"); decide)
  have hna₃ : consAccept {} (co "cons" ⟨0⟩ s₁ [.i32 q, .i32 (q + 1)]) = none :=
    consAccept_eq_none (by show ("sexp", "cons") ≠ ("sexp", "accept"); decide)
  have hac : consAccept {} (co "accept" ⟨1⟩ s₁ [.i32 (q + 1 + 1)]) =
      some (.accept (q + 1 + 1)) := by
    simp [consAccept, calloutIn, Callout.args1, Callout.i32?, Val.i32]
  rw [hco₁, hco₂, hco₃, hco₄] at t₈
  refine ⟨_, ⟨mt, Is, c, hI, L, q, countEnv_reply consOut_shape _, .run, true, _,
    by rw [hmem0]; exact t₈⟩, ?_⟩
  simp only [Option.elim, Roles.callTags, Roles.answerTags, R, consRoles]
  rw [hna₁, hw₁, hna₂, hw₂, hna₃, hw₃, hac]
  rfl

/-- **`consMod` accepts `(hi)`**, for every profile and policy. -/
theorem consMod_live (P : Profile) (pol : Policy (BitVec 32)) :
    hiList ∈ consWriterLang P (ReplyEnvs consReply) 0 consMod {} pol := by
  let q := base pol
  have hn₀ : pol.sentinel ≠ some q := by simpa using base_ne pol (k := 0) (by decide)
  have hn₁ : pol.sentinel ≠ some (q + 1) := base_ne pol (k := 1) (by decide)
  have hn₂ : pol.sentinel ≠ some (q + 1 + 1) := by
    rw [BitVec.add_assoc]; exact base_ne pol (k := 1 + 1) (by decide)
  have d₁ : q + 1 ≠ q := by bv_omega
  have d₂ : q + 1 + 1 ≠ q := by bv_omega
  have d₃ : q + 1 + 1 ≠ q + 1 := by bv_omega
  have e₁ : Function.update (Env.empty : Env (BitVec 32) (SExp2 MemAtom)) q
      (some (.atom hiAtom)) (q + 1) = none := by
    rw [Function.update_of_ne d₁]; rfl
  have e₂ : Function.update (Function.update (Env.empty : Env (BitVec 32) (SExp2 MemAtom)) q
      (some (.atom hiAtom))) (q + 1) (some .nil) (q + 1 + 1) = none := by
    rw [Function.update_of_ne d₃, Function.update_of_ne d₂]; rfl
  have hb : (consW MemAtom).built (Function.update (Function.update
      (Env.empty : Env (BitVec 32) (SExp2 MemAtom)) q (some (.atom hiAtom))) (q + 1)
      (some .nil)) .cons [q, q + 1] = some hiList := by
    simp [Writer.built, Env.lookupAll, consW, hiList]
  simp only [consWriterLang, writerLang, Host.lang]
  refine Set.mem_biUnion (cons_traces P q) ⟨_, _, .cons .enter
    (.cons (.writeOk (t := .atom hiAtom) rfl ⟨hn₀, .inl rfl⟩ fun _ h => by cases h)
    (.cons (.writeOk (t := .nil) rfl ⟨hn₁, .inl e₁⟩ fun _ h => by cases h)
    (.cons (.writeOk (t := hiList) hb ⟨hn₂, .inl e₂⟩ fun _ h => by cases h)
    (.cons (.acceptOk (t := hiList) (by simp)) (.nil _))))), by simp⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Cons
