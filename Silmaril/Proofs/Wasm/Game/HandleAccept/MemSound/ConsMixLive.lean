module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ConsLive
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ConsMix

/-!
# Proofs: `consMix` accepts the list `(hi "hi")`

Against the counting host `countEnv consMixOut` started at `q` (one fresh handle from `symbol`,
`string`, `nil` and `cons`, nothing from `accept`, in the caller's store), the traced session of
`consMix` runs `run` to `accept(q + 4)`: `symbol(0, 2)` and `string(0, 2)` observe `68 69`
(handles `q`, `q + 1`), `nil()` returns `q + 2`, `cons(q + 1, q + 2)` returns `q + 3` and
`cons(q, q + 3)` returns `q + 4`.
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

theorem consMixSpec_some : (Silmaril.Wasm.Verify.specInstance? consMix).isSome = true := by
  decide +kernel

theorem consMixMem : memSizes consMix = [65536] := by decide +kernel

theorem consMixOut_shape (k : Nat) (q : BitVec 32) : consMixShape k (consMixOut k q) := by
  rcases k with _ | _ | _ | _ | _ | k <;> simp [consMixShape, consMixOut]

/-- **The writer trace of the session.** -/
theorem consMix_traces (P : Profile) (q : BitVec 32) :
    [.enter, .write (.atom hiAtom) [] q, .write (.atom hiStr) [] (q + 1),
      .write .nil [] (q + 1 + 1), .write .cons [q + 1, q + 1 + 1] (q + 1 + 1 + 1),
      .write .cons [q, q + 1 + 1 + 1] (q + 1 + 1 + 1 + 1), .accept (q + 1 + 1 + 1 + 1)] ∈
      consTraces P (ReplyEnvs consMixReply) 0 consMix {} := by
  obtain ⟨mt, Is, c₀, hI⟩ := spec_exists consMixSpec_some
  obtain ⟨c, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, hexp, hml, f₀, f₁, f₂, f₃, f₄, f₅, hf, h0, h1, h2, h3, h4, h5⟩ :=
    consMix_facts hp
  obtain ⟨mi, hmis, hsize⟩ := one_page consMixMem hp
  obtain ⟨ps₀, rs₀, hc₀, he₀, hn₀⟩ := stubOk_spec h0
  obtain ⟨ps₁, rs₁, hc₁, he₁, hn₁⟩ := stubOk_spec h1
  obtain ⟨ps₂, rs₂, hc₂, he₂, hn₂⟩ := stubOk_spec h2
  obtain ⟨ps₃, rs₃, hc₃, he₃, hn₃⟩ := stubOk_spec h3
  obtain ⟨ps₄, rs₄, hc₄, he₄, hn₄⟩ := stubOk_spec h4
  obtain ⟨code, ps, rs, hcode5, hloc, hbody, he, hps, hrs, hfuncs, hmems5, -⟩ := fnOk_spec h5
  rw [show c.withStart none = c from rfl] at hI
  have hmem0 : c.frame.module.mems[0]? = some 0 := by rw [hmems]; rfl
  have hmi : c.store.mems[0]? = some mi := by rw [hmis]; rfl
  let L := countEnv consMixOut
  let R := consRoles {}
  have t₀ : TSession P L consMix (some 0) R c q Is.addrs .inst false (c, q) [] := .start
  have hf5 : c.store.funcs[5]? = some f₅ := by rw [hf]; rfl
  have hok : InvokeOk c.store 5 [] := ⟨f₅, ps, rs, hf5, he, by
    rw [List.eq_nil_of_length_eq_zero (l := ps.toList) hps]; exact .nil⟩
  have ha : 5 ∈ Is.addrs := by rw [← haddr, hexp]; simp
  have t₁ := TSession.invoke t₀ (by decide) ⟨[], hcode⟩ ha hok
  let F : Frame := Frame.forCall f₅.module [] []
  have hFf : F.module.funcs = [0, 1, 2, 3, 4, 5] := by simp [F, Frame.forCall, hfuncs]
  have hFm : F.module.mems = [0] := by simp [F, Frame.forCall, hmems5]
  have st₀ : Step P NH (invoke c.store 5 [])
      ⟨c.store, {}, [.frame 0 F [.label 0 [] (expression consMixBody)]]⟩ := by
    have h := Step.callRefFunc (P := P) (host := NH) (s := c.store) (f := {})
      (c := .callRefType ((c.store.funcs[5]?.map FuncInst.type).getD default)) (vs := [])
      (a := 5) (fi := f₅) (code := code) trivial hf5 he (by rw [hps]; rfl) hcode5
    rw [hrs, hloc, hbody] at h
    exact h
  have hfk : ∀ s : Store Nat, s.funcs = c.store.funcs → s.funcs[0]? = some f₀ ∧
      s.funcs[1]? = some f₁ ∧ s.funcs[2]? = some f₂ ∧ s.funcs[3]? = some f₃ ∧
      s.funcs[4]? = some f₄ := by
    intro s h; rw [h, hf]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  -- "hi" at 0
  obtain ⟨b, hst⟩ := store_some (B := mi.bytes) (a := effAddr (0 : BitVec 32).toNat ⟨0, 0⟩)
    (n := PackSize.i16.width / 8) ((0x6968 : BitVec 32).setWidth _) (by rw [hsize]; decide)
  have hz₁ : b.size = 65536 := (Silmaril.Wasm.Logic.Core.size_store hst).trans hsize
  let mi₁ : MemInst := { mi with bytes := b }
  let s₁ := c.store.setMem 0 mi₁
  obtain ⟨hm₁, hl₁, hfs₁⟩ := setMem_mems (mi := mi₁) hml
  have hk₁ := hfk s₁ hfs₁
  have st₁ : Step P NH ⟨c.store, {}, [.frame 0 F [.label 0 [] (expression consMixBody)]]⟩
      ⟨s₁, {}, [.frame 0 F [.label 0 [] (expression (consMixBody.drop 3))]]⟩ :=
    step_body (step_mid [] _ (step_storePack hFm hmi hst))
  -- symbol(0, 2)
  have st₂ : Step P NH ⟨s₁, {}, [.frame 0 F [.label 0 [] (expression (consMixBody.drop 3))]]⟩
      ⟨s₁, {}, (bodyCtx F (expression (consMixBody.drop 6))).fill
        (vals [.i32 0, .i32 2] ++ [.ref (.func 0), .callRefType f₀.type])⟩ :=
    step_body (step_mid [.i32 0, .i32 2] (expression (consMixBody.drop 6))
      (step_call (x := ⟨0⟩) (by rw [hFf]; rfl) hk₁.1))
  have hd₁ : decompose? s₁ ((bodyCtx F (expression (consMixBody.drop 6))).fill
      (vals [.i32 0, .i32 2] ++ [.ref (.func 0), .callRefType f₀.type])) =
      some (bodyCtx F (expression (consMixBody.drop 6)), 0, 0, [.i32 0, .i32 2]) :=
    decompose_fill _ trivial hk₁.1 he₀ (by rw [hn₀]; rfl) hc₀
  have t₂ := TSession.call (TSession.of_core_steps t₁
    ((st₀.steps.trans st₁.steps).trans st₂.steps)) hd₁
  have t₃ := TSession.answer t₂ hd₁ (a := ⟨s₁, .values [.i32 q]⟩) (q' := q + 1) ⟨rfl, rfl⟩
  -- "hi" at 0 again
  obtain ⟨b₂, hst₂⟩ := store_some (B := mi₁.bytes) (a := effAddr (0 : BitVec 32).toNat ⟨0, 0⟩)
    (n := PackSize.i16.width / 8) ((0x6968 : BitVec 32).setWidth _) (by rw [hz₁]; decide)
  let s₂ := s₁.setMem 0 { mi₁ with bytes := b₂ }
  obtain ⟨-, hl₂, hfs₂⟩ := setMem_mems (s := s₁) (mi := { mi₁ with bytes := b₂ }) hl₁
  have hk₂ := hfk s₂ (hfs₂.trans hfs₁)
  have st₃ : Step P NH ⟨s₁, {}, (bodyCtx F (expression (consMixBody.drop 6))).fill
      (Result.values [.i32 q]).toAdmin⟩
      ⟨s₂, {}, [.frame 0 F [.label 0 [] (vals [.i32 q] ++ [] ++
        expression (consMixBody.drop 9))]]⟩ :=
    step_body (step_mid [.i32 q] (expression (consMixBody.drop 9))
      (step_storePack hFm hm₁ hst₂))
  -- string(0, 2)
  let E₂ : Ctx := .frame [] 0 F (.label [] 0 []
    (.top [.i32 q] (expression (consMixBody.drop 12))) []) []
  have st₄ : Step P NH ⟨s₂, {}, [.frame 0 F [.label 0 [] (vals [.i32 q] ++ [] ++
        expression (consMixBody.drop 9))]]⟩
      ⟨s₂, {}, E₂.fill (vals [.i32 0, .i32 2] ++ [.ref (.func 1), .callRefType f₁.type])⟩ :=
    step_body (step_mid [.i32 q, .i32 0, .i32 2] (expression (consMixBody.drop 12))
      (step_call (x := ⟨1⟩) (by rw [hFf]; rfl) hk₂.2.1))
  have hd₂ : decompose? s₂ (E₂.fill (vals [.i32 0, .i32 2] ++
      [.ref (.func 1), .callRefType f₁.type])) = some (E₂, 1, 1, [.i32 0, .i32 2]) :=
    decompose_fill _ trivial hk₂.2.1 he₁ (by rw [hn₁]; rfl) hc₁
  have t₄ := TSession.call (TSession.of_core_steps t₃ (st₃.steps.trans st₄.steps)) hd₂
  have t₅ := TSession.answer t₄ hd₂ (a := ⟨s₂, .values [.i32 (q + 1)]⟩) (q' := q + 1 + 1)
    ⟨rfl, rfl⟩
  -- nil()
  let E₃ : Ctx := .frame [] 0 F (.label [] 0 []
    (.top [.i32 q, .i32 (q + 1)] (expression (consMixBody.drop 13))) []) []
  have st₅ : Step P NH ⟨s₂, {}, E₂.fill (Result.values [.i32 (q + 1)]).toAdmin⟩
      ⟨s₂, {}, E₃.fill (vals [] ++ [.ref (.func 2), .callRefType f₂.type])⟩ :=
    step_body (step_mid [.i32 q, .i32 (q + 1)] (expression (consMixBody.drop 13))
      (step_call (x := ⟨2⟩) (by rw [hFf]; rfl) hk₂.2.2.1))
  have hd₃ : decompose? s₂ (E₃.fill (vals [] ++ [.ref (.func 2), .callRefType f₂.type])) =
      some (E₃, 2, 2, []) :=
    decompose_fill _ trivial hk₂.2.2.1 he₂ (by rw [hn₂]; rfl) hc₂
  have t₆ := TSession.call (TSession.of_core_steps t₅ st₅.steps) hd₃
  have t₇ := TSession.answer t₆ hd₃ (a := ⟨s₂, .values [.i32 (q + 1 + 1)]⟩)
    (q' := q + 1 + 1 + 1) ⟨rfl, rfl⟩
  -- cons(q + 1, q + 2)
  let E₄ : Ctx := .frame [] 0 F (.label [] 0 []
    (.top [.i32 q] (expression (consMixBody.drop 14))) []) []
  have st₆ : Step P NH ⟨s₂, {}, E₃.fill (Result.values [.i32 (q + 1 + 1)]).toAdmin⟩
      ⟨s₂, {}, E₄.fill (vals [.i32 (q + 1), .i32 (q + 1 + 1)] ++
        [.ref (.func 3), .callRefType f₃.type])⟩ :=
    step_body (step_mid [.i32 q, .i32 (q + 1), .i32 (q + 1 + 1)]
      (expression (consMixBody.drop 14)) (step_call (x := ⟨3⟩) (by rw [hFf]; rfl) hk₂.2.2.2.1))
  have hd₄ : decompose? s₂ (E₄.fill (vals [.i32 (q + 1), .i32 (q + 1 + 1)] ++
      [.ref (.func 3), .callRefType f₃.type])) =
      some (E₄, 3, 3, [.i32 (q + 1), .i32 (q + 1 + 1)]) :=
    decompose_fill _ trivial hk₂.2.2.2.1 he₃ (by rw [hn₃]; rfl) hc₃
  have t₈ := TSession.call (TSession.of_core_steps t₇ st₆.steps) hd₄
  have t₉ := TSession.answer t₈ hd₄ (a := ⟨s₂, .values [.i32 (q + 1 + 1 + 1)]⟩)
    (q' := q + 1 + 1 + 1 + 1) ⟨rfl, rfl⟩
  -- cons(q, q + 3)
  have st₇ : Step P NH ⟨s₂, {}, E₄.fill (Result.values [.i32 (q + 1 + 1 + 1)]).toAdmin⟩
      ⟨s₂, {}, (bodyCtx F (expression (consMixBody.drop 15))).fill
        (vals [.i32 q, .i32 (q + 1 + 1 + 1)] ++ [.ref (.func 3), .callRefType f₃.type])⟩ :=
    step_body (step_mid [.i32 q, .i32 (q + 1 + 1 + 1)] (expression (consMixBody.drop 15))
      (step_call (x := ⟨3⟩) (by rw [hFf]; rfl) hk₂.2.2.2.1))
  have hd₅ : decompose? s₂ ((bodyCtx F (expression (consMixBody.drop 15))).fill
      (vals [.i32 q, .i32 (q + 1 + 1 + 1)] ++ [.ref (.func 3), .callRefType f₃.type])) =
      some (bodyCtx F (expression (consMixBody.drop 15)), 3, 3,
        [.i32 q, .i32 (q + 1 + 1 + 1)]) :=
    decompose_fill _ trivial hk₂.2.2.2.1 he₃ (by rw [hn₃]; rfl) hc₃
  have t₁₀ := TSession.call (TSession.of_core_steps t₉ st₇.steps) hd₅
  have t₁₁ := TSession.answer t₁₀ hd₅ (a := ⟨s₂, .values [.i32 (q + 1 + 1 + 1 + 1)]⟩)
    (q' := q + 1 + 1 + 1 + 1 + 1) ⟨rfl, rfl⟩
  -- accept(q + 4)
  have st₈ : Step P NH ⟨s₂, {}, (bodyCtx F (expression (consMixBody.drop 15))).fill
      (Result.values [.i32 (q + 1 + 1 + 1 + 1)]).toAdmin⟩
      ⟨s₂, {}, (bodyCtx F []).fill
        (vals [.i32 (q + 1 + 1 + 1 + 1)] ++ [.ref (.func 4), .callRefType f₄.type])⟩ :=
    step_body (step_mid [.i32 (q + 1 + 1 + 1 + 1)] [] (step_call (x := ⟨4⟩)
      (by rw [hFf]; rfl) hk₂.2.2.2.2))
  have hd₆ : decompose? s₂ ((bodyCtx F []).fill
      (vals [.i32 (q + 1 + 1 + 1 + 1)] ++ [.ref (.func 4), .callRefType f₄.type])) =
      some (bodyCtx F [], 4, 4, [.i32 (q + 1 + 1 + 1 + 1)]) :=
    decompose_fill _ trivial hk₂.2.2.2.2 he₄ (by rw [hn₄]; rfl) hc₄
  have t₁₂ := TSession.call (TSession.of_core_steps t₁₁ st₈.steps) hd₆
  -- the decoded events
  have hco₁ : calloutAt? consMix (some 0)
      ⟨s₁, {}, (bodyCtx F (expression (consMixBody.drop 6))).fill
        (vals [.i32 0, .i32 2] ++ [.ref (.func 0), .callRefType f₀.type])⟩ =
      some (co "symbol" ⟨0⟩ s₁ [.i32 0, .i32 2]) := by
    unfold calloutAt?; rw [hd₁]; rfl
  have hco₂ : calloutAt? consMix (some 0)
      ⟨s₂, {}, E₂.fill (vals [.i32 0, .i32 2] ++ [.ref (.func 1), .callRefType f₁.type])⟩ =
      some (co "string" ⟨0⟩ s₂ [.i32 0, .i32 2]) := by
    unfold calloutAt?; rw [hd₂]; rfl
  have hco₃ : calloutAt? consMix (some 0)
      ⟨s₂, {}, E₃.fill (vals [] ++ [.ref (.func 2), .callRefType f₂.type])⟩ =
      some (co "nil" ⟨3⟩ s₂ []) := by
    unfold calloutAt?; rw [hd₃]; rfl
  have hco₄ : calloutAt? consMix (some 0)
      ⟨s₂, {}, E₄.fill (vals [.i32 (q + 1), .i32 (q + 1 + 1)] ++
        [.ref (.func 3), .callRefType f₃.type])⟩ =
      some (co "cons" ⟨0⟩ s₂ [.i32 (q + 1), .i32 (q + 1 + 1)]) := by
    unfold calloutAt?; rw [hd₄]; rfl
  have hco₅ : calloutAt? consMix (some 0)
      ⟨s₂, {}, (bodyCtx F (expression (consMixBody.drop 15))).fill
        (vals [.i32 q, .i32 (q + 1 + 1 + 1)] ++ [.ref (.func 3), .callRefType f₃.type])⟩ =
      some (co "cons" ⟨0⟩ s₂ [.i32 q, .i32 (q + 1 + 1 + 1)]) := by
    unfold calloutAt?; rw [hd₅]; rfl
  have hco₆ : calloutAt? consMix (some 0) ⟨s₂, {}, (bodyCtx F []).fill
      (vals [.i32 (q + 1 + 1 + 1 + 1)] ++ [.ref (.func 4), .callRefType f₄.type])⟩ =
      some (co "accept" ⟨1⟩ s₂ [.i32 (q + 1 + 1 + 1 + 1)]) := by
    unfold calloutAt?; rw [hd₆]; rfl
  have hb₁ : (co "symbol" ⟨0⟩ s₁ [.i32 0, .i32 2]).bytes32 = some [0x68, 0x69] := by
    rw [bytes32_of_store hml hst rfl]
    decide
  have hb₂ : (co "string" ⟨0⟩ s₂ [.i32 0, .i32 2]).bytes32 = some [0x68, 0x69] := by
    rw [bytes32_of_store hl₁ hst₂ rfl]
    decide
  have hw₁ := consWrite_symbol (r := q) (mem := memOf (some 0) s₁) rfl hb₁
  have hw₂ := consWrite_string (r := q + 1) (mem := memOf (some 0) s₂) rfl hb₂
  have hw₃ := consWrite_nil (o := co "nil" ⟨3⟩ s₂ []) (r := q + 1 + 1)
    (mem := memOf (some 0) s₂) rfl rfl
  have hw₄ := consWrite_cons (o := co "cons" ⟨0⟩ s₂ [.i32 (q + 1), .i32 (q + 1 + 1)])
    (r := q + 1 + 1 + 1) (mem := memOf (some 0) s₂) rfl rfl
  have hw₅ := consWrite_cons (o := co "cons" ⟨0⟩ s₂ [.i32 q, .i32 (q + 1 + 1 + 1)])
    (r := q + 1 + 1 + 1 + 1) (mem := memOf (some 0) s₂) rfl rfl
  have hna₁ : consAccept {} (co "symbol" ⟨0⟩ s₁ [.i32 0, .i32 2]) = none :=
    consAccept_eq_none (by show ("sexp", "symbol") ≠ ("sexp", "accept"); decide)
  have hna₂ : consAccept {} (co "string" ⟨0⟩ s₂ [.i32 0, .i32 2]) = none :=
    consAccept_eq_none (by show ("sexp", "string") ≠ ("sexp", "accept"); decide)
  have hna₃ : consAccept {} (co "nil" ⟨3⟩ s₂ []) = none :=
    consAccept_eq_none (by show ("sexp", "nil") ≠ ("sexp", "accept"); decide)
  have hna₄ : ∀ args, consAccept {} (co "cons" ⟨0⟩ s₂ args) = none := fun _ =>
    consAccept_eq_none (by show ("sexp", "cons") ≠ ("sexp", "accept"); decide)
  have hac : consAccept {} (co "accept" ⟨1⟩ s₂ [.i32 (q + 1 + 1 + 1 + 1)]) =
      some (.accept (q + 1 + 1 + 1 + 1)) := by
    simp [consAccept, calloutIn, Callout.args1, Callout.i32?, Val.i32]
  rw [hco₁, hco₂, hco₃, hco₄, hco₅, hco₆] at t₁₂
  refine ⟨_, ⟨mt, Is, c, hI, L, q, countEnv_reply consMixOut_shape _, .run, true, _,
    by rw [hmem0]; exact t₁₂⟩, ?_⟩
  simp only [Option.elim, Roles.callTags, Roles.answerTags, R, consRoles]
  rw [hna₁, hw₁, hna₂, hw₂, hna₃, hw₃, hna₄, hw₄, hna₄, hw₅, hac]
  rfl

set_option maxHeartbeats 1000000 in
/-- **`consMix` accepts `(hi "hi")`**, for every profile and policy. -/
theorem consMix_live (P : Profile) (pol : Policy (BitVec 32)) :
    mixList ∈ consWriterLang P (ReplyEnvs consMixReply) 0 consMix {} pol := by
  let q := base pol
  have hn : ∀ k : BitVec 32, k + 1 ≠ 0 → pol.sentinel ≠ some (q + k) := fun k hk =>
    base_ne pol hk
  have hn₀ : pol.sentinel ≠ some q := by simpa using hn 0 (by decide)
  have hn₁ : pol.sentinel ≠ some (q + 1) := hn 1 (by decide)
  have hn₂ : pol.sentinel ≠ some (q + 1 + 1) := by
    rw [show q + 1 + 1 = q + 2 by bv_omega]; exact hn 2 (by decide)
  have hn₃ : pol.sentinel ≠ some (q + 1 + 1 + 1) := by
    rw [show q + 1 + 1 + 1 = q + 3 by bv_omega]; exact hn 3 (by decide)
  have hn₄ : pol.sentinel ≠ some (q + 1 + 1 + 1 + 1) := by
    rw [show q + 1 + 1 + 1 + 1 = q + 4 by bv_omega]; exact hn 4 (by decide)
  let ρ₁ : Env (BitVec 32) (SExp2 MemAtom) := Function.update Env.empty q (some (.atom hiAtom))
  let ρ₂ := Function.update ρ₁ (q + 1) (some (.atom hiStr))
  let ρ₃ := Function.update ρ₂ (q + 1 + 1) (some .nil)
  let ρ₄ := Function.update ρ₃ (q + 1 + 1 + 1) (some (.cons (.atom hiStr) .nil))
  have e₁ : ρ₁ (q + 1) = none := by
    simp only [ρ₁]; rw [Function.update_of_ne (by bv_omega)]; rfl
  have e₂ : ρ₂ (q + 1 + 1) = none := by
    simp only [ρ₂, ρ₁]
    rw [Function.update_of_ne (by bv_omega), Function.update_of_ne (by bv_omega)]; rfl
  have e₃ : ρ₃ (q + 1 + 1 + 1) = none := by
    simp only [ρ₃, ρ₂, ρ₁]
    rw [Function.update_of_ne (by bv_omega), Function.update_of_ne (by bv_omega),
      Function.update_of_ne (by bv_omega)]; rfl
  have e₄ : ρ₄ (q + 1 + 1 + 1 + 1) = none := by
    simp only [ρ₄, ρ₃, ρ₂, ρ₁]
    rw [Function.update_of_ne (by bv_omega), Function.update_of_ne (by bv_omega),
      Function.update_of_ne (by bv_omega), Function.update_of_ne (by bv_omega)]; rfl
  have g₁ : ρ₃ (q + 1) = some (.atom hiStr) := by
    simp only [ρ₃, ρ₂]
    rw [Function.update_of_ne (by bv_omega), Function.update_self]
  have g₂ : ρ₃ (q + 1 + 1) = some .nil := Function.update_self _ _ _
  have g₃ : ρ₄ q = some (.atom hiAtom) := by
    simp only [ρ₄, ρ₃, ρ₂, ρ₁]
    rw [Function.update_of_ne (by bv_omega), Function.update_of_ne (by bv_omega),
      Function.update_of_ne (by bv_omega), Function.update_self]
  have g₄ : ρ₄ (q + 1 + 1 + 1) = some (.cons (.atom hiStr) .nil) := Function.update_self _ _ _
  have hb₄ : (consW MemAtom).built ρ₃ .cons [q + 1, q + 1 + 1] =
      some (.cons (.atom hiStr) .nil) := by
    unfold Writer.built Env.lookupAll
    rw [List.mapM_cons, List.mapM_cons, List.mapM_nil, g₁, g₂]
    rfl
  have hb₅ : (consW MemAtom).built ρ₄ .cons [q, q + 1 + 1 + 1] = some mixList := by
    unfold Writer.built Env.lookupAll
    rw [List.mapM_cons, List.mapM_cons, List.mapM_nil, g₃, g₄]
    rfl
  simp only [consWriterLang, writerLang, Host.lang]
  refine Set.mem_biUnion (consMix_traces P q) ⟨_, _, .cons .enter
    (.cons (.writeOk (t := .atom hiAtom) rfl ⟨hn₀, .inl rfl⟩ fun _ h => by cases h)
    (.cons (.writeOk (t := .atom hiStr) rfl ⟨hn₁, .inl e₁⟩ fun _ h => by cases h)
    (.cons (.writeOk (t := .nil) rfl ⟨hn₂, .inl e₂⟩ fun _ h => by cases h)
    (.cons (.writeOk (t := .cons (.atom hiStr) .nil) hb₄ ⟨hn₃, .inl e₃⟩ fun _ h => by cases h)
    (.cons (.writeOk (t := mixList) hb₅ ⟨hn₄, .inl e₄⟩ fun _ h => by cases h)
    (.cons (.acceptOk (t := mixList) (Function.update_self _ _ _)) (.nil _))))))), by simp⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Cons
