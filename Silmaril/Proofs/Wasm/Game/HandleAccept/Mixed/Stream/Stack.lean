module

public import Silmaril.Wasm.Game.HandleAccept.Mixed.Stream.Stack.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream.Shape

/-!
# `stackParse` meets its streaming specification

* `stack_shape`: the instance has shape `MShape` (kernel evaluation); `stackInv_init`: the
  instantiated store represents the empty buffer;
* `prelude_hwp`: after the prelude the flag is set and the handle denotes the reversed buffer;
* `stackParse_sat`: in every environment `ρ`, every profile and for every parsing policy whose
  `done` clears the buffer, assuming writer answers agree with `ρ` (no writer sentinel), the
  instance meets `streamSSpec stackPix ppol ρ stackR (stackInv ρ)`: `append(x)` moves the
  represented buffer from `g` to `g ++ [x]`, `done() -> h` returns a handle denoting the list of
  `g` reversed and moves it to `[]`; traps keep it.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream.Stack

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.GameLink
  Silmaril.Formats Silmaril.Formats.Api Silmaril.Accept.Handle Silmaril.Accept.Parse
  Silmaril.Accept.Mixed Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Writers Silmaril.Wasm.Game.HandleAccept.Writers.Builders
  Silmaril.Wasm.Game.HandleAccept.Parsing Silmaril.Wasm.Game.HandleAccept.Mixed.Stream
  Silmaril.Wasm.Game.HandleAccept.Mixed.Stream.Stack
  Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers
  Silmaril.Proofs.Wasm.Game.HandleAccept.Parsing.Checkers
  Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.TwoWords
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream
open Silmaril.Wasm.Logic.Strategy (ISpec)
open Silmaril.Wasm.Logic.Core (Outcome Post)

/-- The export types. -/
abbrev stackFTs : List FnType := [runFT, ⟨[], [.num (.int .i32)]⟩]

/-- The exported functions. -/
abbrev stackFns : List (List ValType × List Instr × List (Option Val)) :=
  [([], appendBody, []), ([], doneBody, [])]

theorem stack_shape : MShape (Verify.instOf stackParse) twoFTs stackFTs stackFns [0, 1] :=
  MShape.of_ok (by decide +kernel)

theorem stack_gval0 : gval (Verify.instOf stackParse).store 0 = some (.i32 0) := by
  decide +kernel

theorem stack_gval1 : gval (Verify.instOf stackParse).store 1 = some (.i32 0) := by
  decide +kernel

theorem stackInv_init (ρ : Env (BitVec 32) (SExp2 (BitVec 64))) :
    stackInv ρ [] (Verify.instOf stackParse).store :=
  ⟨rfl, 0, 0, stack_gval0, stack_gval1, fun _ => rfl, fun h => absurd rfl h⟩

theorem stackInv_uniq {ρ : Env (BitVec 32) (SExp2 (BitVec 64))} {g g' : List (BitVec 64)}
    {s : Store Nat} (h : stackInv ρ g s) (h' : stackInv ρ g' s) : g = g' := by
  obtain ⟨-, fl, acc, h0, h1, hz, hnz⟩ := h
  obtain ⟨-, fl', acc', h0', h1', hz', hnz'⟩ := h'
  rw [h0] at h0'
  rw [h1] at h1'
  obtain rfl : fl = fl' := by simp [Val.i32] at h0'; cases h0'; rfl
  obtain rfl : acc = acc' := by simp [Val.i32] at h1'; cases h1'; rfl
  by_cases hf : fl = 0
  · rw [hz hf, hz' hf]
  · have := (hnz hf).symm.trans (hnz' hf)
    simpa using SExp2.ofAtoms_injective (Option.some.inj this)

theorem ansVals_of {ft : FnType} {v : Answer ft} {res : List Val}
    (h : v.toResult = .values res) : ansVals v = some res := by
  cases v <;> simp_all [Answer.toResult, ansVals]

theorem ofAtoms_snoc_reverse (g : List (BitVec 64)) (x : BitVec 64) :
    SExp2.ofAtoms (g ++ [x]).reverse = .cons (.atom x) (SExp2.ofAtoms g.reverse) := by
  simp [SExp2.ofAtoms, SExp2.ofList]

/-! ## The prelude -/

variable {P : Profile} {s : Store Nat} {f : Frame} {Q : Post Nat}
  {ρ : Env (BitVec 32) (SExp2 (BitVec 64))}

abbrev SI : ScalarInstance := Verify.instOf stackParse

theorem prelude_hwp {rest : List Instr} {g : List (BitVec 64)} {fl acc : BitVec 32}
    (hs : s.funcs = SI.store.funcs) (hm : f.module.funcs = List.range (twoFTs.length + 2))
    (hg : f.module.globals = [0, 1]) (hrep : StackRep ρ g s fl acc)
    (hT : ∀ s', stackInv ρ g s' → Traps Q s')
    (hk : ∀ s' fl' acc', s'.funcs = s.funcs → StackRep ρ g s' fl' acc' → fl' ≠ 0 →
      HWP P (gameHost SI (WSpec SI ρ Set.univ)) s' f (vals [] ++ expression rest) Q) :
    HWP P (gameHost SI (WSpec SI ρ Set.univ)) s f (vals [] ++ expression (prelude ++ rest)) Q := by
  obtain ⟨h0, h1, hz, hnz⟩ := hrep
  simp only [prelude, List.cons_append, List.nil_append]
  refine X.globalGet (us := []) (x := ⟨0⟩) (a := 0) (by rw [hg]; rfl) h0 ?_
  refine X.eqz (us := []) ?_
  refine X.if_ (us := []) (fun hc => ?_) (fun hc => ?_)
  · have hf : fl = 0 := by simpa using bool32_ne_zero hc
    have hg0 := hz hf
    refine X.wNilM (us := []) stack_shape hs hm
      (Traps.label (hT s ⟨hs, fl, acc, h0, h1, hz, hnz⟩)) fun n hn => ?_
    refine X.globalSet (us := []) (x := ⟨1⟩) (a := 1) (by rw [hg]; rfl) (by simp [h1]) ?_
    refine X.i32Const (us := []) ?_
    refine X.globalSet (us := []) (x := ⟨0⟩) (a := 0) (by rw [hg]; rfl)
      (by simp [gval_setGlobal, h0]) ?_
    refine X.blockEnd (us := []) (hk _ 1 n rfl ⟨?_, ?_, fun h => absurd h (by decide), ?_⟩
      (by decide))
    · simp [gval_setGlobal, h0]; rfl
    · simp [gval_setGlobal, h1]
    · intro _
      rw [hg0]
      exact hn
  · have hf : fl ≠ 0 := by simpa using bool32_eq_zero hc
    exact hk s fl acc rfl ⟨h0, h1, hz, hnz⟩ hf

/-! ## Decoding the answers -/

theorem dec_append {ts : List FnType} {e : (ifaceSig ts).Op} {v : (ifaceSig ts).Ar e}
    {x : BitVec 64} (he : e.1.val = 0) (hx : e.2.1 = [.i64 x]) (hv : ansVals v = some []) :
    parseDec stackPix e v = some (.append x) := by
  simp [parseDec, stackPix, hv, he, hx, i64Val, Writers.i64Arg, Val.i64]

theorem dec_done {ts : List FnType} {e : (ifaceSig ts).Op} {v : (ifaceSig ts).Ar e}
    {h : BitVec 32} (he : e.1.val = 1) (hv : ansVals v = some [.i32 h]) :
    parseDec stackPix e v = some (.done h) := by
  simp [parseDec, stackPix, hv, he, i32Res, Val.i32]

/-! ## The module -/

/-- **`stackParse` meets its streaming specification** in every environment and every profile,
for parsing policies whose `done` clears the buffer. -/
theorem stackParse_sat (P : Profile) (ρ : Env (BitVec 32) (SExp2 (BitVec 64)))
    {ppol : PPolicy (BitVec 32)} (hc : ppol.doneClears = true) :
    SGameSat P SI (WSpec SI ρ Set.univ) (streamSSpec stackPix ppol ρ stackR (stackInv ρ)) := by
  have hS := stack_shape
  refine sgameSat_ofM hS (fun g s h => h.1) (fun g g' s h h' => stackInv_uniq h h')
    (fun g e v hv => ⟨fun e' hd => by simp [parseDec, hv] at hd, by
      simp [streamSSpec, streamNext, parseDec, hv]⟩)
    fun j fi s args ht g Q hfi hm hmg hinv hT hret => ?_
  obtain ⟨hfs, fl, acc, hrep⟩ := hinv
  have hlen : SI.exports.length = 2 := by rw [hS.exports]; rfl
  have hgj := hS.get j
  obtain ⟨j, hj⟩ := j
  have hj2 : j < 2 := hlen ▸ hj
  match j, hj2 with
  | 0, _ =>
    -- `append(x)`
    have ht' := ht
    rw [hgj] at ht'
    obtain ⟨x, rfl⟩ : ∃ x, args = [.i64 x] := by
      rcases ht' with _ | ⟨⟨x, rfl⟩, hnil⟩
      cases hnil
      exact ⟨x, rfl⟩
    show HWP P _ s _ (vals [] ++ expression (prelude ++ _)) Q
    refine prelude_hwp hfs hm hmg hrep hT fun s₁ fl₁ acc₁ hs₁ hrep₁ hfl₁ => ?_
    have hT₁ := hT s₁ ⟨hs₁.trans hfs, fl₁, acc₁, hrep₁⟩
    obtain ⟨h0, h1, -, hnz⟩ := hrep₁
    refine X.localGet (v := .i64 x) rfl ?_
    refine X.wWordM (us := []) hS (hs₁.trans hfs) hm hT₁ fun a ha => ?_
    refine X.globalGet (us := [.i32 a]) (x := ⟨1⟩) (a := 1) (by rw [hmg]; rfl) h1 ?_
    refine X.wConsM (us := []) hS (hs₁.trans hfs) hm ha (hnz hfl₁) hT₁ fun c hcons => ?_
    refine X.globalSet (us := []) (x := ⟨1⟩) (a := 1) (by rw [hmg]; rfl) (by simp [h1]) ?_
    refine X.return_ (hret _ _ [] (by rw [hgj]; rfl) fun v hv => ⟨?_, ?_⟩)
    · intro e hd
      rw [dec_append rfl rfl (ansVals_of hv)] at hd
      cases hd
      intro ps w h ps' _ hR
      exact hR.elim
    · have hn : streamNext (I := SI) stackPix ppol g ⟨⟨0, hj⟩, ⟨[.i64 x], ht⟩⟩ v = g ++ [x] := by
        simp [streamNext, dec_append (ts := SI.exports) (e := ⟨⟨0, hj⟩, ⟨[.i64 x], ht⟩⟩) rfl rfl (ansVals_of hv),
          accStep]
      show stackInv ρ (streamNext (I := SI) stackPix ppol g ⟨⟨0, hj⟩, ⟨[.i64 x], ht⟩⟩ v) _
      rw [hn]
      refine ⟨hs₁.trans hfs, fl₁, c, ?_, ?_, fun h => absurd h hfl₁, fun _ => ?_⟩
      · simp [gval_setGlobal, h0]
      · simp [gval_setGlobal, h1]
      · rw [ofAtoms_snoc_reverse]
        exact hcons
  | 1, _ =>
    -- `done()`
    have ht' := ht
    rw [hgj] at ht'
    obtain rfl : args = [] := by
      cases ht'
      rfl
    show HWP P _ s _ (vals [] ++ expression (prelude ++ _)) Q
    refine prelude_hwp hfs hm hmg hrep hT fun s₁ fl₁ acc₁ hs₁ hrep₁ hfl₁ => ?_
    obtain ⟨h0, h1, -, hnz⟩ := hrep₁
    refine X.globalGet (us := []) (x := ⟨1⟩) (a := 1) (by rw [hmg]; rfl) h1 ?_
    refine X.i32Const ?_
    refine X.globalSet (us := [.i32 acc₁]) (x := ⟨0⟩) (a := 0) (by rw [hmg]; rfl)
      (by simp [h0]) ?_
    refine X.return_ (hret _ _ [.i32 acc₁] (by rw [hgj]; rfl) fun v hv => ⟨?_, ?_⟩)
    · intro e hd
      rw [dec_done rfl (ansVals_of hv)] at hd
      cases hd
      intro ps w h ps' hps hR hh y hy
      obtain ⟨rfl, rfl, -⟩ := hR
      rw [hnz hfl₁] at hy
      cases hy
      show SExp2.ofAtoms g.reverse = SExp2.ofAtoms ps.acc.reverse
      rw [hps]
    · have hn : streamNext (I := SI) stackPix ppol g ⟨⟨1, hj⟩, ⟨[], ht⟩⟩ v = [] := by
        simp [streamNext, dec_done (ts := SI.exports) (e := ⟨⟨1, hj⟩, ⟨[], ht⟩⟩) rfl (ansVals_of hv), accStep, hc]
      show stackInv ρ (streamNext (I := SI) stackPix ppol g ⟨⟨1, hj⟩, ⟨[], ht⟩⟩ v) _
      rw [hn]
      refine ⟨hs₁.trans hfs, 0, acc₁, ?_, ?_, fun _ => rfl, fun h => absurd rfl h⟩
      · simp [gval_setGlobal, h0]; rfl
      · simp [gval_setGlobal, h1]

end Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream.Stack
