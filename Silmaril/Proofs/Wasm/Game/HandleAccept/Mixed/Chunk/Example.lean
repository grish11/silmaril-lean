module

public import Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream.Stack
public import Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.Generic

/-!
# `chunkStack` meets its chunk specification

* `chunk_shape`: the instance has shape `MShape` (kernel evaluation); `chunkInv_init`: the
  instantiated store represents the empty buffer; `chunkInv_uniq`: a store represents at most
  one buffer;
* `cprelude_hwp`: after the prelude the flag is set and the handle denotes the reversed buffer,
  the count unchanged;
* `chunkStack_sat`: in every environment `ρ` and every profile, assuming the writer answers agree
  with `ρ` (no writer sentinel), the instance meets
  `chunkSSpec chunkPix ppol ρ chunkR (chunkInv ρ)`:
  `feed(x)` moves the represented buffer from `g` to `g ++ [x]` (or diverges when `2³² - 1`
  values are buffered); `finish(n)` with `n` below the count returns `(0, h)`, `h` denoting `()`,
  keeping the buffer; otherwise it returns `(|g|, h)`, `h` denoting `g` reversed, and empties the
  buffer. Traps keep it.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.GameLink
  Silmaril.Formats Silmaril.Formats.Api Silmaril.Accept.Handle Silmaril.Accept.Parse
  Silmaril.Accept.Mixed Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Writers Silmaril.Wasm.Game.HandleAccept.Writers.Builders
  Silmaril.Wasm.Game.HandleAccept.Parsing Silmaril.Wasm.Game.HandleAccept.Mixed.Stream
  Silmaril.Wasm.Game.HandleAccept.Mixed.Stream.Stack Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk
  Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers
  Silmaril.Proofs.Wasm.Game.HandleAccept.Parsing.Checkers
  Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.TwoWords
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream.Stack
open Silmaril.Wasm.Logic.Strategy (ISpec)
open Silmaril.Wasm.Logic.Core (Outcome Post)

/-- The export types. -/
abbrev chunkFTs : List FnType :=
  [runFT, ⟨[.num (.int .i32)], [.num (.int .i32), .num (.int .i32)]⟩]

/-- The exported functions. -/
abbrev chunkFns : List (List ValType × List Instr × List (Option Val)) :=
  [([], feedBody, []), ([], finBody, [])]

theorem chunk_shape : MShape (Verify.instOf chunkStack) twoFTs chunkFTs chunkFns [0, 1, 2] :=
  MShape.of_ok (by decide +kernel)

theorem chunk_gval0 : gval (Verify.instOf chunkStack).store 0 = some (.i32 0) := by
  decide +kernel

theorem chunk_gval1 : gval (Verify.instOf chunkStack).store 1 = some (.i32 0) := by
  decide +kernel

theorem chunk_gval2 : gval (Verify.instOf chunkStack).store 2 = some (.i32 0) := by
  decide +kernel

theorem chunkInv_init (ρ : Env (BitVec 32) (SExp2 (BitVec 64))) :
    chunkInv ρ [] (Verify.instOf chunkStack).store :=
  ⟨rfl, 0, 0, 0, chunk_gval0, chunk_gval1, chunk_gval2, rfl, fun _ => rfl, fun h => absurd rfl h⟩

theorem chunkInv_uniq {ρ : Env (BitVec 32) (SExp2 (BitVec 64))} {g g' : List (BitVec 64)}
    {s : Store Nat} (h : chunkInv ρ g s) (h' : chunkInv ρ g' s) : g = g' := by
  obtain ⟨-, fl, acc, cnt, h0, h1, -, -, hz, hnz⟩ := h
  obtain ⟨-, fl', acc', cnt', h0', h1', -, -, hz', hnz'⟩ := h'
  rw [h0] at h0'
  rw [h1] at h1'
  obtain rfl : fl = fl' := by simp [Val.i32] at h0'; cases h0'; rfl
  obtain rfl : acc = acc' := by simp [Val.i32] at h1'; cases h1'; rfl
  by_cases hf : fl = 0
  · rw [hz hf, hz' hf]
  · have := (hnz hf).symm.trans (hnz' hf)
    simpa using SExp2.ofAtoms_injective (Option.some.inj this)

/-! ## The prelude -/

variable {P : Profile} {s : Store Nat} {f : Frame} {Q : Post Nat}
  {ρ : Env (BitVec 32) (SExp2 (BitVec 64))}

abbrev CI : ScalarInstance := Verify.instOf chunkStack

theorem cprelude_hwp {rest : List Instr} {g : List (BitVec 64)} {fl acc cnt : BitVec 32}
    (hs : s.funcs = CI.store.funcs) (hm : f.module.funcs = List.range (twoFTs.length + 2))
    (hg : f.module.globals = [0, 1, 2]) (hrep : ChunkRep ρ g s fl acc cnt)
    (hT : ∀ s', chunkInv ρ g s' → Traps Q s')
    (hk : ∀ s' fl' acc', s'.funcs = s.funcs → ChunkRep ρ g s' fl' acc' cnt → fl' ≠ 0 →
      HWP P (gameHost CI (WSpec CI ρ Set.univ)) s' f (vals [] ++ expression rest) Q) :
    HWP P (gameHost CI (WSpec CI ρ Set.univ)) s f (vals [] ++ expression (prelude ++ rest)) Q := by
  obtain ⟨h0, h1, h2, hl, hz, hnz⟩ := hrep
  simp only [prelude, List.cons_append, List.nil_append]
  refine X.globalGet (us := []) (x := ⟨0⟩) (a := 0) (by rw [hg]; rfl) h0 ?_
  refine X.eqz (us := []) ?_
  refine X.if_ (us := []) (fun hc => ?_) (fun hc => ?_)
  · have hf : fl = 0 := by simpa using bool32_ne_zero hc
    have hg0 := hz hf
    refine X.wNilM (us := []) chunk_shape hs hm
      (Traps.label (hT s ⟨hs, fl, acc, cnt, h0, h1, h2, hl, hz, hnz⟩)) fun n hn => ?_
    refine X.globalSet (us := []) (x := ⟨1⟩) (a := 1) (by rw [hg]; rfl) (by simp [h1]) ?_
    refine X.i32Const (us := []) ?_
    refine X.globalSet (us := []) (x := ⟨0⟩) (a := 0) (by rw [hg]; rfl)
      (by simp [gval_setGlobal, h0]) ?_
    refine X.blockEnd (us := []) (hk _ 1 n rfl ⟨?_, ?_, ?_, hl, fun h => absurd h (by decide), ?_⟩
      (by decide))
    · simp [gval_setGlobal, h0]; rfl
    · simp [gval_setGlobal, h1]
    · simp [gval_setGlobal, h2]
    · intro _
      rw [hg0]
      exact hn
  · have hf : fl ≠ 0 := by simpa using bool32_eq_zero hc
    exact hk s fl acc rfl ⟨h0, h1, h2, hl, hz, hnz⟩ hf

/-! ## Decoding the answers -/

theorem dec_feed {ts : List FnType} {e : (ifaceSig ts).Op} {v : (ifaceSig ts).Ar e}
    {x : BitVec 64} (he : e.1.val = 0) (hx : e.2.1 = [.i64 x]) (hv : ansVals v = some []) :
    parseDec chunkPix e v = some (.feed [x]) := by
  simp [parseDec, chunkPix, hv, he, hx, i64Val, Writers.i64Arg, Val.i64]

theorem dec_finish {ts : List FnType} {e : (ifaceSig ts).Op} {v : (ifaceSig ts).Ar e}
    {u h : BitVec 32} (he : e.1.val = 1) (hv : ansVals v = some [.i32 u, .i32 h]) :
    parseDec chunkPix e v = some (.finish u.toNat h) := by
  simp [parseDec, chunkPix, hv, he, i32Two, Val.i32]

theorem cnt_succ {cnt : BitVec 32} (hne : cnt ≠ BitVec.allOnes 32) :
    (cnt + 1).toNat = cnt.toNat + 1 := by
  have h1 := cnt.isLt
  have h2 : cnt.toNat ≠ 2 ^ 32 - 1 := fun h =>
    hne (BitVec.eq_of_toNat_eq (by rw [h, BitVec.toNat_allOnes]))
  rw [BitVec.toNat_add]
  exact Nat.mod_eq_of_lt (by simp; omega)

/-! ## The module -/

/-- **`chunkStack` meets its chunk specification** in every environment and every profile. -/
theorem chunkStack_sat (P : Profile) (ρ : Env (BitVec 32) (SExp2 (BitVec 64)))
    (ppol : PPolicy (BitVec 32)) :
    SGameSat P CI (WSpec CI ρ Set.univ) (chunkSSpec chunkPix ppol ρ chunkR (chunkInv ρ)) := by
  have hS := chunk_shape
  refine sgameSat_ofM hS (fun g s h => h.1) (fun g g' s h h' => chunkInv_uniq h h')
    (fun g e v hv => ⟨fun e' hd => by simp [parseDec, hv] at hd, by
      simp [chunkSSpec, chunkNext, parseDec, hv]⟩)
    fun j fi s args ht g Q hfi hm hmg hinv hT hret => ?_
  obtain ⟨hfs, fl, acc, cnt, hrep⟩ := hinv
  have hlen : CI.exports.length = 2 := by rw [hS.exports]; rfl
  have hgj := hS.get j
  obtain ⟨j, hj⟩ := j
  have hj2 : j < 2 := hlen ▸ hj
  match j, hj2 with
  | 0, _ =>
    -- `feed(x)`
    have ht' := ht
    rw [hgj] at ht'
    obtain ⟨x, rfl⟩ : ∃ x, args = [.i64 x] := by
      rcases ht' with _ | ⟨⟨x, rfl⟩, hnil⟩
      cases hnil
      exact ⟨x, rfl⟩
    obtain ⟨h0, h1, h2, hl, hz, hnz⟩ := hrep
    show HWP P _ s ⟨[some (.i64 x)], fi.module⟩
      (vals [] ++ expression (cntGuard ++ prelude ++ _)) Q
    simp only [cntGuard, List.cons_append, List.nil_append]
    refine X.globalGet (us := []) (x := ⟨2⟩) (a := 2) (by rw [hmg]; rfl) h2 ?_
    refine X.i32Const (us := [] ++ [.i32 cnt]) ?_
    refine X.rel32 (us := []) ?_
    refine X.if_ (us := []) (fun _ => ?_) (fun hc => ?_)
    · refine X.loop (Inv := fun _ _ => True) (fun _ _ _ => ?_) trivial
      exact HWP.of_exits (o := .br 0 []) ⟨⟨0⟩, [], rfl, rfl⟩ ⟨[], [], rfl, rfl, rfl, trivial⟩
    · have hne : cnt ≠ BitVec.allOnes 32 := by
        rintro rfl
        simp [Numerics.intRelOp] at hc
        exact absurd hc (by decide)
      refine cprelude_hwp hfs hm hmg ⟨h0, h1, h2, hl, hz, hnz⟩ hT
        fun s₁ fl₁ acc₁ hs₁ hrep₁ hfl₁ => ?_
      have hT₁ := hT s₁ ⟨hs₁.trans hfs, fl₁, acc₁, cnt, hrep₁⟩
      obtain ⟨h0', h1', h2', -, -, hnz'⟩ := hrep₁
      refine X.localGet (x := ⟨0⟩) (v := .i64 x) rfl ?_
      refine X.wWordM (us := []) hS (hs₁.trans hfs) hm hT₁ fun a ha => ?_
      refine X.globalGet (us := [.i32 a]) (x := ⟨1⟩) (a := 1) (by rw [hmg]; rfl) h1' ?_
      refine X.wConsM (us := []) hS (hs₁.trans hfs) hm ha (hnz' hfl₁) hT₁ fun c hcons => ?_
      refine X.globalSet (us := []) (x := ⟨1⟩) (a := 1) (by rw [hmg]; rfl) (by simp [h1']) ?_
      refine X.globalGet (us := []) (x := ⟨2⟩) (a := 2) (v := .i32 cnt) (by rw [hmg]; rfl)
        (by simp [gval_setGlobal, h2']) ?_
      refine X.i32Const (us := [] ++ [.i32 cnt]) ?_
      refine X.add32 (us := []) ?_
      refine X.globalSet (us := []) (x := ⟨2⟩) (a := 2) (by rw [hmg]; rfl)
        (by simp [gval_setGlobal, h2']) ?_
      refine X.return_ (hret _ _ [] (by rw [hgj]; rfl) fun v hv => ⟨?_, ?_⟩)
      · intro e hd
        rw [dec_feed rfl rfl (ansVals_of hv)] at hd
        cases hd
        intro ps w h ps' _ hR
        exact hR.elim
      · have hn : chunkNext (I := CI) chunkPix g ⟨⟨0, hj⟩, ⟨[.i64 x], ht⟩⟩ v = g ++ [x] := by
          simp [chunkNext, dec_feed (ts := CI.exports) (e := ⟨⟨0, hj⟩, ⟨[.i64 x], ht⟩⟩) rfl rfl
            (ansVals_of hv), chunkStep]
        show chunkInv ρ (chunkNext (I := CI) chunkPix g ⟨⟨0, hj⟩, ⟨[.i64 x], ht⟩⟩ v) _
        rw [hn]
        refine ⟨hs₁.trans hfs, fl₁, c, cnt + 1, ?_, ?_, ?_, ?_, fun h => absurd h hfl₁, fun _ => ?_⟩
        · simp [gval_setGlobal, h0']
        · simp [gval_setGlobal, h1']
        · simp [gval_setGlobal, h2']; rfl
        · rw [cnt_succ hne, hl]; simp
        · rw [ofAtoms_snoc_reverse]
          exact hcons
  | 1, _ =>
    -- `finish(n)`
    have ht' := ht
    rw [hgj] at ht'
    obtain ⟨n, rfl⟩ : ∃ n, args = [.i32 n] := by
      rcases ht' with _ | ⟨⟨n, rfl⟩, hnil⟩
      cases hnil
      exact ⟨n, rfl⟩
    obtain ⟨h0, h1, h2, hl, hz, hnz⟩ := hrep
    show HWP P _ s ⟨[some (.i32 n)], fi.module⟩ (vals [] ++ expression (_ ++ prelude ++ _)) Q
    simp only [List.cons_append, List.nil_append]
    refine X.localGet (x := ⟨0⟩) (v := .i32 n) rfl ?_
    refine X.globalGet (us := [] ++ [.i32 n]) (f := ⟨[some (.i32 n)], fi.module⟩) (x := ⟨2⟩)
      (a := 2) (by rw [hmg]; rfl) h2 ?_
    refine X.rel32 (us := []) ?_
    refine X.if_ (us := []) (fun _ => ?_) (fun hc => ?_)
    · -- `n < count`: nothing is consumed
      refine X.i32Const (us := []) ?_
      refine X.wNilM (us := [.i32 0]) hS hfs hm
        (Traps.label (hT s ⟨hfs, fl, acc, cnt, h0, h1, h2, hl, hz, hnz⟩)) fun r hr => ?_
      refine X.return_ (hret _ _ [.i32 0, .i32 r] (by rw [hgj]; rfl) fun v hv => ⟨?_, ?_⟩)
      · intro e hd
        rw [dec_finish rfl (ansVals_of hv)] at hd
        cases hd
        intro ps w h ps' _ hR _ y hy
        obtain ⟨-, rfl, rfl, -⟩ := hR
        rw [hr] at hy
        cases hy
        simp [chunkR, SExp2.ofAtoms, SExp2.ofList]
      · have hn : chunkNext (I := CI) chunkPix g ⟨⟨1, hj⟩, ⟨[.i32 n], ht⟩⟩ v = g := by
          simp [chunkNext, dec_finish (ts := CI.exports) (e := ⟨⟨1, hj⟩, ⟨[.i32 n], ht⟩⟩) rfl
            (ansVals_of hv), chunkStep]
        show chunkInv ρ (chunkNext (I := CI) chunkPix g ⟨⟨1, hj⟩, ⟨[.i32 n], ht⟩⟩ v) _
        rw [hn]
        exact ⟨hfs, fl, acc, cnt, h0, h1, h2, hl, hz, hnz⟩
    · -- `n ≥ count`: every buffered value is consumed
      refine cprelude_hwp hfs hm hmg ⟨h0, h1, h2, hl, hz, hnz⟩ hT
        fun s₁ fl₁ acc₁ hs₁ hrep₁ hfl₁ => ?_
      obtain ⟨h0', h1', h2', hl', -, hnz'⟩ := hrep₁
      refine X.globalGet (us := []) (f := ⟨[some (.i32 n)], fi.module⟩) (x := ⟨2⟩) (a := 2)
        (by rw [hmg]; rfl) h2' ?_
      refine X.globalGet (us := [] ++ [.i32 cnt]) (f := ⟨[some (.i32 n)], fi.module⟩) (x := ⟨1⟩)
        (a := 1) (by rw [hmg]; rfl) h1' ?_
      refine X.i32Const (us := [] ++ [.i32 cnt] ++ [.i32 acc₁]) ?_
      refine X.globalSet (us := [] ++ [.i32 cnt] ++ [.i32 acc₁]) (s := s₁)
        (f := ⟨[some (.i32 n)], fi.module⟩) (x := ⟨0⟩) (a := 0) (by rw [hmg]; rfl)
        (by simp [h0']) ?_
      refine X.i32Const (us := [] ++ [.i32 cnt] ++ [.i32 acc₁]) ?_
      refine X.globalSet (us := [] ++ [.i32 cnt] ++ [.i32 acc₁]) (s := s₁.setGlobal 0 (.i32 0))
        (f := ⟨[some (.i32 n)], fi.module⟩) (x := ⟨2⟩) (a := 2) (by rw [hmg]; rfl)
        (by simp [gval_setGlobal, h2']) ?_
      refine X.return_ (hret _ _ [.i32 cnt, .i32 acc₁] (by rw [hgj]; rfl) fun v hv => ⟨?_, ?_⟩)
      · intro e hd
        rw [dec_finish rfl (ansVals_of hv)] at hd
        cases hd
        intro ps w h ps' hps hR _ y hy
        obtain ⟨-, rfl, rfl, -⟩ := hR
        rw [hnz' hfl₁] at hy
        cases hy
        show SExp2.ofAtoms g.reverse = SExp2.ofAtoms (ps.buf.take cnt.toNat).reverse
        rw [hps, hl', List.take_length]
      · have hn : chunkNext (I := CI) chunkPix g ⟨⟨1, hj⟩, ⟨[.i32 n], ht⟩⟩ v = [] := by
          simp [chunkNext, dec_finish (ts := CI.exports) (e := ⟨⟨1, hj⟩, ⟨[.i32 n], ht⟩⟩) rfl
            (ansVals_of hv), chunkStep, hl']
        show chunkInv ρ (chunkNext (I := CI) chunkPix g ⟨⟨1, hj⟩, ⟨[.i32 n], ht⟩⟩ v) _
        rw [hn]
        refine ⟨hs₁.trans hfs, 0, acc₁, 0, ?_, ?_, ?_, rfl, fun _ => rfl, fun h => absurd rfl h⟩
        · simp [gval_setGlobal, h0']
        · simp [gval_setGlobal, h1']
        · simp [gval_setGlobal, h2']; rfl

end Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk
