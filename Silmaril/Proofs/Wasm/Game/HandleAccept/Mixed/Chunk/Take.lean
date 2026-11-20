module

public import Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Take.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.Example

/-!
# `chunkTake` meets its chunk specification

* `take_shape`: the instance has shape `MShape` (kernel evaluation); `takeInv_init`: the
  instantiated store represents the empty buffer; `takeInv_uniq`: a store represents at most one
  buffer;
* `chunkTake_sat`: in every environment `ρ` and every profile, assuming the writer answers agree
  with `ρ` (no writer sentinel), the instance meets `chunkSSpec takePix ppol ρ takeR takeInv`:
  `feed(x)` moves the represented buffer from `g` to `g ++ [x]` (or diverges with two values
  buffered); `finish(n)` with `n = 0` or `n` above the count returns `(0, h)`, `h` denoting `()`,
  keeping the buffer; otherwise it returns `(n, h)`, `h` denoting the list of the first `n`
  buffered values, and drops them from the buffer. Traps keep it.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.Take

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.GameLink
  Silmaril.Formats Silmaril.Formats.Api Silmaril.Accept.Handle Silmaril.Accept.Parse
  Silmaril.Accept.Mixed Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Writers Silmaril.Wasm.Game.HandleAccept.Writers.Builders
  Silmaril.Wasm.Game.HandleAccept.Parsing Silmaril.Wasm.Game.HandleAccept.Mixed.Stream
  Silmaril.Wasm.Game.HandleAccept.Mixed.Stream.Stack Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk
  Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Take
  Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers
  Silmaril.Proofs.Wasm.Game.HandleAccept.Parsing.Checkers
  Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.TwoWords
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream.Stack
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk
open Silmaril.Wasm.Logic.Strategy (ISpec)
open Silmaril.Wasm.Logic.Core (Outcome Post)

/-- The exported functions. -/
abbrev takeFns : List (List ValType × List Instr × List (Option Val)) :=
  [([], takeFeedBody, []), ([], takeFinBody, [])]

theorem take_shape : MShape (Verify.instOf chunkTake) twoFTs chunkFTs takeFns [0, 1, 2] :=
  MShape.of_ok (by decide +kernel)

theorem take_gval0 : gval (Verify.instOf chunkTake).store 0 = some (.i64 0) := by
  decide +kernel

theorem take_gval1 : gval (Verify.instOf chunkTake).store 1 = some (.i64 0) := by
  decide +kernel

theorem take_gval2 : gval (Verify.instOf chunkTake).store 2 = some (.i32 0) := by
  decide +kernel

theorem takeInv_init : takeInv [] (Verify.instOf chunkTake).store :=
  ⟨rfl, 0, 0, 0, take_gval0, take_gval1, take_gval2, by decide, rfl⟩

theorem takeInv_uniq {g g' : List (BitVec 64)} {s : Store Nat} (h : takeInv g s)
    (h' : takeInv g' s) : g = g' := by
  obtain ⟨-, v₀, v₁, cnt, h0, h1, h2, -, rfl⟩ := h
  obtain ⟨-, v₀', v₁', cnt', h0', h1', h2', -, rfl⟩ := h'
  rw [h0] at h0'
  rw [h1] at h1'
  rw [h2] at h2'
  simp [Val.i32, Val.i64] at h0' h1' h2'
  cases h0'
  cases h1'
  cases h2'
  rfl

/-! ## Small facts -/

theorem rel_eq_ne {x y : BitVec 32} (h : Numerics.intRelOp .i32 .eq x y ≠ 0) : x = y := by
  have := bool32_ne_zero (b := x == y) h
  simpa using this

theorem rel_eq_z {x y : BitVec 32} (h : Numerics.intRelOp .i32 .eq x y = 0) : x ≠ y := by
  have := bool32_eq_zero (b := x == y) h
  simpa using this

theorem rel_gtu_z {x y : BitVec 32} (h : Numerics.intRelOp .i32 (.gt .unsigned) x y = 0) :
    x.toNat ≤ y.toNat := by
  have := bool32_eq_zero (b := decide (x.toNat > y.toNat)) h
  simpa using this

theorem eqz_z {x : BitVec 32} (h : bool32 (x == 0) = 0) : x ≠ 0 := by
  have := bool32_eq_zero h
  simpa using this

theorem cnt_cases {c : BitVec 32} (h : c.toNat ≤ 2) : c = 0 ∨ c = 1 ∨ c = 2 := by bv_omega

theorem two_cases {n c : BitVec 32} (h0 : n ≠ 0) (h1 : n ≠ 1) (h : n.toNat ≤ c.toNat)
    (hc : c.toNat ≤ 2) : n = 2 ∧ c = 2 := by bv_omega

theorem tdec_feed {ts : List FnType} {e : (ifaceSig ts).Op} {v : (ifaceSig ts).Ar e}
    {x : BitVec 64} (he : e.1.val = 0) (hx : e.2.1 = [.i64 x]) (hv : ansVals v = some []) :
    parseDec takePix e v = some (.feed [x]) := by
  simp [parseDec, takePix, hv, he, hx, i64Val, Writers.i64Arg, Val.i64]

theorem tdec_finish {ts : List FnType} {e : (ifaceSig ts).Op} {v : (ifaceSig ts).Ar e}
    {u h : BitVec 32} (he : e.1.val = 1) (hv : ansVals v = some [.i32 u, .i32 h]) :
    parseDec takePix e v = some (.finish u.toNat h) := by
  simp [parseDec, takePix, hv, he, i32Two, Val.i32]

/-! ## The module -/

abbrev TI : ScalarInstance := Verify.instOf chunkTake

/-- **`chunkTake` meets its chunk specification** in every environment and every profile. -/
theorem chunkTake_sat (P : Profile) (ρ : Env (BitVec 32) (SExp2 (BitVec 64)))
    (ppol : PPolicy (BitVec 32)) :
    SGameSat P TI (WSpec TI ρ Set.univ) (chunkSSpec takePix ppol ρ takeR takeInv) := by
  have hS := take_shape
  refine sgameSat_ofM hS (fun g s h => h.1) (fun g g' s h h' => takeInv_uniq h h')
    (fun g e v hv => ⟨fun e' hd => by simp [parseDec, hv] at hd, by
      simp [chunkSSpec, chunkNext, parseDec, hv]⟩)
    fun j fi s args ht g Q hfi hm hmg hinv hT hret => ?_
  obtain ⟨hfs, v₀, v₁, cnt, hrep⟩ := hinv
  have hlen : TI.exports.length = 2 := by rw [hS.exports]; rfl
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
    obtain ⟨h0, h1, h2, hle, hg⟩ := hrep
    show HWP P _ s ⟨[some (.i64 x)], fi.module⟩ (vals [] ++ expression (capGuard ++ _)) Q
    simp only [capGuard, List.cons_append, List.nil_append]
    refine X.globalGet (us := []) (x := ⟨2⟩) (a := 2) (by rw [hmg]; rfl) h2 ?_
    refine X.i32Const (us := [] ++ [.i32 cnt]) ?_
    refine X.rel32 (us := []) ?_
    refine X.if_ (us := []) (fun _ => ?_) (fun hc => ?_)
    · refine X.loop (Inv := fun _ _ => True) (fun _ _ _ => ?_) trivial
      exact HWP.of_exits (o := .br 0 []) ⟨⟨0⟩, [], rfl, rfl⟩ ⟨[], [], rfl, rfl, rfl, trivial⟩
    · have hc2 := rel_eq_z hc
      have hn : ∀ v : Answer (TI.exports.get ⟨0, hj⟩), v.toResult = .values [] →
          chunkNext (I := TI) takePix g ⟨⟨0, hj⟩, ⟨[.i64 x], ht⟩⟩ v = g ++ [x] := fun v hv => by
        simp [chunkNext, tdec_feed (ts := TI.exports) (e := ⟨⟨0, hj⟩, ⟨[.i64 x], ht⟩⟩) rfl rfl
          (ansVals_of hv), chunkStep]
      have hpost : ∀ v : Answer (TI.exports.get ⟨0, hj⟩), v.toResult = .values [] →
          (chunkSSpec (I := TI) takePix ppol ρ takeR takeInv).post g
            ⟨⟨0, hj⟩, ⟨[.i64 x], ht⟩⟩ v := fun v hv e hd => by
        rw [tdec_feed rfl rfl (ansVals_of hv)] at hd
        cases hd
        intro ps w h ps' _ hR
        exact hR.elim
      rcases cnt_cases hle with rfl | rfl | rfl
      · -- one free slot more: slot `0`
        refine X.globalGet (us := []) (x := ⟨2⟩) (a := 2) (by rw [hmg]; rfl) h2 ?_
        refine X.eqz (us := []) ?_
        refine X.if_ (us := []) (fun _ => ?_) (fun hc => absurd hc (by decide))
        refine X.localGet (x := ⟨0⟩) (v := .i64 x) rfl ?_
        refine X.globalSet (us := []) (x := ⟨0⟩) (a := 0) (by rw [hmg]; rfl) (by simp [h0]) ?_
        refine X.blockEnd (us := []) ?_
        refine X.globalGet (us := []) (x := ⟨2⟩) (a := 2) (v := .i32 0) (by rw [hmg]; rfl)
          (by simp [gval_setGlobal, h2]) ?_
        refine X.i32Const (us := [] ++ [.i32 0]) ?_
        refine X.rel32 (us := []) ?_
        refine X.if_ (us := []) (fun hc => absurd hc (by decide)) (fun _ => ?_)
        refine X.globalGet (us := []) (x := ⟨2⟩) (a := 2) (v := .i32 0) (by rw [hmg]; rfl)
          (by simp [gval_setGlobal, h2]) ?_
        refine X.i32Const (us := [] ++ [.i32 0]) ?_
        refine X.add32 (us := []) ?_
        refine X.globalSet (us := []) (x := ⟨2⟩) (a := 2) (by rw [hmg]; rfl)
          (by simp [gval_setGlobal, h2]) ?_
        refine X.return_ (hret _ _ [] (by rw [hgj]; rfl) fun v hv => ⟨hpost v hv, ?_⟩)
        show takeInv (chunkNext (I := TI) takePix g ⟨⟨0, hj⟩, ⟨[.i64 x], ht⟩⟩ v) _
        rw [hn v hv]
        refine ⟨hfs, x, v₁, 1, ?_, ?_, ?_, by decide, ?_⟩
        · simp [gval_setGlobal, h0]
        · simp [gval_setGlobal, h1]
        · simp [gval_setGlobal, h2]; rfl
        · subst hg; rfl
      · -- slot `1`
        refine X.globalGet (us := []) (x := ⟨2⟩) (a := 2) (by rw [hmg]; rfl) h2 ?_
        refine X.eqz (us := []) ?_
        refine X.if_ (us := []) (fun hc => absurd hc (by decide)) (fun _ => ?_)
        refine X.globalGet (us := []) (x := ⟨2⟩) (a := 2) (by rw [hmg]; rfl) h2 ?_
        refine X.i32Const (us := [] ++ [.i32 1]) ?_
        refine X.rel32 (us := []) ?_
        refine X.if_ (us := []) (fun _ => ?_) (fun hc => absurd hc (by decide))
        refine X.localGet (x := ⟨0⟩) (v := .i64 x) rfl ?_
        refine X.globalSet (us := []) (x := ⟨1⟩) (a := 1) (by rw [hmg]; rfl) (by simp [h1]) ?_
        refine X.blockEnd (us := []) ?_
        refine X.globalGet (us := []) (x := ⟨2⟩) (a := 2) (v := .i32 1) (by rw [hmg]; rfl)
          (by simp [gval_setGlobal, h2]) ?_
        refine X.i32Const (us := [] ++ [.i32 1]) ?_
        refine X.add32 (us := []) ?_
        refine X.globalSet (us := []) (x := ⟨2⟩) (a := 2) (by rw [hmg]; rfl)
          (by simp [gval_setGlobal, h2]) ?_
        refine X.return_ (hret _ _ [] (by rw [hgj]; rfl) fun v hv => ⟨hpost v hv, ?_⟩)
        show takeInv (chunkNext (I := TI) takePix g ⟨⟨0, hj⟩, ⟨[.i64 x], ht⟩⟩ v) _
        rw [hn v hv]
        refine ⟨hfs, v₀, x, 2, ?_, ?_, ?_, by decide, ?_⟩
        · simp [gval_setGlobal, h0]
        · simp [gval_setGlobal, h1]
        · simp [gval_setGlobal, h2]; rfl
        · subst hg; rfl
      · exact absurd rfl hc2
  | 1, _ =>
    -- `finish(n)`
    have ht' := ht
    rw [hgj] at ht'
    obtain ⟨n, rfl⟩ : ∃ n, args = [.i32 n] := by
      rcases ht' with _ | ⟨⟨n, rfl⟩, hnil⟩
      cases hnil
      exact ⟨n, rfl⟩
    have hinv : takeInv g s := ⟨hfs, v₀, v₁, cnt, hrep⟩
    have hT₀ := hT s hinv
    obtain ⟨h0, h1, h2, hle, hg⟩ := hrep
    -- the returns of `finish(n)`, by their answer
    have hpost : ∀ (u r : BitVec 32) (y : SExp2 (BitVec 64)), ρ r = some y →
        (u.toNat ≤ g.length → y = SExp2.ofAtoms (g.take u.toNat)) →
        ∀ v : Answer (TI.exports.get ⟨1, hj⟩), v.toResult = .values [.i32 u, .i32 r] →
        (chunkSSpec (I := TI) takePix ppol ρ takeR takeInv).post g
          ⟨⟨1, hj⟩, ⟨[.i32 n], ht⟩⟩ v := fun u r y hy hu v hv e hd => by
      rw [tdec_finish rfl (ansVals_of hv)] at hd
      cases hd
      intro ps w h ps' hps hR _ y' hy'
      obtain ⟨hl, rfl, rfl, -⟩ := hR
      rw [hy] at hy'
      cases hy'
      rw [hps] at hl ⊢
      exact hu hl
    have hnext : ∀ (u r : BitVec 32) (v : Answer (TI.exports.get ⟨1, hj⟩)),
        v.toResult = .values [.i32 u, .i32 r] →
        chunkNext (I := TI) takePix g ⟨⟨1, hj⟩, ⟨[.i32 n], ht⟩⟩ v =
          chunkStep g (.finish u.toNat r) := fun u r v hv => by
      simp [chunkNext, tdec_finish (ts := TI.exports) (e := ⟨⟨1, hj⟩, ⟨[.i32 n], ht⟩⟩) rfl
        (ansVals_of hv)]
    show HWP P _ s ⟨[some (.i32 n)], fi.module⟩ (vals [] ++ expression takeFinBody) Q
    simp only [takeFinBody]
    refine X.localGet (x := ⟨0⟩) (v := .i32 n) rfl ?_
    refine X.globalGet (us := [] ++ [.i32 n]) (f := ⟨[some (.i32 n)], fi.module⟩) (x := ⟨2⟩)
      (a := 2) (by rw [hmg]; rfl) h2 ?_
    refine X.rel32 (us := []) ?_
    refine X.if_ (us := []) (fun _ => ?_) (fun hc => ?_)
    · -- `n > count`: nothing is consumed
      refine X.i32Const (us := []) ?_
      refine X.wNilM (us := [.i32 0]) hS hfs hm (Traps.label hT₀) fun r hr => ?_
      refine X.return_ (hret _ _ [.i32 0, .i32 r] (by rw [hgj]; rfl) fun v hv =>
        ⟨hpost 0 r _ hr (fun _ => by simp [SExp2.ofAtoms, SExp2.ofList]) v hv, ?_⟩)
      show takeInv (chunkNext (I := TI) takePix g ⟨⟨1, hj⟩, ⟨[.i32 n], ht⟩⟩ v) _
      rw [hnext 0 r v hv]
      simpa [chunkStep] using hinv
    · have hnc := rel_gtu_z hc
      refine X.localGet (x := ⟨0⟩) (v := .i32 n) rfl ?_
      refine X.eqz (us := []) ?_
      refine X.if_ (us := []) (fun _ => ?_) (fun hc₀ => ?_)
      · -- `n = 0`: nothing is consumed
        refine X.i32Const (us := []) ?_
        refine X.wNilM (us := [.i32 0]) hS hfs hm (Traps.label hT₀) fun r hr => ?_
        refine X.return_ (hret _ _ [.i32 0, .i32 r] (by rw [hgj]; rfl) fun v hv =>
          ⟨hpost 0 r _ hr (fun _ => by simp [SExp2.ofAtoms, SExp2.ofList]) v hv, ?_⟩)
        show takeInv (chunkNext (I := TI) takePix g ⟨⟨1, hj⟩, ⟨[.i32 n], ht⟩⟩ v) _
        rw [hnext 0 r v hv]
        simpa [chunkStep] using hinv
      · have hn0 := eqz_z hc₀
        refine X.localGet (x := ⟨0⟩) (v := .i32 n) rfl ?_
        refine X.i32Const (us := [] ++ [.i32 n]) ?_
        refine X.rel32 (us := []) ?_
        refine X.if_ (us := []) (fun hc₁ => ?_) (fun hc₁ => ?_)
        · -- `n = 1`: the oldest value is consumed
          have hn1 := rel_eq_ne hc₁
          rw [hn1] at hnc
          have hc12 : cnt = 1 ∨ cnt = 2 := by
            rcases cnt_cases hle with rfl | h | h
            · exact absurd hnc (by decide)
            · exact .inl h
            · exact .inr h
          let F : Frame := ⟨[some (.i32 n)], fi.module⟩
          let s₁ := s.setGlobal 0 (.i64 v₁)
          refine X.i32Const (us := []) ?_
          refine X.globalGet (f := F) (us := [] ++ [.i32 1]) (x := ⟨0⟩) (a := 0)
            (by rw [hmg]; rfl) h0 ?_
          refine X.wWordM (f := F) (us := [] ++ [.i32 1]) hS hfs hm (Traps.label hT₀)
            fun a ha => ?_
          refine X.wNilM (f := F) (us := [] ++ [.i32 1] ++ [.i32 a]) hS hfs hm
            (Traps.label hT₀) fun b hb => ?_
          refine X.wConsM (f := F) (us := [] ++ [.i32 1]) hS hfs hm ha hb (Traps.label hT₀)
            fun c hcc => ?_
          refine X.globalGet (f := F) (us := [] ++ [.i32 1] ++ [.i32 c]) (x := ⟨1⟩) (a := 1)
            (by rw [hmg]; rfl) h1 ?_
          refine X.globalSet (s := s) (f := F) (us := [] ++ [.i32 1] ++ [.i32 c]) (x := ⟨0⟩)
            (a := 0) (by rw [hmg]; rfl) (by simp [h0]) ?_
          refine X.globalGet (s := s₁) (f := F) (us := [] ++ [.i32 1] ++ [.i32 c]) (x := ⟨2⟩)
            (a := 2) (v := .i32 cnt) (by rw [hmg]; rfl) (by simp [s₁, gval_setGlobal, h2]) ?_
          refine X.i32Const (us := [] ++ [.i32 1] ++ [.i32 c] ++ [.i32 cnt]) ?_
          refine X.add32 (us := [] ++ [.i32 1] ++ [.i32 c]) ?_
          refine X.globalSet (s := s₁) (f := F) (us := [] ++ [.i32 1] ++ [.i32 c]) (x := ⟨2⟩)
            (a := 2) (by rw [hmg]; rfl) (by simp [s₁, gval_setGlobal, h2]) ?_
          refine X.return_ (hret _ _ [.i32 1, .i32 c] (by rw [hgj]; rfl) fun v hv =>
            ⟨hpost 1 c _ hcc (fun _ => by
              rcases hc12 with rfl | rfl <;> subst hg <;> simp [SExp2.ofAtoms, SExp2.ofList])
              v hv, ?_⟩)
          show takeInv (chunkNext (I := TI) takePix g ⟨⟨1, hj⟩, ⟨[.i32 n], ht⟩⟩ v) _
          rw [hnext 1 c v hv]
          rcases hc12 with rfl | rfl <;> subst hg
          · refine ⟨hfs, v₁, v₁, 0, ?_, ?_, ?_, by decide, by simp [chunkStep]⟩
            · simp [s₁, gval_setGlobal, h0]
            · simp [s₁, gval_setGlobal, h1]
            · simp [s₁, gval_setGlobal, h2]
          · refine ⟨hfs, v₁, v₁, 1, ?_, ?_, ?_, by decide, by simp [chunkStep]⟩
            · simp [s₁, gval_setGlobal, h0]
            · simp [s₁, gval_setGlobal, h1]
            · simp [s₁, gval_setGlobal, h2]
        · -- `n = 2 = count`: both values are consumed
          have hn1 := rel_eq_z hc₁
          obtain ⟨-, rfl⟩ := two_cases hn0 hn1 hnc hle
          subst hg
          let F : Frame := ⟨[some (.i32 n)], fi.module⟩
          refine X.i32Const (us := []) ?_
          refine X.globalGet (f := F) (us := [] ++ [.i32 2]) (x := ⟨0⟩) (a := 0)
            (by rw [hmg]; rfl) h0 ?_
          refine X.wWordM (f := F) (us := [] ++ [.i32 2]) hS hfs hm hT₀ fun a ha => ?_
          refine X.globalGet (f := F) (us := [] ++ [.i32 2] ++ [.i32 a]) (x := ⟨1⟩) (a := 1)
            (by rw [hmg]; rfl) h1 ?_
          refine X.wWordM (f := F) (us := [] ++ [.i32 2] ++ [.i32 a]) hS hfs hm hT₀
            fun b hb => ?_
          refine X.wNilM (f := F) (us := [] ++ [.i32 2] ++ [.i32 a] ++ [.i32 b]) hS hfs hm hT₀
            fun c hcc => ?_
          refine X.wConsM (f := F) (us := [] ++ [.i32 2] ++ [.i32 a]) hS hfs hm hb hcc hT₀
            fun d hd => ?_
          refine X.wConsM (f := F) (us := [] ++ [.i32 2]) hS hfs hm ha hd hT₀ fun t ht₂ => ?_
          refine X.i32Const (us := [] ++ [.i32 2] ++ [.i32 t]) ?_
          refine X.globalSet (s := s) (f := F) (us := [] ++ [.i32 2] ++ [.i32 t]) (x := ⟨2⟩)
            (a := 2) (by rw [hmg]; rfl) (by simp [h2]) ?_
          refine X.return_ (hret _ _ [.i32 2, .i32 t] (by rw [hgj]; rfl) fun v hv =>
            ⟨hpost 2 t _ ht₂ (fun _ => by simp [SExp2.ofAtoms, SExp2.ofList]) v hv, ?_⟩)
          show takeInv (chunkNext (I := TI) takePix _ ⟨⟨1, hj⟩, ⟨[.i32 n], ht⟩⟩ v) _
          rw [hnext 2 t v hv]
          refine ⟨hfs, v₀, v₁, 0, ?_, ?_, ?_, by decide, by simp [chunkStep]⟩
          · simp [gval_setGlobal, h0]
          · simp [gval_setGlobal, h1]
          · simp [gval_setGlobal, h2]; rfl

end Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.Take
