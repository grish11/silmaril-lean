module

public import Silmaril.Wasm.Game.HandleAccept.Mixed.Parser.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.Parse.OneShot
public import Silmaril.Proofs.Wasm.Game.HandleAccept.Writer.TwoWords

/-!
# `listParse` meets its mixed specification

* `X.wWordT`, `X.wNilT`, `X.wConsT`: the cons writer call rules of
  `Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.TwoWords` for a postcondition that only
  accepts traps and exceptions (through `X.callT`), for any export type;
* `listParse_sat`: in every environment `ρ` and every profile, the instance of `listParse`
  meets the import specification "writer answers agree with `ρ`" (no writer sentinel) and the
  export specification `parseESpec listPix 0 ρ listR`: straight-line code, the returned handle
  denotes in `ρ` the tree `cons (atom x) nil` built from the trees of its arguments.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Parser

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.GameLink
  Silmaril.Formats Silmaril.Formats.Api Silmaril.Accept.Handle Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Writers Silmaril.Wasm.Game.HandleAccept.Writers.Builders
  Silmaril.Wasm.Game.HandleAccept.Parsing Silmaril.Wasm.Game.HandleAccept.Mixed.Parser
  Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers
  Silmaril.Proofs.Wasm.Game.HandleAccept.Parsing.Checkers
  Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.TwoWords
open Silmaril.Wasm.Logic.Strategy (ISpec)
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {P : Profile} {s : Store Nat} {f : Frame} {us : List Val} {is : List Instr}
  {Q : Post Nat}

/-! ## Writer calls under a trapping postcondition -/

section Calls

variable {I : ScalarInstance} {eft : FnType} {locals : List ValType} {body : List Instr}
  {D : List (Option Val)} (hS : GShape I twoFTs eft locals body D)
  (hs : s.funcs = I.store.funcs) (hm : f.module.funcs = List.range (twoFTs.length + 1))
  {ρ : Env (BitVec 32) (SExp2 (BitVec 64))} {L : Set (SExp2 (BitVec 64))}

include hS hs hm

/-- `word(x)`. -/
theorem X.wWordT {x : BitVec 64} (hQ : Traps Q s)
    (hc : ∀ r, ρ r = some (.atom x) →
      HWP P (gameHost I (WSpec I ρ L)) s f (vals (us ++ [.i32 r]) ++ expression is) Q) :
    HWP P (gameHost I (WSpec I ρ L)) s f
      (vals (us ++ [.i64 x]) ++ expression (.call ⟨2⟩ :: is)) Q :=
  X.callT hS hs hm (k := 2) (by decide) rfl rfl
    (w_pre_of_ne hS.imports (by decide) (by decide) (.cons ⟨x, rfl⟩ .nil))
    (fun _ _ he hv res hr => by
      obtain ⟨r, rfl, h⟩ := wWord_post hS.imports he hv hr
      exact hc r h) hQ

/-- `nil()`. -/
theorem X.wNilT (hQ : Traps Q s)
    (hc : ∀ r, ρ r = some .nil →
      HWP P (gameHost I (WSpec I ρ L)) s f (vals (us ++ [.i32 r]) ++ expression is) Q) :
    HWP P (gameHost I (WSpec I ρ L)) s f (vals us ++ expression (.call ⟨0⟩ :: is)) Q := by
  have h := X.callT (us := us) (args := []) (x := ⟨0⟩) hS hs hm (k := 0) (by decide) rfl rfl
    (w_pre_of_ne hS.imports (by decide) (by decide) .nil)
    (fun _ _ he hv res hr => by
      obtain ⟨r, rfl, h⟩ := wNil_post hS.imports he hv hr
      exact hc r h) hQ
  simpa using h

/-- `cons(a, b)`. -/
theorem X.wConsT {a b : BitVec 32} {x y : SExp2 (BitVec 64)} (ha : ρ a = some x)
    (hb : ρ b = some y) (hQ : Traps Q s)
    (hc : ∀ r, ρ r = some (.cons x y) →
      HWP P (gameHost I (WSpec I ρ L)) s f (vals (us ++ [.i32 r]) ++ expression is) Q) :
    HWP P (gameHost I (WSpec I ρ L)) s f
      (vals (us ++ [.i32 a] ++ [.i32 b]) ++ expression (.call ⟨1⟩ :: is)) Q := by
  rw [List.append_assoc]
  exact X.callT hS hs hm (k := 1) (args := [.i32 a, .i32 b]) (by decide) rfl rfl
    (w_pre_of_ne hS.imports (by decide) (by decide) (.cons ⟨a, rfl⟩ (.cons ⟨b, rfl⟩ .nil)))
    (fun _ _ he hv res hr => by
      obtain ⟨r, rfl, h⟩ := wCons_post hS.imports ha hb he hv hr
      exact hc r h) hQ

end Calls

/-! ## The module -/

theorem list_shape : GShape (Verify.instOf listParse) twoFTs parseFT [] listBody [] :=
  GShape.of_ok (by decide +kernel)

/-- What a `parse` answer decodes to. -/
theorem parseDec_list {ts : List FnType} {e : (ifaceSig ts).Op} {v : (ifaceSig ts).Ar e}
    {w : BitVec 64} {h : BitVec 32} (hd : parseDec listPix e v = some (.parse w h)) :
    i64Val e.2.1 = some w ∧ ∃ vs, ansVals v = some vs ∧ i32Res vs = some h :=
  parseDec_nz hd

/-- **`listParse` meets its mixed specification** in every environment and every profile:
assuming writer answers agree with `ρ` (no writer sentinel), a non-sentinel handle returned by
`parse(x)` denotes in `ρ` a tree related to `x` by `listR`. -/
theorem listParse_sat (P : Profile) (ρ : Env (BitVec 32) (SExp2 (BitVec 64))) :
    GameSat P (Verify.instOf listParse) (StoreInv (Verify.instOf listParse))
      (WSpec (Verify.instOf listParse) ρ Set.univ) (parseESpec listPix 0 ρ listR) := by
  refine gameSat_ofE list_shape (fun j args ht v hv w h hd => ?_)
    fun fi s args j ht Q ht' _ hm hs hT hret => ?_
  · obtain ⟨-, vs, hvs, -⟩ := parseDec_list hd
    rw [hv] at hvs
    cases hvs
  obtain ⟨x, rfl⟩ : ∃ x, args = [.i64 x] := by
    rcases ht' with _ | ⟨⟨x, rfl⟩, hnil⟩
    cases hnil
    exact ⟨x, rfl⟩
  have hS := list_shape
  simp only [listBody]
  refine X.localGet (v := .i64 x) rfl ?_
  refine Wp.intTestOp (m := .part) (t := .i64) (x := x) (us := []) ?_
  refine X.if_ (fun h0 => ?_) (fun h0 => ?_)
  · -- `parse(0)`: the sentinel
    refine X.i32Const ?_
    refine X.return_ (hret _ [.i32 0] rfl fun v hv w h hd hh => ?_)
    obtain ⟨-, vs, hvs, hr⟩ := parseDec_list hd
    have : vs = [.i32 0] := by
      cases v <;> simp_all [Answer.toResult, ansVals]
    subst this
    simp [i32Res, Val.i32] at hr
    exact absurd hr.symm hh
  · -- `parse(x)`, `x ≠ 0`: `cons(word(x), nil())`
    have hx := eqz64_eq h0
    refine X.localGet (v := .i64 x) rfl ?_
    refine X.wWordT (us := []) hS hs hm hT (fun a ha => ?_)
    refine X.wNilT hS hs hm hT (fun n hn => ?_)
    refine X.wConsT (us := []) hS hs hm ha hn hT (fun c hc => ?_)
    refine X.return_ (hret _ [.i32 c] rfl fun v hv w h hd hh y hy => ?_)
    obtain ⟨hw, vs, hvs, hr⟩ := parseDec_list hd
    have : vs = [.i32 c] := by
      cases v <;> simp_all [Answer.toResult, ansVals]
    subst this
    simp [i32Res, Val.i32] at hr
    subst hr
    simp [i64Val, Writers.i64Arg, Val.i64] at hw
    subst hw
    rw [hc] at hy
    cases hy
    exact ⟨x, hx, rfl⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Parser
