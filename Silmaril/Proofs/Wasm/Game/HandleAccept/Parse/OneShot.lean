module

public import Silmaril.Wasm.Game.HandleAccept.Parse.Checkers.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.Generic

/-!
# `nzParse` meets its parse specification

* `hwp_importT`, `X.callT`: the import call rule when the postcondition only accepts traps and
  exceptions (a function with results cannot accept every `return`, unlike `Leaves`);
* `gameSat_ofE`: the body-to-`GameSat` step for a nontrivial export specification: the body
  must return results whose answers satisfy it;
* `nzParse_sat`: the instance of `nzParse` meets `parseESpec nzIx 0 ρ (nzR X)` in every
  environment `ρ` and every profile.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Parsing.Checkers

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.GameLink
  Silmaril.Wasm.Game.HandleAccept Silmaril.Wasm.Game.HandleAccept.Parsing
  Silmaril.Wasm.Game.HandleAccept.Parsing.Checkers
  Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers
open Silmaril.Wasm.Logic.Strategy (ISpec resultOutcome)
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {P : Profile} {s : Store Nat} {f : Frame} {us : List Val} {is : List Instr}
  {Q : Post Nat}

/-- `Q` accepts every trap and exception in the store `s`. -/
def Traps (Q : Post Nat) (s : Store Nat) : Prop := ∀ f, Q s f .trap ∧ ∀ a, Q s f (.throw a)

/-! ## Import calls -/

section Import

variable {I : ScalarInstance} {Ii : ISpec I.E}

/-- A call of import `k` when the postcondition accepts traps and exceptions. -/
theorem hwp_importT {x : FuncIdx} {k : Nat} {fk : FuncInst Nat} {ps rs : Ty (.list .val)}
    {args : List Val}
    (hx : f.module.funcs[x.toNat]? = some k) (hf : s.funcs[k]? = some fk) (hcode : fk.code = .host k)
    (he : Expand fk.type (.func ps rs)) (hps : ps.length = args.length)
    (hop : ∃ e, I.importOp? k args = some e ∧ Ii.pre e)
    (hk : ∀ e (v : I.E.Ar e), I.importOp? k args = some e → Ii.post e v →
      ∀ res, Answer.toResult (ft := I.imports.get e.1) v = .values res →
        HWP P (gameHost I Ii) s f (vals (us ++ res) ++ expression is) Q)
    (hQ : Traps Q s) :
    HWP P (gameHost I Ii) s f (vals (us ++ args) ++ expression (.call x :: is)) Q
  | 0 => trivial
  | n + 1 => by
    have hS : importCtx I Ii (id k) = some (importSpec I Ii k) := rfl
    refine Safe.callIdx (x := x) (S := Silmaril.Wasm.Logic.Open.stubSpec k k (importSpec I Ii k)) hx hf
      (Silmaril.Wasm.Logic.Open.FSpecAt.stub hS n) ⟨⟨fk, ps, rs, hf, hcode, he, hps.symm⟩, hop⟩ ?_
    rintro s' o ⟨-, ⟨res, rfl, hR⟩ | ⟨rfl, hR⟩ | ⟨y, rfl, hR⟩⟩
    · obtain ⟨rfl, hall⟩ := hR
      obtain ⟨e, he', -⟩ := hop
      obtain ⟨v, hv, ho⟩ := hall e he'
      have hr : Answer.toResult (ft := I.imports.get e.1) v = .values res := by
        revert ho
        cases v <;> simp [Answer.toResult, resultOutcome]
      exact hk e v he' hv res hr n
    · obtain ⟨rfl, -⟩ := hR
      exact (hQ f).1
    · obtain ⟨rfl, -⟩ := hR
      exact (hQ f).2 y

end Import

section Calls

variable {I : ScalarInstance} {fts : List FnType} {eft : FnType} {locals : List ValType}
  {body : List Instr} {D : List (Option Val)}
  (hS : GShape I fts eft locals body D) (hs : s.funcs = I.store.funcs)
  (hm : f.module.funcs = List.range (fts.length + 1)) {Ii : ISpec I.E}

include hS hs hm

/-- A call of import `k` by a module of shape `GShape`, for a postcondition accepting traps
and exceptions. -/
theorem X.callT {k : Nat} (hk : k < fts.length) {x : FuncIdx} (hx : x.toNat = k)
    {args : List Val} (hargs : (fts[k]'hk).params.length = args.length)
    (hop : ∃ e, I.importOp? k args = some e ∧ Ii.pre e)
    (hc : ∀ e (v : I.E.Ar e), I.importOp? k args = some e → Ii.post e v →
      ∀ res, Answer.toResult (ft := I.imports.get e.1) v = .values res →
        HWP P (gameHost I Ii) s f (vals (us ++ res) ++ expression is) Q)
    (hQ : Traps Q s) :
    HWP P (gameHost I Ii) s f (vals (us ++ args) ++ expression (.call x :: is)) Q := by
  obtain ⟨fk, ps, rs, hf, hcode, he, hps⟩ := hS.stub k hk
  refine hwp_importT (fk := fk) (ps := ps) (rs := rs) ?_ (by rw [hs]; exact hf) hcode he
    (hps.trans hargs) hop hc hQ
  rw [hm, hx, List.getElem?_range (by omega)]

end Calls

/-! ## From the function body to the game -/

/-- **A module of shape `GShape` meets a nontrivial export specification** `Ie` (allowing every
answer that returns no values) if its body, from the frame of a call on typed arguments, is safe
for every postcondition accepting traps, exceptions and the `return` of results whose answers
`Ie` allows. -/
theorem gameSat_ofE {I : ScalarInstance} {fts : List FnType} {eft : FnType}
    {locals : List ValType} {body : List Instr} {D : List (Option Val)}
    (hS : GShape I fts eft locals body D) {Ii : ISpec I.E} {Ie : ISpec I.F}
    (hIe : ∀ (j : Fin I.exports.length) args
      (ht : List.Forall₂ ScalarType.HasVal (I.exports.get j).params args)
      (v : Answer (I.exports.get j)), ansVals v = none → Ie.post ⟨j, ⟨args, ht⟩⟩ v)
    (hbody : ∀ (fi : FuncInst Nat) (s : Store Nat) (args : List Val) (j : Fin I.exports.length)
      (ht : List.Forall₂ ScalarType.HasVal (I.exports.get j).params args) (Q : Post Nat),
      List.Forall₂ ScalarType.HasVal eft.params args →
      I.store.funcs[fts.length]? = some fi → fi.module.funcs = List.range (fts.length + 1) →
      s.funcs = I.store.funcs → Traps Q s →
      (∀ f res, res.length = eft.results.length →
        (∀ v : Answer (I.exports.get j), v.toResult = .values res → Ie.post ⟨j, ⟨args, ht⟩⟩ v) →
        Q s f (.ret res)) →
      HWP P (gameHost I Ii) s ⟨args.map some ++ D, fi.module⟩ (vals [] ++ expression body) Q) :
    GameSat P I (StoreInv I) Ii Ie := by
  intro j
  rw [hS.addr j]
  obtain ⟨fi, code, ps, rs, hf, hcode, hloc, hbod, he, hps, hrs, hm, hD⟩ := hS.fn
  have hl : I.exports.length = 1 := by rw [hS.exports]; rfl
  have hg : I.exports.get j = eft := by
    rw [List.get_eq_getElem, List.getElem_of_eq hS.exports j.2]
    have hj : j.val = 0 := by have := j.2; omega
    simp only [hj]
    rfl
  intro n
  cases n with
  | zero => exact fun _ _ _ _ _ _ _ => trivial
  | succ n =>
    refine FSpecAt.of_body (fi := fi) (fun s args hpre => by rw [hpre.1]; exact hf) hcode he
      (fun s args hpre => ?_) (fun s args hpre f₀ vs₀ => ?_)
    · obtain ⟨-, ht, -⟩ := hpre
      rw [hg] at ht
      rw [hps, ht.length_eq]
    · obtain ⟨hInv, ht, -⟩ := hpre
      have ht' := ht
      rw [hg] at ht'
      have hfr : Frame.forCall fi.module args code.locals = ⟨args.map some ++ D, fi.module⟩ := by
        unfold Frame.forCall
        rw [hloc, hD]
      rw [hfr, hbod]
      refine hbody fi s args j ht _ ht' hf hm hInv (fun F => ⟨?_, fun a => ?_⟩)
        (fun F res hlen hpost => ?_) n
      · refine ⟨rfl, .inr (.inl ⟨rfl, hInv, fun ht₂ v hv => hIe j args ht₂ v ?_⟩)⟩
        cases v with
        | values vs => simp [Answer.toResult, resultOutcome] at hv
        | _ => rfl
      · refine ⟨rfl, .inr (.inr ⟨a, rfl, hInv, fun ht₂ v hv => hIe j args ht₂ v ?_⟩)⟩
        cases v with
        | values vs => simp [Answer.toResult, resultOutcome] at hv
        | _ => rfl
      · refine ⟨[], res, by simp, by rw [hlen, hrs], rfl, .inl ⟨res, rfl, hInv, fun ht₂ v hv => ?_⟩⟩
        refine hpost v ?_
        cases v with
        | values vs => simpa [Answer.toResult, resultOutcome] using hv
        | _ => simp [Answer.toResult, resultOutcome] at hv

/-! ## `nzParse` -/

/-- `[i64] → [i32]`. -/
abbrev parseFT : FnType := ⟨[.num (.int .i64)], [.num (.int .i32)]⟩

theorem nz_shape : GShape (Verify.instOf nzParse) [parseFT] parseFT [] nzBody [] :=
  GShape.of_ok (by decide +kernel)

/-- What a `parse` answer decodes to. -/
theorem parseDec_nz {ts : List FnType} {e : (ifaceSig ts).Op} {v : (ifaceSig ts).Ar e}
    {w : BitVec 64} {h : BitVec 32} (hd : parseDec nzIx e v = some (.parse w h)) :
    i64Val e.2.1 = some w ∧ ∃ vs, ansVals v = some vs ∧ i32Res vs = some h := by
  unfold parseDec at hd
  rcases hv : ansVals v with _ | vs <;> simp only [hv, Option.bind_eq_bind, Option.bind_none,
    Option.bind_some, reduceCtorEq] at hd
  simp only [nzIx] at hd
  split_ifs at hd
  · rcases hw : i64Val e.2.1 with _ | w' <;> rcases hr : i32Res vs with _ | r <;>
      simp [hw, hr] at hd
    obtain ⟨rfl, rfl⟩ := hd
    exact ⟨rfl, vs, rfl, hr⟩
  simp_all

theorem eqz64_ne {x : BitVec 64} (h : Numerics.intTestOp .i64 .eqz x ≠ 0) : x = 0 := by
  have := bool32_ne_zero (b := x == 0) h
  simpa using this

theorem eqz64_eq {x : BitVec 64} (h : Numerics.intTestOp .i64 .eqz x = 0) : x ≠ 0 := by
  have := bool32_eq_zero (b := x == 0) h
  simpa using this

/-- **`nzParse` meets the parse specification of `nzR`** (sentinel `0`) in every environment
and every profile. -/
theorem nzParse_sat (P : Profile) {T : Type}
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) T) :
    GameSat P (Verify.instOf nzParse) (StoreInv (Verify.instOf nzParse)) (topISpec _)
      (parseESpec nzIx 0 ρ (nzR T)) := by
  refine gameSat_ofE nz_shape (fun j args ht v hv w h hd => ?_)
    fun fi s args j ht Q ht' _ hm hs hT hret => ?_
  · obtain ⟨-, vs, hvs, -⟩ := parseDec_nz hd
    rw [hv] at hvs
    cases hvs
  obtain ⟨x, rfl⟩ : ∃ x, args = [.i64 x] := by
    rcases ht' with _ | ⟨⟨x, rfl⟩, hnil⟩
    cases hnil
    exact ⟨x, rfl⟩
  simp only [nzBody]
  refine X.localGet (v := .i64 x) rfl ?_
  refine Wp.intTestOp (m := .part) (t := .i64) (x := x) (us := []) ?_
  refine X.if_ (fun h0 => ?_) (fun h0 => ?_)
  · -- `parse(0)`: the sentinel
    refine X.i32Const ?_
    refine X.return_ (hret _ [.i32 0] rfl fun v hv w h hd hh => ?_)
    obtain ⟨-, vs, hvs, hr⟩ := parseDec_nz hd
    have : vs = [.i32 0] := by
      cases v <;> simp_all [Answer.toResult, ansVals]
    subst this
    simp [i32Res, Val.i32] at hr
    exact absurd hr.symm hh
  · -- `parse(x)`, `x ≠ 0`: `word(x)`
    have hx := eqz64_eq h0
    refine X.localGet (v := .i64 x) rfl ?_
    refine X.callT (us := []) nz_shape hs hm (k := 0) (by decide) rfl rfl
      (Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.importOp?_existsG nz_shape.imports
        (k := 0) (by decide) (.cons ⟨x, rfl⟩ .nil) |>.imp fun _ he => ⟨he, trivial⟩)
      (fun e v he _ res hr => ?_) hT
    obtain ⟨hty, -⟩ := results_ofG nz_shape.imports hr
    simp only [(importOp?_eq he).1] at hty
    obtain ⟨c, rfl⟩ := res_i32 hty
    refine X.return_ (hret _ [.i32 c] rfl fun v' _ w h hd _ y _ => ?_)
    obtain ⟨hw, -⟩ := parseDec_nz hd
    simp [i64Val, Writers.i64Arg, Val.i64] at hw
    exact ⟨w, rfl, hw ▸ hx⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Parsing.Checkers
