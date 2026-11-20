module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.Generic
public import Silmaril.Wasm.Game.HandleAccept.Combined.Defs

/-!
# `readBack` meets its combined specification

What an allowed answer of the combined imports says under `combISpec` (`cWrite_post`,
`cKind_post`, `cCar_post`, `cCdr_post`), the call rules for an instance of shape
`GShape I readBackFTs runFT …`, and `readBack_sat`: in every fixed environment `ρ`, for every
sentinel and profile, the instance meets the combined specification of `singleL`. The proof uses
**only the reads**: the written handle is accepted only after `kind`, `car` and `cdr` confirmed
that it denotes `(w)`, so nothing is assumed about the answers of the writes.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Combined

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.GameLink
  Silmaril.Formats Silmaril.Formats.Api Silmaril.Accept.Handle Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Writers Silmaril.Wasm.Game.HandleAccept.Combined
  Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers
open Silmaril.Wasm.Logic.Strategy (ISpec)
open Silmaril.Wasm.Logic.Core (Outcome Post)

/-- `[] → [i32]`. -/
abbrev nilFT : FnType := ⟨[], [.num (.int .i32)]⟩
/-- `[i32 i32] → [i32]`. -/
abbrev consFT : FnType := ⟨[.num (.int .i32), .num (.int .i32)], [.num (.int .i32)]⟩
/-- `[i64] → [i32]`. -/
abbrev wordFT : FnType := ⟨[.num (.int .i64)], [.num (.int .i32)]⟩
/-- `[i64] → []`. -/
abbrev runFT : FnType := ⟨[.num (.int .i64)], []⟩

/-- The import types of `readBack`. -/
abbrev readBackFTs : List FnType := [nilFT, consFT, wordFT, aFT, qFT, qFT, qFT]

/-- The combined specification of `readBack`. -/
abbrev CSpec (I : ScalarInstance) (sn : Option (BitVec 32))
    (ρ : Env (BitVec 32) (SExp2 (BitVec 64))) (L : Set (SExp2 (BitVec 64))) : ISpec I.E :=
  combISpec (consW (BitVec 64)) (consR (BitVec 64) (BitVec 32)) sn
    (combDecAsk (ts := I.imports) readBackIx) (combDecAns readBackIx) ρ L

variable {P : Profile} {s : Store Nat} {f : Frame} {us : List Val} {is : List Instr}
  {Q : Post Nat}

/-! ## Answers -/

section Posts

variable {I : ScalarInstance} (hI : I.imports = readBackFTs) {sn : Option (BitVec 32)}
  {ρ : Env (BitVec 32) (SExp2 (BitVec 64))} {L : Set (SExp2 (BitVec 64))}

include hI

/-- Only `accept` has a precondition. -/
theorem c_pre_of_ne {k : Nat} (hk : k < 7) (h3 : k ≠ 3) {args : List Val}
    (ht : List.Forall₂ ScalarType.HasVal (readBackFTs[k]'hk).params args) :
    ∃ e, I.importOp? k args = some e ∧ (CSpec I sn ρ L).pre e := by
  obtain ⟨e, he⟩ := importOp?_existsG hI hk ht
  refine ⟨e, he, fun h hd => ?_⟩
  have h1 := (importOp?_eq he).1
  simp [combDecAsk, readBackIx, h1, h3] at hd

/-- `accept(a)` is allowed when `a` denotes a member of `L`. -/
theorem c_pre_accept (a : BitVec 32) (hL : ∀ t, ρ a = some t → t ∈ L) :
    ∃ e, I.importOp? 3 [.i32 a] = some e ∧ (CSpec I sn ρ L).pre e := by
  obtain ⟨e, he⟩ := importOp?_existsG hI (k := 3) (by decide) (.cons ⟨a, rfl⟩ .nil)
  refine ⟨e, he, fun h hd => ?_⟩
  obtain ⟨h1, h2⟩ := importOp?_eq he
  simp [combDecAsk, readBackIx, h1, h2, i32Arg] at hd
  obtain rfl := hd
  exact hL

variable {e : I.E.Op} {v : I.E.Ar e} {res : List Val}

/-- An answer of an import returning one `i32`. -/
theorem c_res_i32 {k : Nat} {args : List Val} (hk : k < 7)
    (hty : (readBackFTs[k]'hk).results = [.num (.int .i32)])
    (he : I.importOp? k args = some e)
    (hr : Answer.toResult (ft := I.imports.get e.1) v = .values res) :
    ∃ r, res = [.i32 r] ∧ retI32 v = some r := by
  obtain ⟨h1, -⟩ := importOp?_eq he
  obtain ⟨hty', hans⟩ := results_ofG hI hr
  have : (readBackFTs[e.1.val]'(by simpa [hI] using e.1.2)).results = [.num (.int .i32)] := by
    simp only [h1]; exact hty
  rw [this] at hty'
  obtain ⟨r, rfl⟩ := res_i32 hty'
  exact ⟨r, rfl, by simp [retI32, hans, i32Res, Val.i32]⟩

/-- An allowed answer of `kind(a)`. -/
theorem cKind_post {a : BitVec 32} (he : I.importOp? 4 [.i32 a] = some e)
    (hv : (CSpec I sn ρ L).post e v)
    (hr : Answer.toResult (ft := I.imports.get e.1) v = .values res) :
    ∃ c, res = [.i32 c] ∧ ((c = 0 ∧ ρ a = some .nil) ∨ (c = 1 ∧ ∃ w, ρ a = some (.atom w)) ∨
      (c = 2 ∧ ∃ x y, ρ a = some (.cons x y))) := by
  obtain ⟨c, rfl, hc⟩ := c_res_i32 hI (k := 4) (by decide) rfl he hr
  refine ⟨c, rfl, ?_⟩
  obtain ⟨h1, h2⟩ := importOp?_eq he
  have hd : combDecAns readBackIx e v = some (.r (.kind a) (kindAns c)) := by
    simp [combDecAns, readBackIx, h1, h2, hc, i32Arg, Val.i32]
  obtain ⟨-, hok⟩ := hv.2 _ _ hd
  unfold kindAns at hok
  split_ifs at hok with hc0 hc1 hc2
  · obtain ⟨x, hx, hk⟩ := hok
    cases x <;> cases hk
    exact .inl ⟨hc0, hx⟩
  · obtain ⟨x, hx, hk⟩ := hok
    cases x <;> cases hk
    exact .inr (.inl ⟨hc1, _, hx⟩)
  · obtain ⟨x, hx, hk⟩ := hok
    cases x <;> cases hk
    exact .inr (.inr ⟨hc2, _, _, hx⟩)
  · exact hok.elim

/-- An allowed answer of `car(a)`. -/
theorem cCar_post {a : BitVec 32} (he : I.importOp? 5 [.i32 a] = some e)
    (hv : (CSpec I sn ρ L).post e v)
    (hr : Answer.toResult (ft := I.imports.get e.1) v = .values res) :
    ∃ c, res = [.i32 c] ∧ ∃ x y, ρ a = some (.cons x y) ∧ ρ c = some x := by
  obtain ⟨c, rfl, hc⟩ := c_res_i32 hI (k := 5) (by decide) rfl he hr
  refine ⟨c, rfl, ?_⟩
  obtain ⟨h1, h2⟩ := importOp?_eq he
  have hd : combDecAns readBackIx e v = some (.r (.car a) (.handle c)) := by
    simp [combDecAns, readBackIx, h1, h2, hc, i32Arg, Val.i32]
  exact (hv.2 _ _ hd).2

/-- An allowed answer of `cdr(a)`. -/
theorem cCdr_post {a : BitVec 32} (he : I.importOp? 6 [.i32 a] = some e)
    (hv : (CSpec I sn ρ L).post e v)
    (hr : Answer.toResult (ft := I.imports.get e.1) v = .values res) :
    ∃ c, res = [.i32 c] ∧ ∃ x y, ρ a = some (.cons x y) ∧ ρ c = some y := by
  obtain ⟨c, rfl, hc⟩ := c_res_i32 hI (k := 6) (by decide) rfl he hr
  refine ⟨c, rfl, ?_⟩
  obtain ⟨h1, h2⟩ := importOp?_eq he
  have hd : combDecAns readBackIx e v = some (.r (.cdr a) (.handle c)) := by
    simp [combDecAns, readBackIx, h1, h2, hc, i32Arg, Val.i32]
  exact (hv.2 _ _ hd).2

/-- An answer of `accept(a)` returns no values. -/
theorem cAccept_post {a : BitVec 32} (he : I.importOp? 3 [.i32 a] = some e)
    (hr : Answer.toResult (ft := I.imports.get e.1) v = .values res) : res = [] := by
  obtain ⟨h1, -⟩ := importOp?_eq he
  obtain ⟨hty, -⟩ := results_ofG hI hr
  simp only [h1] at hty
  exact res_nil hty

end Posts

/-! ## Calls -/

section Calls

variable {I : ScalarInstance} {locals : List ValType} {body : List Instr} {D : List (Option Val)}
  (hS : GShape I readBackFTs runFT locals body D) (hs : s.funcs = I.store.funcs)
  (hm : f.module.funcs = List.range (readBackFTs.length + 1)) {sn : Option (BitVec 32)}
  {ρ : Env (BitVec 32) (SExp2 (BitVec 64))} {L : Set (SExp2 (BitVec 64))}

include hS hs hm

/-- A write (`nil`, `cons`, `word`): its result is some handle, nothing else is used. -/
theorem X.cWrite {k : Nat} (hk : k < 3) {x : FuncIdx} (hx : x.toNat = k) {args : List Val}
    (ht : List.Forall₂ ScalarType.HasVal (readBackFTs[k]'(by simp only [readBackFTs, List.length_cons, List.length_nil]; omega)).params args)
    (hQ : Leaves Q s)
    (hc : ∀ r : BitVec 32,
      HWP P (gameHost I (CSpec I sn ρ L)) s f (vals (us ++ [.i32 r]) ++ expression is) Q) :
    HWP P (gameHost I (CSpec I sn ρ L)) s f (vals (us ++ args) ++ expression (.call x :: is))
      Q :=
  X.callG hS hs hm (k := k) (by simp only [readBackFTs, List.length_cons, List.length_nil]; omega)
    hx ht.length_eq
    (c_pre_of_ne hS.imports (by omega) (by omega) ht)
    (fun _ _ he _ res hr => by
      obtain ⟨r, rfl, -⟩ := c_res_i32 hS.imports (k := k) (by omega)
        (by rcases k with _ | _ | _ | k <;> first | rfl | omega) he hr
      exact hc r) hQ

/-- `kind(a)`. -/
theorem X.cKind {a : BitVec 32} (hQ : Leaves Q s)
    (hc : ∀ c, ((c = 0 ∧ ρ a = some .nil) ∨ (c = 1 ∧ ∃ w, ρ a = some (.atom w)) ∨
        (c = 2 ∧ ∃ x y, ρ a = some (.cons x y))) →
      HWP P (gameHost I (CSpec I sn ρ L)) s f (vals (us ++ [.i32 c]) ++ expression is) Q) :
    HWP P (gameHost I (CSpec I sn ρ L)) s f
      (vals (us ++ [.i32 a]) ++ expression (.call ⟨4⟩ :: is)) Q :=
  X.callG hS hs hm (k := 4) (by decide) rfl rfl
    (c_pre_of_ne hS.imports (by decide) (by decide) (.cons ⟨a, rfl⟩ .nil))
    (fun _ _ he hv res hr => by
      obtain ⟨c, rfl, h⟩ := cKind_post hS.imports he hv hr
      exact hc c h) hQ

/-- `car(a)`. -/
theorem X.cCar {a : BitVec 32} (hQ : Leaves Q s)
    (hc : ∀ c x y, ρ a = some (.cons x y) → ρ c = some x →
      HWP P (gameHost I (CSpec I sn ρ L)) s f (vals (us ++ [.i32 c]) ++ expression is) Q) :
    HWP P (gameHost I (CSpec I sn ρ L)) s f
      (vals (us ++ [.i32 a]) ++ expression (.call ⟨5⟩ :: is)) Q :=
  X.callG hS hs hm (k := 5) (by decide) rfl rfl
    (c_pre_of_ne hS.imports (by decide) (by decide) (.cons ⟨a, rfl⟩ .nil))
    (fun _ _ he hv res hr => by
      obtain ⟨c, rfl, x, y, h1, h2⟩ := cCar_post hS.imports he hv hr
      exact hc c x y h1 h2) hQ

/-- `cdr(a)`. -/
theorem X.cCdr {a : BitVec 32} (hQ : Leaves Q s)
    (hc : ∀ c x y, ρ a = some (.cons x y) → ρ c = some y →
      HWP P (gameHost I (CSpec I sn ρ L)) s f (vals (us ++ [.i32 c]) ++ expression is) Q) :
    HWP P (gameHost I (CSpec I sn ρ L)) s f
      (vals (us ++ [.i32 a]) ++ expression (.call ⟨6⟩ :: is)) Q :=
  X.callG hS hs hm (k := 6) (by decide) rfl rfl
    (c_pre_of_ne hS.imports (by decide) (by decide) (.cons ⟨a, rfl⟩ .nil))
    (fun _ _ he hv res hr => by
      obtain ⟨c, rfl, x, y, h1, h2⟩ := cCdr_post hS.imports he hv hr
      exact hc c x y h1 h2) hQ

/-- `accept(a)`, for `a` denoting a member of `L`. -/
theorem X.cAccept {a : BitVec 32} (hL : ∀ t, ρ a = some t → t ∈ L) (hQ : Leaves Q s)
    (hc : HWP P (gameHost I (CSpec I sn ρ L)) s f (vals us ++ expression is) Q) :
    HWP P (gameHost I (CSpec I sn ρ L)) s f
      (vals (us ++ [.i32 a]) ++ expression (.call ⟨3⟩ :: is)) Q :=
  X.callG hS hs hm (k := 3) (by decide) rfl rfl (c_pre_accept hS.imports a hL)
    (fun _ _ he _ res hr => by
      obtain rfl := cAccept_post hS.imports he hr
      simpa using hc) hQ

end Calls

/-! ## The module -/

theorem readBack_shape : GShape (Verify.instOf readBack) readBackFTs runFT [.i32, .i32]
    readBackBody [some (.i32 0), some (.i32 0)] :=
  GShape.of_ok (by decide +kernel)

theorem args_runFT {args : List Val} (ht : List.Forall₂ ScalarType.HasVal runFT.params args) :
    ∃ x, args = [.i64 x] := by
  rcases ht with _ | ⟨⟨x, rfl⟩, hnil⟩
  cases hnil
  exact ⟨x, rfl⟩

/-- **`readBack` meets the combined specification of `singleL`**, in every fixed environment,
for every sentinel and profile. -/
theorem readBack_sat (P : Profile) (sn : Option (BitVec 32))
    (ρ : Env (BitVec 32) (SExp2 (BitVec 64))) :
    GameSat P (Verify.instOf readBack) (StoreInv (Verify.instOf readBack))
      (CSpec (Verify.instOf readBack) sn ρ singleL) (topISpec _) :=
  gameSat_ofG readBack_shape rfl fun fi s args Q ht _ hm hs hQ hQn => by
    obtain ⟨x, rfl⟩ := args_runFT ht
    have hS := readBack_shape
    simp only [readBackBody]
    refine X.localGet (v := .i64 x) rfl ?_
    refine X.cWrite (us := []) hS hs hm (k := 2) (by decide) rfl (.cons ⟨x, rfl⟩ .nil) hQ
      (fun a => ?_)
    refine X.cWrite (us := [.i32 a]) (args := []) hS hs hm (k := 0) (by decide) rfl .nil hQ
      (fun n => ?_)
    rw [show [Val.i32 a] ++ [Val.i32 n] = ([] : List Val) ++ [Val.i32 a, Val.i32 n] from rfl]
    refine X.cWrite (us := []) hS hs hm (k := 1) (by decide) rfl
      (.cons ⟨a, rfl⟩ (.cons ⟨n, rfl⟩ .nil)) hQ (fun c => ?_)
    refine X.localSet (by simp [Idx.toNat]) ?_
    refine X.localGet (v := .i32 c) rfl ?_
    refine X.cKind hS hs hm hQ (fun k hk => ?_)
    refine X.neConst ?_
    refine X.if_ (fun _ => X.return_ ((hQ.label _).1 _)) (fun h2 => ?_)
    have hk2 : k = 2 := bne_eq_false_iff_eq.1 (bool32_eq_zero h2)
    obtain ⟨y, z, hcz⟩ : ∃ y z, ρ c = some (.cons y z) := by
      rcases hk with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨-, h⟩
      · exact absurd hk2 (by decide)
      · exact absurd hk2 (by decide)
      · exact h
    refine X.localGet (v := .i32 c) rfl ?_
    refine X.cCar hS hs hm hQ (fun a' y' z' hc' ha' => ?_)
    have hy : ρ a' = some y := by
      rw [ha', (SExp2.cons.inj (Option.some.inj (hc'.symm.trans hcz))).1]
    refine X.cKind hS hs hm hQ (fun k₁ hk₁ => ?_)
    refine X.neConst ?_
    refine X.if_ (fun _ => X.return_ ((hQ.label _).1 _)) (fun h1 => ?_)
    have hk1 : k₁ = 1 := bne_eq_false_iff_eq.1 (bool32_eq_zero h1)
    obtain ⟨w, hw⟩ : ∃ w, ρ a' = some (.atom w) := by
      rcases hk₁ with ⟨rfl, -⟩ | ⟨-, h⟩ | ⟨rfl, -⟩
      · exact absurd hk1 (by decide)
      · exact h
      · exact absurd hk1 (by decide)
    have hyw : y = .atom w := Option.some.inj (hy.symm.trans hw)
    refine X.localGet (v := .i32 c) rfl ?_
    refine X.cCdr hS hs hm hQ (fun d y'' z'' hc'' hd => ?_)
    have hz : ρ d = some z := by
      rw [hd, (SExp2.cons.inj (Option.some.inj (hc''.symm.trans hcz))).2]
    refine X.localSet (by simp [Frame.setLocal, Idx.toNat]) ?_
    refine X.localGet (v := .i32 d) rfl ?_
    refine X.cKind hS hs hm hQ (fun k₀ hk₀ => ?_)
    refine X.neConst ?_
    refine X.if_ (fun _ => X.return_ ((hQ.label _).1 _)) (fun h0 => ?_)
    have hk0 : k₀ = 0 := bne_eq_false_iff_eq.1 (bool32_eq_zero h0)
    have hnil : ρ d = some .nil := by
      rcases hk₀ with ⟨-, h⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact h
      · exact absurd hk0 (by decide)
      · exact absurd hk0 (by decide)
    have hzn : z = .nil := Option.some.inj (hz.symm.trans hnil)
    refine X.localGet (v := .i32 c) rfl ?_
    refine X.cAccept (us := []) hS hs hm (fun t ht' => ?_) hQ (X.done (hQn _))
    rw [hcz, hyw, hzn] at ht'
    cases ht'
    exact ⟨w, rfl⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Combined
