module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.Generic
public import Silmaril.Wasm.Game.HandleAccept.Nary.Examples

/-!
# N-ary reader checkers: import rules

What an allowed answer of the n-ary reader imports `kind`, `count`, `child`, `word` and
`accept` (indices `pairIx`) says under `sexpISpec` (`sxKind_post`, `sxCount_post`,
`sxChild_post`, `sxWord_post`, `sxAccept_post`), and the call rules for an instantiated
module of shape `GShape I sxFTs aFT …` (`X.sxKind`, …, `X.sxAccept`).

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Nary

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.GameLink
  Silmaril.Formats Silmaril.Formats.Api Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Nary Silmaril.Wasm.Game.HandleAccept.Nary.Examples
  Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers
open Silmaril.Wasm.Logic.Strategy (ISpec)
open Silmaril.Wasm.Logic.Core (Outcome Post)

/-- `[i32 i32] → [i32]`. -/
abbrev cFT : FnType := ⟨[.num (.int .i32), .num (.int .i32)], [.num (.int .i32)]⟩

/-- The import types of the n-ary reader checkers. -/
abbrev sxFTs : List FnType := [qFT, qFT, cFT, wFT, aFT]

variable {P : Profile} {s : Store Nat} {f : Frame} {us : List Val} {is : List Instr}
  {Q : Post Nat}

section Posts

variable {I : ScalarInstance} (hI : I.imports = sxFTs)
  {ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp (BitVec 64))} {L : Set (SExp (BitVec 64))}

include hI

/-- Only `accept` has a precondition. -/
theorem sx_pre_of_ne {k : Nat} (hk : k < 5) (h4 : k ≠ 4) {args : List Val}
    (ht : List.Forall₂ ScalarType.HasVal (sxFTs[k]'hk).params args) :
    ∃ e, I.importOp? k args = some e ∧ (sexpISpec (ts := I.imports) pairIx ρ L).pre e := by
  obtain ⟨e, he⟩ := importOp?_existsG hI hk ht
  refine ⟨e, he, fun h hd => ?_⟩
  have h1 := (importOp?_eq he).1
  simp [sxDecAsk, pairIx, h1, h4] at hd

/-- `accept(a)` is allowed when `a` denotes a member of `L`. -/
theorem sx_pre_accept (a : BitVec 32) (hL : ∀ t, ρ a = some t → t ∈ L) :
    ∃ e, I.importOp? 4 [.i32 a] = some e ∧ (sexpISpec (ts := I.imports) pairIx ρ L).pre e := by
  obtain ⟨e, he⟩ := importOp?_existsG hI (k := 4) (by decide) (.cons ⟨a, rfl⟩ .nil)
  refine ⟨e, he, fun h hd => ?_⟩
  obtain ⟨h1, h2⟩ := importOp?_eq he
  simp [sxDecAsk, pairIx, h1, h2, i32Arg] at hd
  obtain rfl := hd
  exact hL

variable {e : I.E.Op} {v : I.E.Ar e} {a : BitVec 32} {res : List Val}

/-- An allowed answer of `kind(a)`. -/
theorem sxKind_post (he : I.importOp? 0 [.i32 a] = some e)
    (hv : (sexpISpec (ts := I.imports) pairIx ρ L).post e v)
    (hr : Answer.toResult (ft := I.imports.get e.1) v = .values res) :
    ∃ c, res = [.i32 c] ∧ ((c = 0 ∧ ∃ w, ρ a = some (.atom w)) ∨
      (c = 1 ∧ ∃ x, ρ a = some x ∧ isList x = true)) := by
  obtain ⟨h1, h2⟩ := importOp?_eq he
  obtain ⟨hty, hans⟩ := results_ofG hI hr
  simp only [h1] at hty
  obtain ⟨c, rfl⟩ := res_i32 hty
  refine ⟨c, rfl, ?_⟩
  have hd : sxDecAns pairIx e v = some (.read (.kind a) (sxKindAns c)) := by
    simp [sxDecAns, sxDecRead, pairIx, h1, h2, hans, i32Arg, i32Res, Val.i32]
  obtain ⟨-, hok⟩ := hv _ _ hd
  unfold sxKindAns at hok
  split_ifs at hok with hc0 hc1
  · obtain ⟨x, hx, hk⟩ := hok
    cases x with
    | atom w => exact .inl ⟨hc0, w, hx⟩
    | list => cases hk
  · obtain ⟨x, hx, hk⟩ := hok
    exact .inr ⟨hc1, x, hx, hk.symm⟩
  · exact hok.elim

/-- An allowed answer of `count(a)`. -/
theorem sxCount_post (he : I.importOp? 1 [.i32 a] = some e)
    (hv : (sexpISpec (ts := I.imports) pairIx ρ L).post e v)
    (hr : Answer.toResult (ft := I.imports.get e.1) v = .values res) :
    ∃ c, res = [.i32 c] ∧ ∃ cs, ρ a = some (SExp.ofList cs) ∧ cs.length = c.toNat := by
  obtain ⟨h1, h2⟩ := importOp?_eq he
  obtain ⟨hty, hans⟩ := results_ofG hI hr
  simp only [h1] at hty
  obtain ⟨c, rfl⟩ := res_i32 hty
  refine ⟨c, rfl, ?_⟩
  have hd : sxDecAns pairIx e v = some (.read (.count a) (.count c.toNat)) := by
    simp [sxDecAns, sxDecRead, pairIx, h1, h2, hans, i32Arg, i32Res, Val.i32]
  exact (hv _ _ hd).2

/-- An allowed answer of `child(a, i)`. -/
theorem sxChild_post {i : BitVec 32} (he : I.importOp? 2 [.i32 a, .i32 i] = some e)
    (hv : (sexpISpec (ts := I.imports) pairIx ρ L).post e v)
    (hr : Answer.toResult (ft := I.imports.get e.1) v = .values res) :
    ∃ c, res = [.i32 c] ∧ ∃ cs x, ρ a = some (SExp.ofList cs) ∧ cs[i.toNat]? = some x ∧
      ρ c = some x := by
  obtain ⟨h1, h2⟩ := importOp?_eq he
  obtain ⟨hty, hans⟩ := results_ofG hI hr
  simp only [h1] at hty
  obtain ⟨c, rfl⟩ := res_i32 hty
  refine ⟨c, rfl, ?_⟩
  have hd : sxDecAns pairIx e v = some (.read (.child a i.toNat) (.handle c)) := by
    simp [sxDecAns, sxDecRead, pairIx, h1, h2, hans, i32Two, i32Res, Val.i32]
  exact (hv _ _ hd).2

/-- An allowed answer of `word(a)`. -/
theorem sxWord_post (he : I.importOp? 3 [.i32 a] = some e)
    (hv : (sexpISpec (ts := I.imports) pairIx ρ L).post e v)
    (hr : Answer.toResult (ft := I.imports.get e.1) v = .values res) :
    ∃ w, res = [.i64 w] ∧ ρ a = some (.atom w) := by
  obtain ⟨h1, h2⟩ := importOp?_eq he
  obtain ⟨hty, hans⟩ := results_ofG hI hr
  simp only [h1] at hty
  obtain ⟨w, rfl⟩ := res_i64 hty
  refine ⟨w, rfl, ?_⟩
  have hd : sxDecAns pairIx e v = some (.read (.atom a) (.atom w)) := by
    simp [sxDecAns, sxDecRead, pairIx, h1, h2, hans, i32Arg, i64Res, Val.i32, Val.i64]
  exact (hv _ _ hd).2

/-- An answer of `accept(a)` returns no values. -/
theorem sxAccept_post (he : I.importOp? 4 [.i32 a] = some e)
    (hr : Answer.toResult (ft := I.imports.get e.1) v = .values res) : res = [] := by
  obtain ⟨h1, -⟩ := importOp?_eq he
  obtain ⟨hty, -⟩ := results_ofG hI hr
  simp only [h1] at hty
  exact res_nil hty

end Posts

/-! ## Calls of an instantiated checker -/

section Calls

variable {I : ScalarInstance} {locals : List ValType} {body : List Instr} {D : List (Option Val)}
  (hS : GShape I sxFTs aFT locals body D) (hs : s.funcs = I.store.funcs)
  (hm : f.module.funcs = List.range (sxFTs.length + 1))
  {ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp (BitVec 64))} {L : Set (SExp (BitVec 64))}
  {a : BitVec 32}

include hS hs hm

/-- `kind(a)`. -/
theorem X.sxKind (hQ : Leaves Q s)
    (hc : ∀ c, ((c = 0 ∧ ∃ w, ρ a = some (.atom w)) ∨
      (c = 1 ∧ ∃ x, ρ a = some x ∧ isList x = true)) →
      HWP P (gameHost I (sexpISpec pairIx ρ L)) s f (vals (us ++ [.i32 c]) ++ expression is) Q) :
    HWP P (gameHost I (sexpISpec pairIx ρ L)) s f
      (vals (us ++ [.i32 a]) ++ expression (.call ⟨0⟩ :: is)) Q :=
  X.callG hS hs hm (k := 0) (by decide) rfl rfl
    (sx_pre_of_ne hS.imports (by decide) (by decide) (.cons ⟨a, rfl⟩ .nil))
    (fun _ _ he hv res hr => by
      obtain ⟨c, rfl, h⟩ := sxKind_post hS.imports he hv hr
      exact hc c h) hQ

/-- `count(a)`. -/
theorem X.sxCount (hQ : Leaves Q s)
    (hc : ∀ c cs, ρ a = some (SExp.ofList cs) → cs.length = c.toNat →
      HWP P (gameHost I (sexpISpec pairIx ρ L)) s f (vals (us ++ [.i32 c]) ++ expression is) Q) :
    HWP P (gameHost I (sexpISpec pairIx ρ L)) s f
      (vals (us ++ [.i32 a]) ++ expression (.call ⟨1⟩ :: is)) Q :=
  X.callG hS hs hm (k := 1) (by decide) rfl rfl
    (sx_pre_of_ne hS.imports (by decide) (by decide) (.cons ⟨a, rfl⟩ .nil))
    (fun _ _ he hv res hr => by
      obtain ⟨c, rfl, cs, h₁, h₂⟩ := sxCount_post hS.imports he hv hr
      exact hc c cs h₁ h₂) hQ

/-- `child(a, i)`. -/
theorem X.sxChild {i : BitVec 32} (hQ : Leaves Q s)
    (hc : ∀ c cs x, ρ a = some (SExp.ofList cs) → cs[i.toNat]? = some x → ρ c = some x →
      HWP P (gameHost I (sexpISpec pairIx ρ L)) s f (vals (us ++ [.i32 c]) ++ expression is) Q) :
    HWP P (gameHost I (sexpISpec pairIx ρ L)) s f
      (vals (us ++ [.i32 a] ++ [.i32 i]) ++ expression (.call ⟨2⟩ :: is)) Q := by
  rw [List.append_assoc]
  exact X.callG hS hs hm (k := 2) (args := [.i32 a, .i32 i]) (by decide) rfl rfl
    (sx_pre_of_ne hS.imports (by decide) (by decide) (.cons ⟨a, rfl⟩ (.cons ⟨i, rfl⟩ .nil)))
    (fun _ _ he hv res hr => by
      obtain ⟨c, rfl, cs, x, h₁, h₂, h₃⟩ := sxChild_post hS.imports he hv hr
      exact hc c cs x h₁ h₂ h₃) hQ

/-- `word(a)`. -/
theorem X.sxWord (hQ : Leaves Q s)
    (hc : ∀ w, ρ a = some (.atom w) →
      HWP P (gameHost I (sexpISpec pairIx ρ L)) s f (vals (us ++ [.i64 w]) ++ expression is) Q) :
    HWP P (gameHost I (sexpISpec pairIx ρ L)) s f
      (vals (us ++ [.i32 a]) ++ expression (.call ⟨3⟩ :: is)) Q :=
  X.callG hS hs hm (k := 3) (by decide) rfl rfl
    (sx_pre_of_ne hS.imports (by decide) (by decide) (.cons ⟨a, rfl⟩ .nil))
    (fun _ _ he hv res hr => by
      obtain ⟨w, rfl, h⟩ := sxWord_post hS.imports he hv hr
      exact hc w h) hQ

/-- `accept(a)`, for `a` denoting a member of `L`. -/
theorem X.sxAccept (hL : ∀ t, ρ a = some t → t ∈ L) (hQ : Leaves Q s)
    (hc : HWP P (gameHost I (sexpISpec pairIx ρ L)) s f (vals us ++ expression is) Q) :
    HWP P (gameHost I (sexpISpec pairIx ρ L)) s f
      (vals (us ++ [.i32 a]) ++ expression (.call ⟨4⟩ :: is)) Q :=
  X.callG hS hs hm (k := 4) (by decide) rfl rfl (sx_pre_accept hS.imports a hL)
    (fun _ _ he _ res hr => by
      obtain rfl := sxAccept_post hS.imports he hr
      simpa using hc) hQ

end Calls

/-- The argument of `check`. -/
theorem args_aFT {args : List Val} (ht : List.Forall₂ ScalarType.HasVal aFT.params args) :
    ∃ h, args = [.i32 h] := by
  rcases ht with _ | ⟨⟨h, rfl⟩, hnil⟩
  cases hnil
  exact ⟨h, rfl⟩

/-! ## Comparisons -/

theorem rel32_eq_ne_zero {x y : BitVec 32} (h : Numerics.intRelOp .i32 .eq x y ≠ 0) : x = y := by
  have h' : bool32 (x == y) ≠ 0 := h
  exact beq_iff_eq.1 (bool32_ne_zero h')

theorem rel32_eq_zero {x y : BitVec 32} (h : Numerics.intRelOp .i32 .eq x y = 0) : x ≠ y := by
  have h' : bool32 (x == y) = 0 := h
  intro hxy
  have := bool32_eq_zero h'
  simp [hxy] at this

theorem rel32_ne_zero {x y : BitVec 32} (h : Numerics.intRelOp .i32 .ne x y = 0) : x = y := by
  have h' : bool32 (x != y) = 0 := h
  exact bne_eq_false_iff_eq.1 (bool32_eq_zero h')

end Silmaril.Proofs.Wasm.Game.HandleAccept.Nary
