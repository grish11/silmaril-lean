module

public import Silmaril.Wasm.Game.HandleAccept.Checkers.Defs
public import Silmaril.Wasm.Logic.GameLink.Thms
public import Silmaril.Wasm.Logic.Instr.Thms
public import Silmaril.Wasm.Logic.Open.Thms

/-!
# Reader checkers: shared rules

Every-run (`HWP`) rules for the instruction sequences of the checkers, stated on code of the
form `vals us ++ expression is` (the operand stack, then the remaining instructions), the import
call rule under the most general environment of the cons reader specification
(`hwp_import`, through `Open.FSpecAt.stub`), and what an allowed answer of `kind`, `car`,
`cdr`, `word` and `accept` says (`kind_post`, `car_post`, `cdr_post`, `word_post`,
`accept_post`).

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.GameLink
  Silmaril.Formats Silmaril.Formats.Api Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Checkers
open Silmaril.Wasm.Logic.Strategy (ISpec resultOutcome)
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {P : Profile} {host : HostSemantics Nat} {s : Store Nat} {f : Frame} {us : List Val}
  {is : List Instr} {Q : Post Nat}

/-! ## Straight-line rules -/

theorem X.localGet {x : LocalIdx} {v : Val} (hv : f.local? x = some (some v))
    (h : HWP P host s f (vals (us ++ [v]) ++ expression is) Q) :
    HWP P host s f (vals us ++ expression (.localGet x :: is)) Q :=
  HWP.localGet hv h

theorem X.localSet {x : LocalIdx} {v : Val} (hx : x.toNat < f.locals.length)
    (h : HWP P host s (f.setLocal x v) (vals us ++ expression is) Q) :
    HWP P host s f (vals (us ++ [v]) ++ expression (.localSet x :: is)) Q :=
  HWP.localSet hx h

theorem X.i32Const {c : BitVec 32} (h : HWP P host s f (vals (us ++ [.i32 c]) ++ expression is) Q) :
    HWP P host s f (vals us ++ expression (.intConst .i32 c :: is)) Q := by
  simpa [vals, expression, Val.i32, Val.toAdmin] using h

theorem X.eqz {c : BitVec 32}
    (h : HWP P host s f (vals (us ++ [.i32 (bool32 (c == 0))]) ++ expression is) Q) :
    HWP P host s f (vals (us ++ [.i32 c]) ++ expression (.intTestOp .i32 .eqz :: is)) Q :=
  Wp.intTestOp (m := .part) (t := .i32) (x := c) h

theorem X.neConst {x y : BitVec 32}
    (h : HWP P host s f (vals (us ++ [.i32 (bool32 (x != y))]) ++ expression is) Q) :
    HWP P host s f (vals (us ++ [.i32 x]) ++
      expression (.intConst .i32 y :: .intRelOp .i32 .ne :: is)) Q := by
  refine X.i32Const ?_
  rw [List.append_assoc]
  exact Wp.intRelOp (m := .part) (t := .i32) (x := x) (y := y) h

theorem X.les64 {x y : BitVec 64}
    (h : HWP P host s f (vals (us ++ [.i32 (bool32 (x.sle y))]) ++ expression is) Q) :
    HWP P host s f (vals (us ++ [.i64 x] ++ [.i64 y]) ++
      expression (.intRelOp .i64 (.le .signed) :: is)) Q := by
  rw [List.append_assoc]
  have he : bool32 (x.sle y) = intRelOp .i64 (.le .signed) x y := rfl
  rw [he] at h
  exact Wp.intRelOp (m := .part) (t := .i64) (x := x) (y := y) h

/-! ## Control -/

theorem X.return_ (hq : Q s f (.ret us)) : HWP P host s f (vals us ++ expression (.return_ :: is)) Q :=
  HWP.of_exits (o := .ret us) ⟨_, rfl⟩ hq

theorem X.br0 (hq : Q s f (.br 0 us)) : HWP P host s f (vals us ++ expression (.br ⟨0⟩ :: is)) Q :=
  Wp.br (m := .part) (l := ⟨0⟩) hq

/-- The end of a block body of type `[] → []`. -/
theorem X.blockEnd (h : HWP P host s f (vals us ++ expression is) Q) :
    HWP P host s f (vals [] ++ expression [])
      (labelPost P host 0 [] us (seqPost P host (expression is) Q)) := by
  refine HWP.of_vals (vs := []) ?_
  show HWP P host s f (vals (us ++ []) ++ expression is) Q
  simpa using h

/-- `if` with an empty `else`, both of block type `[] → []`. -/
theorem X.if_ {c : BitVec 32} {b : List Instr}
    (h₁ : c ≠ 0 → HWP P host s f (vals [] ++ expression b)
      (labelPost P host 0 [] us (seqPost P host (expression is) Q)))
    (h₂ : c = 0 → HWP P host s f (vals us ++ expression is) Q) :
    HWP P host s f (vals (us ++ [.i32 c]) ++ expression (.if_ .empty b [] :: is)) Q := by
  refine HWP.if_ (fun hc => ?_) (fun hc => ?_)
  · have hb := HWP.block (us := us) (vs := []) (bt := .empty) (t₁ := []) (t₂ := []) (f := f)
      (rest := expression is) rfl rfl (h₁ hc)
    rwa [List.append_nil] at hb
  · have hb := HWP.block (us := us) (vs := []) (bt := .empty) (t₁ := []) (t₂ := []) (f := f)
      (rest := expression is) (body := []) rfl rfl (X.blockEnd (h₂ hc))
    rwa [List.append_nil] at hb

/-- A loop of block type `[] → []` with an invariant on the store and the frame. -/
theorem X.loop {Inv : Store Nat → Frame → Prop} {body : List Instr}
    (hbody : ∀ s f, Inv s f → HWP P host s f (vals [] ++ expression body)
      (loopPost 0 [] (fun s f vs => vs = [] ∧ Inv s f) Q))
    (hi : Inv s f) : HWP P host s f (vals [] ++ expression [.loop .empty body]) Q :=
  HWP.loop (us := []) (vs := []) (t₁ := []) (t₂ := []) (Inv := fun s f vs => vs = [] ∧ Inv s f)
    (fun _ _ _ _ => rfl) (fun _ _ _ h => by rw [h.1]; rfl)
    (fun s f vs h => by obtain ⟨rfl, h⟩ := h; exact hbody s f h) ⟨rfl, hi⟩

/-! ## Outcomes that leave the function -/

/-- `Q` accepts every return, trap and exception in the store `s`. -/
def Leaves (Q : Post Nat) (s : Store Nat) : Prop :=
  ∀ f, (∀ vs, Q s f (.ret vs)) ∧ Q s f .trap ∧ ∀ a, Q s f (.throw a)

theorem Leaves.loop {Inv : Store Nat → Frame → List Val → Prop} (h : Leaves Q s) :
    Leaves (loopPost 0 [] Inv Q) s := fun f =>
  ⟨fun vs => (h f).1 ([] ++ vs), (h f).2.1, (h f).2.2⟩

theorem Leaves.label {rest : List Admin} (h : Leaves Q s) :
    Leaves (labelPost P host 0 [] us (seqPost P host rest Q)) s := fun f =>
  ⟨fun vs => (h f).1 (us ++ vs), (h f).2.1, (h f).2.2⟩

/-- The function body's postcondition accepts every return, trap and exception in a store
meeting the invariant. -/
theorem leaves_body {I : ScalarInstance} {Inv : Store Nat → Prop} {Ie : ISpec I.F}
    {j : Fin I.exports.length} {rs : Ty (.list .val)} (hrs : rs.length = 0) {n : Nat}
    {f₀ : Frame} {vs₀ args : List Val} {s₀ : Store Nat} (hInv : Inv s)
    (hIe : ∀ e v, Ie.post e v) :
    Leaves (bodyPostK P host rs.length f₀ vs₀
      (callPost f₀ vs₀ ((exportSpec I Inv Ie j).post s₀ args)) n) s := by
  have hR : ∀ o, (exportSpec I Inv Ie j).post s₀ args s o := fun _ => ⟨hInv, fun _ _ _ => hIe _ _⟩
  intro F
  refine ⟨fun vs => ?_, ⟨rfl, .inr (.inl ⟨rfl, hR _⟩)⟩, fun a => ⟨rfl, .inr (.inr ⟨a, rfl, hR _⟩)⟩⟩
  refine ⟨[] ++ vs, [], by simp, by simp [hrs], rfl, .inl ⟨[], by simp, hR _⟩⟩

/-! ## Import calls -/

section Import

variable {I : ScalarInstance} {Ii : ISpec I.E}

theorem importOp?_eq {k : Nat} {args : List Val} {e : I.E.Op} (he : I.importOp? k args = some e) :
    e.1.val = k ∧ e.2.1 = args := by
  unfold ScalarInstance.importOp? ifaceOp? at he
  split at he
  · split at he
    · cases he
      exact ⟨rfl, rfl⟩
    · cases he
  · cases he

/-- A call of import `k` (the host stub at address `k`, a function of one parameter) with the
argument `a`: from an allowed question, every allowed answer must make the rest safe. -/
theorem hwp_import {x : FuncIdx} {k : Nat} {fk : FuncInst Nat} {ps rs : Ty (.list .val)} {a : BitVec 32}
    (hx : f.module.funcs[x.toNat]? = some k) (hf : s.funcs[k]? = some fk) (hcode : fk.code = .host k)
    (he : Expand fk.type (.func ps rs)) (hps : ps.length = 1)
    (hop : ∃ e, I.importOp? k [.i32 a] = some e ∧ Ii.pre e)
    (hk : ∀ e (v : I.E.Ar e), I.importOp? k [.i32 a] = some e → Ii.post e v →
      ∀ res, Answer.toResult (ft := I.imports.get e.1) v = .values res →
        HWP P (gameHost I Ii) s f (vals (us ++ res) ++ expression is) Q)
    (hQ : Leaves Q s) :
    HWP P (gameHost I Ii) s f (vals (us ++ [.i32 a]) ++ expression (.call x :: is)) Q
  | 0 => trivial
  | n + 1 => by
    have hS : importCtx I Ii (id k) = some (importSpec I Ii k) := rfl
    refine Safe.callIdx (x := x) (S := Silmaril.Wasm.Logic.Open.stubSpec k k (importSpec I Ii k)) hx hf
      (Silmaril.Wasm.Logic.Open.FSpecAt.stub hS n) ⟨⟨fk, ps, rs, hf, hcode, he, by simp [hps]⟩, hop⟩ ?_
    rintro s' o ⟨-, ⟨res, rfl, hR⟩ | ⟨rfl, hR⟩ | ⟨y, rfl, hR⟩⟩
    · obtain ⟨rfl, hall⟩ := hR
      obtain ⟨e, he', -⟩ := hop
      obtain ⟨v, hv, ho⟩ := hall e he'
      have hr : Answer.toResult (ft := I.imports.get e.1) v = .values res := by
        revert ho
        cases v <;> simp [Answer.toResult, resultOutcome]
      exact hk e v he' hv res hr n
    · obtain ⟨rfl, -⟩ := hR
      exact (hQ f).2.1
    · obtain ⟨rfl, -⟩ := hR
      exact (hQ f).2.2 y

end Import

/-! ## The cons reader imports -/

/-- `[i32] → [i32]`. -/
abbrev qFT : FnType := ⟨[.num (.int .i32)], [.num (.int .i32)]⟩
/-- `[i32] → [i64]`. -/
abbrev wFT : FnType := ⟨[.num (.int .i32)], [.num (.int .i64)]⟩
/-- `[i32] → []`. -/
abbrev aFT : FnType := ⟨[.num (.int .i32)], []⟩

/-- The import types of the checkers. -/
abbrev consFTs : List FnType := [qFT, qFT, qFT, wFT, aFT]

section Cons

variable {I : ScalarInstance} (hI : I.imports = consFTs)
  {ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))} {L : Set (SExp2 (BitVec 64))}

include hI

theorem get_imports (i : Fin I.imports.length) : I.imports.get i = consFTs[i.val]'(by
    simpa [hI] using i.2) := by
  rw [List.get_eq_getElem]
  exact List.getElem_of_eq hI i.2

theorem importOp?_exists {k : Nat} (hk : k < 5) (a : BitVec 32) :
    ∃ e, I.importOp? k [.i32 a] = some e := by
  have hlt : k < I.imports.length := by simpa [hI] using hk
  have hp : (I.imports.get ⟨k, hlt⟩).params = [.num (.int .i32)] := by
    rw [get_imports hI]
    simp only
    rcases k with _ | _ | _ | _ | _ | k <;> first | rfl | omega
  have hty : List.Forall₂ ScalarType.HasVal (I.imports.get ⟨k, hlt⟩).params [.i32 a] := by
    rw [hp]
    exact .cons ⟨a, rfl⟩ .nil
  exact ⟨⟨⟨k, hlt⟩, ⟨[.i32 a], hty⟩⟩,
    by simp only [ScalarInstance.importOp?, ifaceOp?, dite_eq_left hlt, dite_eq_left hty]⟩

/-- Only `accept` has a precondition. -/
theorem pre_of_ne {k : Nat} (hk : k < 5) (h4 : k ≠ 4) (a : BitVec 32) :
    ∃ e, I.importOp? k [.i32 a] = some e ∧ (consISpec (ts := I.imports) consIx ρ L).pre e := by
  obtain ⟨e, he⟩ := importOp?_exists hI hk a
  refine ⟨e, he, fun h hd => ?_⟩
  have h1 := (importOp?_eq he).1
  simp [consDecAsk, consIx, h1, h4] at hd

/-- `accept(a)` is allowed when `a` denotes a member of `L`. -/
theorem pre_accept (a : BitVec 32) (hL : ∀ t, ρ a = some t → t ∈ L) :
    ∃ e, I.importOp? 4 [.i32 a] = some e ∧ (consISpec (ts := I.imports) consIx ρ L).pre e := by
  obtain ⟨e, he⟩ := importOp?_exists hI (k := 4) (by omega) a
  refine ⟨e, he, fun h hd => ?_⟩
  obtain ⟨h1, h2⟩ := importOp?_eq he
  simp [consDecAsk, consIx, h1, h2, i32Arg, Val.i32] at hd
  obtain rfl := hd
  exact hL

/-- The typed results of an answer of import `k`. -/
theorem results_of {e : I.E.Op} {v : I.E.Ar e} {res : List Val}
    (hr : Answer.toResult (ft := I.imports.get e.1) v = .values res) :
    List.Forall₂ ScalarType.HasVal (consFTs[e.1.val]'(by simpa [hI] using e.1.2)).results res ∧
      ansVals v = some res := by
  rcases v with ⟨vs, hvs⟩ | _ | _
  · simp only [Answer.toResult, Result.values.injEq] at hr
    subst hr
    exact ⟨get_imports hI e.1 ▸ hvs, rfl⟩
  · cases hr
  · cases hr

variable {e : I.E.Op} {v : I.E.Ar e} {a : BitVec 32} {res : List Val}

/-- An allowed answer of `kind(a)`. -/
theorem kind_post (he : I.importOp? 0 [.i32 a] = some e)
    (hv : (consISpec (ts := I.imports) consIx ρ L).post e v)
    (hr : Answer.toResult (ft := I.imports.get e.1) v = .values res) :
    ∃ c, res = [.i32 c] ∧ ((c = 0 ∧ ρ a = some .nil) ∨ (c = 1 ∧ ∃ w, ρ a = some (.atom w)) ∨
      (c = 2 ∧ ∃ x y, ρ a = some (.cons x y))) := by
  obtain ⟨h1, h2⟩ := importOp?_eq he
  obtain ⟨hty, hans⟩ := results_of hI hr
  simp only [h1] at hty
  obtain ⟨c, rfl⟩ : ∃ c, res = [.i32 c] := by
    rcases hty with _ | ⟨⟨c, rfl⟩, hnil⟩
    cases hnil
    exact ⟨c, rfl⟩
  refine ⟨c, rfl, ?_⟩
  have hd : consDecAns consIx e v = some (.read (.kind a) (kindAns c)) := by
    simp [consDecAns, consIx, h1, h2, hans, i32Arg, i32Res, Val.i32]
  obtain ⟨-, hok⟩ := hv _ _ hd
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
theorem car_post (he : I.importOp? 1 [.i32 a] = some e)
    (hv : (consISpec (ts := I.imports) consIx ρ L).post e v)
    (hr : Answer.toResult (ft := I.imports.get e.1) v = .values res) :
    ∃ c, res = [.i32 c] ∧ ∃ x y, ρ a = some (.cons x y) ∧ ρ c = some x := by
  obtain ⟨h1, h2⟩ := importOp?_eq he
  obtain ⟨hty, hans⟩ := results_of hI hr
  simp only [h1] at hty
  obtain ⟨c, rfl⟩ : ∃ c, res = [.i32 c] := by
    rcases hty with _ | ⟨⟨c, rfl⟩, hnil⟩
    cases hnil
    exact ⟨c, rfl⟩
  refine ⟨c, rfl, ?_⟩
  have hd : consDecAns consIx e v = some (.read (.car a) (.handle c)) := by
    simp [consDecAns, consIx, h1, h2, hans, i32Arg, i32Res, Val.i32]
  exact (hv _ _ hd).2

/-- An allowed answer of `cdr(a)`. -/
theorem cdr_post (he : I.importOp? 2 [.i32 a] = some e)
    (hv : (consISpec (ts := I.imports) consIx ρ L).post e v)
    (hr : Answer.toResult (ft := I.imports.get e.1) v = .values res) :
    ∃ c, res = [.i32 c] ∧ ∃ x y, ρ a = some (.cons x y) ∧ ρ c = some y := by
  obtain ⟨h1, h2⟩ := importOp?_eq he
  obtain ⟨hty, hans⟩ := results_of hI hr
  simp only [h1] at hty
  obtain ⟨c, rfl⟩ : ∃ c, res = [.i32 c] := by
    rcases hty with _ | ⟨⟨c, rfl⟩, hnil⟩
    cases hnil
    exact ⟨c, rfl⟩
  refine ⟨c, rfl, ?_⟩
  have hd : consDecAns consIx e v = some (.read (.cdr a) (.handle c)) := by
    simp [consDecAns, consIx, h1, h2, hans, i32Arg, i32Res, Val.i32]
  exact (hv _ _ hd).2

/-- An allowed answer of `word(a)`. -/
theorem word_post (he : I.importOp? 3 [.i32 a] = some e)
    (hv : (consISpec (ts := I.imports) consIx ρ L).post e v)
    (hr : Answer.toResult (ft := I.imports.get e.1) v = .values res) :
    ∃ w, res = [.i64 w] ∧ ρ a = some (.atom w) := by
  obtain ⟨h1, h2⟩ := importOp?_eq he
  obtain ⟨hty, hans⟩ := results_of hI hr
  simp only [h1] at hty
  obtain ⟨w, rfl⟩ : ∃ w, res = [.i64 w] := by
    rcases hty with _ | ⟨⟨w, rfl⟩, hnil⟩
    cases hnil
    exact ⟨w, rfl⟩
  refine ⟨w, rfl, ?_⟩
  have hd : consDecAns consIx e v = some (.read (.atom a) (.atom w)) := by
    simp [consDecAns, consIx, h1, h2, hans, i32Arg, i64Res, Val.i32, Val.i64]
  exact (hv _ _ hd).2

/-- An answer of `accept(a)` returns no values. -/
theorem accept_post (he : I.importOp? 4 [.i32 a] = some e)
    (hr : Answer.toResult (ft := I.imports.get e.1) v = .values res) : res = [] := by
  obtain ⟨h1, -⟩ := importOp?_eq he
  obtain ⟨hty, -⟩ := results_of hI hr
  simp only [h1] at hty
  exact List.forall₂_nil_left_iff.1 hty

end Cons

/-! ## Small facts -/

theorem bool32_ne_zero {b : Bool} (h : bool32 b ≠ 0) : b = true := by
  cases b
  · exact absurd rfl h
  · rfl

theorem bool32_eq_zero {b : Bool} (h : bool32 b = 0) : b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)

/-! ## Executable equality of the checkers' instructions -/

mutual
/-- Structural equality on the instructions used by the checkers; `false` elsewhere. -/
def ieq : Instr → Instr → Bool
  | .return_, .return_ => true
  | .loop bt b, .loop bt' b' => bt == bt' && ieqs b b'
  | .if_ bt t e, .if_ bt' t' e' => bt == bt' && ieqs t t' && ieqs e e'
  | .br l, .br l' => l == l'
  | .call f, .call f' => f == f'
  | .localGet x, .localGet x' | .localSet x, .localSet x' => x == x'
  | .intConst t b, .intConst t' b' => t == t' && b.toNat == b'.toNat
  | .intTestOp t o, .intTestOp t' o' => t == t' && o == o'
  | .intRelOp t o, .intRelOp t' o' => t == t' && o == o'
  | _, _ => false
/-- `ieq` on lists. -/
def ieqs : List Instr → List Instr → Bool
  | [], [] => true
  | i :: is, i' :: is' => ieq i i' && ieqs is is'
  | _, _ => false
end

theorem ieqs_sound_of {b b' : List Instr} (h : ieqs b b' = true)
    (ih : ∀ j ∈ b, ∀ j', ieq j j' = true → j = j') : b = b' := by
  induction b generalizing b' with
  | nil =>
    cases b' with
    | nil => rfl
    | cons j' js' => unfold ieqs at h; simp at h
  | cons j js ihl =>
    cases b' with
    | nil => unfold ieqs at h; simp at h
    | cons j' js' =>
      unfold ieqs at h
      simp only [Bool.and_eq_true] at h
      rw [ih j (by simp) j' h.1, ihl h.2 (fun k hk => ih k (by simp [hk]))]

theorem ieq_sound_lt : ∀ (n : Nat) (i i' : Instr), sizeOf i < n → ieq i i' = true → i = i'
  | 0, _, _, hs, _ => absurd hs (Nat.not_lt_zero _)
  | n + 1, i, i', hs, h => by
    have hlist : ∀ b b' : List Instr, sizeOf b < n → ieqs b b' = true → b = b' :=
      fun b _ hb hbb => ieqs_sound_of hbb fun j hj j' =>
        ieq_sound_lt n j j' (by have := List.sizeOf_lt_of_mem hj; omega)
    unfold ieq at h
    split at h
    all_goals (try simp only [Bool.and_eq_true, beq_iff_eq] at h)
    all_goals first
      | rfl
      | (subst h; rfl)
      | (obtain ⟨rfl, rfl⟩ := h; rfl)
      | (simp at h; done)
      | (obtain ⟨⟨rfl, h2⟩, h3⟩ := h; simp only [Instr.if_.sizeOf_spec] at hs;
         rw [hlist _ _ (by omega) h2, hlist _ _ (by omega) h3])
      | (obtain ⟨rfl, h2⟩ := h; simp only [Instr.loop.sizeOf_spec] at hs;
         rw [hlist _ _ (by omega) h2])
      | (obtain ⟨rfl, h2⟩ := h; rw [BitVec.eq_of_toNat_eq h2])
      | (obtain ⟨rfl, -⟩ := h; cases ‹IntTestOp›; cases ‹IntTestOp›; rfl)

theorem ieqs_sound {is is' : List Instr} (h : ieqs is is' = true) : is = is' :=
  ieqs_sound_of h fun _ _ _ => ieq_sound_lt _ _ _ (Nat.lt_succ_self _)

/-! ## The instantiated checkers -/

/-- A host stub for import `k`, with one parameter. -/
def stubOk (k : Nat) (fi : FuncInst Nat) : Bool :=
  (match fi.code with
    | .host k' => k' == k
    | _ => false) &&
  (match fi.type.expand? with
    | some (.func ps _) => ps.length == 1
    | _ => false)

/-- The checker function: its locals, body and type `[i32] → []`, in a module instance whose
functions are the five stubs and itself. -/
def fnOk (locals : List ValType) (body : List Instr) (D : List (Option Val)) (fi : FuncInst Nat) :
    Bool :=
  (match fi.code with
    | .wasm c => c.locals == locals && ieqs c.body body
    | _ => false) &&
  (match fi.type.expand? with
    | some (.func ps rs) => ps.length == 1 && rs.length == 0
    | _ => false) &&
  fi.module.funcs == [0, 1, 2, 3, 4, 5] &&
  locals.map (fun t => defaultVal? ((liftVal t).substAll (fi.module.types.map .dt))) == D

/-- The shape of an instantiated checker, as a boolean (checked by kernel evaluation). -/
def shapeOk (I : ScalarInstance) (locals : List ValType) (body : List Instr)
    (D : List (Option Val)) : Bool :=
  I.imports == consFTs && I.exports == [aFT] && I.addrs == [5] &&
  match I.store.funcs with
  | [f₀, f₁, f₂, f₃, f₄, f₅] => stubOk 0 f₀ && stubOk 1 f₁ && stubOk 2 f₂ && stubOk 3 f₃ &&
      stubOk 4 f₄ && fnOk locals body D f₅
  | _ => false

/-- The shape of an instantiated checker. -/
structure Shape (I : ScalarInstance) (locals : List ValType) (body : List Instr)
    (D : List (Option Val)) : Prop where
  imports : I.imports = consFTs
  exports : I.exports = [aFT]
  addr : ∀ j, I.addr j = 5
  stub : ∀ k, k < 5 → ∃ (fk : FuncInst Nat) (ps rs : Ty (.list .val)),
    I.store.funcs[k]? = some fk ∧ fk.code = .host k ∧ Expand fk.type (.func ps rs) ∧ ps.length = 1
  fn : ∃ (fi : FuncInst Nat) (code : Func) (ps rs : Ty (.list .val)),
    I.store.funcs[5]? = some fi ∧ fi.code = .wasm code ∧ code.locals = locals ∧ code.body = body ∧
    Expand fi.type (.func ps rs) ∧ ps.length = 1 ∧ rs.length = 0 ∧
    fi.module.funcs = [0, 1, 2, 3, 4, 5] ∧
    locals.map (fun t => defaultVal? ((liftVal t).substAll (fi.module.types.map .dt))) = D

theorem stubOk_spec {k : Nat} {fi : FuncInst Nat} (h : stubOk k fi = true) :
    ∃ ps rs, fi.code = .host k ∧ Expand fi.type (.func ps rs) ∧ ps.length = 1 := by
  unfold stubOk at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h₁, h₂⟩ := h
  split at h₁
  · rename_i k' hc
    split at h₂
    · rename_i ps rs he
      exact ⟨ps, rs, by rw [hc, beq_iff_eq.1 h₁], Expand.iff.2 he, beq_iff_eq.1 h₂⟩
    · cases h₂
  · cases h₁

theorem fnOk_spec {locals : List ValType} {body : List Instr} {D : List (Option Val)}
    {fi : FuncInst Nat} (h : fnOk locals body D fi = true) :
    ∃ (code : Func) (ps rs : Ty (.list .val)),
    fi.code = .wasm code ∧ code.locals = locals ∧ code.body = body ∧
    Expand fi.type (.func ps rs) ∧ ps.length = 1 ∧ rs.length = 0 ∧
    fi.module.funcs = [0, 1, 2, 3, 4, 5] ∧
    locals.map (fun t => defaultVal? ((liftVal t).substAll (fi.module.types.map .dt))) = D := by
  unfold fnOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩ := h
  split at h₁
  · rename_i c hc
    split at h₂
    · rename_i ps rs he
      simp only [Bool.and_eq_true, beq_iff_eq] at h₁ h₂ h₃ h₄
      exact ⟨c, ps, rs, hc, h₁.1, ieqs_sound h₁.2, Expand.iff.2 he, h₂.1, h₂.2, h₃, h₄⟩
    · cases h₂
  · cases h₁

theorem Shape.of_ok {I : ScalarInstance} {locals : List ValType} {body : List Instr}
    {D : List (Option Val)} (h : shapeOk I locals body D = true) : Shape I locals body D := by
  unfold shapeOk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hi, he⟩, ha⟩, hf⟩ := h
  split at hf
  · rename_i f₀ f₁ f₂ f₃ f₄ f₅ hfs
    simp only [Bool.and_eq_true] at hf
    obtain ⟨⟨⟨⟨⟨h₀, h₁⟩, h₂⟩, h₃⟩, h₄⟩, h₅⟩ := hf
    refine ⟨hi, he, fun j => ?_, fun k hk => ?_, ?_⟩
    · have hl : I.exports.length = 1 := by rw [he]; rfl
      have hj : j.val = 0 := by have := j.2; omega
      simp [ScalarInstance.addr, ha, hj]
    · rcases k with _ | _ | _ | _ | _ | k
      · obtain ⟨ps, rs, h⟩ := stubOk_spec h₀; exact ⟨f₀, ps, rs, by simp [hfs], h⟩
      · obtain ⟨ps, rs, h⟩ := stubOk_spec h₁; exact ⟨f₁, ps, rs, by simp [hfs], h⟩
      · obtain ⟨ps, rs, h⟩ := stubOk_spec h₂; exact ⟨f₂, ps, rs, by simp [hfs], h⟩
      · obtain ⟨ps, rs, h⟩ := stubOk_spec h₃; exact ⟨f₃, ps, rs, by simp [hfs], h⟩
      · obtain ⟨ps, rs, h⟩ := stubOk_spec h₄; exact ⟨f₄, ps, rs, by simp [hfs], h⟩
      · omega
    · obtain ⟨c, ps, rs, h⟩ := fnOk_spec h₅
      exact ⟨f₅, c, ps, rs, by simp [hfs], h⟩
  · cases hf

/-! ## Import calls of the instantiated checkers -/

section Calls

variable {I : ScalarInstance} {locals : List ValType} {body : List Instr} {D : List (Option Val)}
  (hS : Shape I locals body D) (hs : s.funcs = I.store.funcs)
  (hm : f.module.funcs = [0, 1, 2, 3, 4, 5])
  {ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))} {L : Set (SExp2 (BitVec 64))}
  {a : BitVec 32}

include hS hs hm

/-- A call of import `k < 5` by an instantiated checker. -/
theorem X.call {k : Nat} (hk : k < 5) {x : FuncIdx} (hx : x.toNat = k)
    (hop : ∃ e, I.importOp? k [.i32 a] = some e ∧ (consISpec (ts := I.imports) consIx ρ L).pre e)
    (hc : ∀ e (v : I.E.Ar e), I.importOp? k [.i32 a] = some e →
      (consISpec (ts := I.imports) consIx ρ L).post e v →
      ∀ res, Answer.toResult (ft := I.imports.get e.1) v = .values res →
        HWP P (gameHost I (consISpec consIx ρ L)) s f (vals (us ++ res) ++ expression is) Q)
    (hQ : Leaves Q s) :
    HWP P (gameHost I (consISpec consIx ρ L)) s f (vals (us ++ [.i32 a]) ++ expression (.call x :: is))
      Q := by
  obtain ⟨fk, ps, rs, hf, hcode, he, hps⟩ := hS.stub k hk
  refine hwp_import (fk := fk) (ps := ps) (rs := rs) ?_ (by rw [hs]; exact hf) hcode he hps hop hc hQ
  rw [hm, hx]
  rcases k with _ | _ | _ | _ | _ | k <;> first | rfl | omega

/-- `kind(a)`. -/
theorem X.kind (hQ : Leaves Q s)
    (hc : ∀ c, ((c = 0 ∧ ρ a = some .nil) ∨ (c = 1 ∧ ∃ w, ρ a = some (.atom w)) ∨
      (c = 2 ∧ ∃ x y, ρ a = some (.cons x y))) →
      HWP P (gameHost I (consISpec consIx ρ L)) s f (vals (us ++ [.i32 c]) ++ expression is) Q) :
    HWP P (gameHost I (consISpec consIx ρ L)) s f
      (vals (us ++ [.i32 a]) ++ expression (.call ⟨0⟩ :: is)) Q :=
  X.call hS hs hm (k := 0) (by omega) rfl (pre_of_ne hS.imports (by omega) (by omega) a)
    (fun _ _ he hv res hr => by
      obtain ⟨c, rfl, h⟩ := kind_post hS.imports he hv hr
      exact hc c h) hQ

/-- `car(a)`. -/
theorem X.car (hQ : Leaves Q s)
    (hc : ∀ c x y, ρ a = some (.cons x y) → ρ c = some x →
      HWP P (gameHost I (consISpec consIx ρ L)) s f (vals (us ++ [.i32 c]) ++ expression is) Q) :
    HWP P (gameHost I (consISpec consIx ρ L)) s f
      (vals (us ++ [.i32 a]) ++ expression (.call ⟨1⟩ :: is)) Q :=
  X.call hS hs hm (k := 1) (by omega) rfl (pre_of_ne hS.imports (by omega) (by omega) a)
    (fun _ _ he hv res hr => by
      obtain ⟨c, rfl, x, y, h₁, h₂⟩ := car_post hS.imports he hv hr
      exact hc c x y h₁ h₂) hQ

/-- `cdr(a)`. -/
theorem X.cdr (hQ : Leaves Q s)
    (hc : ∀ c x y, ρ a = some (.cons x y) → ρ c = some y →
      HWP P (gameHost I (consISpec consIx ρ L)) s f (vals (us ++ [.i32 c]) ++ expression is) Q) :
    HWP P (gameHost I (consISpec consIx ρ L)) s f
      (vals (us ++ [.i32 a]) ++ expression (.call ⟨2⟩ :: is)) Q :=
  X.call hS hs hm (k := 2) (by omega) rfl (pre_of_ne hS.imports (by omega) (by omega) a)
    (fun _ _ he hv res hr => by
      obtain ⟨c, rfl, x, y, h₁, h₂⟩ := cdr_post hS.imports he hv hr
      exact hc c x y h₁ h₂) hQ

/-- `word(a)`. -/
theorem X.word (hQ : Leaves Q s)
    (hc : ∀ w, ρ a = some (.atom w) →
      HWP P (gameHost I (consISpec consIx ρ L)) s f (vals (us ++ [.i64 w]) ++ expression is) Q) :
    HWP P (gameHost I (consISpec consIx ρ L)) s f
      (vals (us ++ [.i32 a]) ++ expression (.call ⟨3⟩ :: is)) Q :=
  X.call hS hs hm (k := 3) (by omega) rfl (pre_of_ne hS.imports (by omega) (by omega) a)
    (fun _ _ he hv res hr => by
      obtain ⟨w, rfl, h⟩ := word_post hS.imports he hv hr
      exact hc w h) hQ

/-- `accept(a)`, for `a` denoting a member of `L`. -/
theorem X.accept (hL : ∀ t, ρ a = some t → t ∈ L) (hQ : Leaves Q s)
    (hc : HWP P (gameHost I (consISpec consIx ρ L)) s f (vals us ++ expression is) Q) :
    HWP P (gameHost I (consISpec consIx ρ L)) s f
      (vals (us ++ [.i32 a]) ++ expression (.call ⟨4⟩ :: is)) Q :=
  X.call hS hs hm (k := 4) (by omega) rfl (pre_accept hS.imports a hL)
    (fun _ _ he _ res hr => by
      obtain rfl := accept_post hS.imports he hr
      simpa using hc) hQ

end Calls

/-! ## From the function body to the game -/

/-- The store invariant of a checker: the functions of its instantiated store. Import calls
return the store unchanged (`importSpec`) and the checkers write no store, so it holds
throughout. -/
def StoreInv (I : ScalarInstance) (s : Store Nat) : Prop := s.funcs = I.store.funcs

theorem args_of {I : ScalarInstance} (he : I.exports = [aFT]) {j : Fin I.exports.length}
    {args : List Val} (ht : List.Forall₂ ScalarType.HasVal (I.exports.get j).params args) :
    ∃ h, args = [.i32 h] := by
  have hl : I.exports.length = 1 := by rw [he]; rfl
  have hj : j.val = 0 := by have := j.2; omega
  have hg : I.exports.get j = aFT := by
    rw [List.get_eq_getElem, List.getElem_of_eq he j.2]
    simp only [hj]
    rfl
  rw [hg] at ht
  rcases ht with _ | ⟨⟨h, rfl⟩, hnil⟩
  cases hnil
  exact ⟨h, rfl⟩

/-- **A checker meets its specification** if its body does, from the frame of a call on
`[i32 h]`, for every postcondition accepting returns, traps and exceptions. -/
theorem gameSat_of {I : ScalarInstance} {locals : List ValType} {body : List Instr}
    {D : List (Option Val)} (hS : Shape I locals body D) {Ii : ISpec I.E}
    (hbody : ∀ (fi : FuncInst Nat) (s : Store Nat) (h : BitVec 32) (Q : Post Nat),
      I.store.funcs[5]? = some fi → fi.module.funcs = [0, 1, 2, 3, 4, 5] →
      s.funcs = I.store.funcs → Leaves Q s →
      HWP P (gameHost I Ii) s ⟨some (.i32 h) :: D, fi.module⟩ (vals [] ++ expression body) Q) :
    GameSat P I (StoreInv I) Ii (topISpec _) := by
  intro j
  rw [hS.addr j]
  obtain ⟨fi, code, ps, rs, hf, hcode, hloc, hbod, he, hps, hrs, hm, hD⟩ := hS.fn
  intro n
  cases n with
  | zero => exact fun _ _ _ _ _ _ _ => trivial
  | succ n =>
    refine FSpecAt.of_body (fi := fi) (fun s args hpre => by rw [hpre.1]; exact hf) hcode he
      (fun s args hpre => ?_) (fun s args hpre f₀ vs₀ => ?_)
    · obtain ⟨-, ht, -⟩ := hpre
      obtain ⟨h, rfl⟩ := args_of hS.exports ht
      simp [hps]
    · obtain ⟨hInv, ht, -⟩ := hpre
      obtain ⟨h, rfl⟩ := args_of hS.exports ht
      have hfr : Frame.forCall fi.module [.i32 h] code.locals = ⟨some (.i32 h) :: D, fi.module⟩ := by
        unfold Frame.forCall
        rw [hloc, hD]
        rfl
      rw [hfr, hbod]
      exact hbody fi s h _ hf hm hInv (leaves_body hrs hInv (fun _ _ => trivial)) n

end Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers
