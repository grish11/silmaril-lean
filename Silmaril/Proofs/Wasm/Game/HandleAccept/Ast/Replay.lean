module

public import Silmaril.Wasm.Game.HandleAccept.Ast.Examples
public import Silmaril.Proofs.Wasm.Game.HandleAccept.Replay

/-!
# AST reader acceptance from a replayed export call

The AST reader instance of `Silmaril.Proofs.Wasm.Game.HandleAccept.Replay`:

* `astAsk`, `astAns`: the decoders `astDecAsk`, `astDecAns` on recorded moves (`astDecAsk_eq`,
  `astDecAns_eq`);
* `texprEqB eq`: Boolean equality of trees, given a sound Boolean equality `eq` of node labels
  (`texprEqB_sound`); `texpr_tag_eq_ofList`; `arithTagEq` for `arithSig` (`arithTagEq_sound`);
* `astOkR eq ρ q a`: the read is valid and correctly answered in `ρ` (`astOkR_sound`);
* **`mem_astLang_of_replay`**: if the decoded replay of an export call has only reads correct in
  `ρ ∈ Envs` and accepts of defined handles, and accepts `h` with `ρ h = some x`, then `x` is in
  the module's AST reader language, for every profile admitting the deterministic steps of the
  replay interpreter.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Ast

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Verify Silmaril.Wasm.Resource
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Ast Silmaril.Accept Silmaril.Accept.Handle Silmaril.Formats
  Silmaril.Formats.Api Silmaril.Proofs.Wasm.Game.HandleAccept.Replay
  Silmaril.Wasm.Game.HandleAccept.Ast.Examples
open Silmaril.Wasm.Numerics (Profile)

/-! ## Trees -/

/-- Boolean equality of trees, given a Boolean equality of labels. -/
def texprEqB {τ : Type} (eq : τ → τ → Bool) : TExpr1 τ → TExpr1 τ → Bool
  | .tag a n f, .tag b m g =>
    eq a b && if h : n = m then (List.finRange n).all fun i => texprEqB eq (f i) (g (i.cast h))
      else false
  | _, _ => false
termination_by structural x => x

theorem texprEqB_sound {τ : Type} {eq : τ → τ → Bool} (heq : ∀ a b, eq a b = true → a = b)
    {x : TExpr1 τ} : ∀ {y : TExpr1 τ}, texprEqB eq x y = true → x = y := by
  induction x with
  | atom v => exact v.elim
  | tag a n f ih =>
    intro y h
    cases y with
    | atom v => exact v.elim
    | tag b m g =>
      simp only [texprEqB, Bool.and_eq_true] at h
      obtain ⟨hab, h⟩ := h
      cases heq a b hab
      split at h
      · rename_i hnm
        subst hnm
        simp only [List.all_eq_true, List.mem_finRange, true_implies] at h
        congr 1
        funext i
        exact ih i (by simpa using h i)
      · cases h

theorem texpr_tag_eq_ofList {τ : Type} (v : τ) {n : Nat} (f : Fin n → TExpr1 τ) :
    TExpr.tag v n f = TExpr.ofList v (List.ofFn f) := by
  unfold TExpr.ofList
  congr 1
  · exact List.length_ofFn.symm
  · exact (Fin.heq_fun_iff List.length_ofFn.symm).2 fun i => by simp

/-- Boolean equality of the labels of `arithSig`. -/
def arithTagEq : (Σ t, arithSig.toAstSig.Arg t) → (Σ t, arithSig.toAstSig.Arg t) → Bool
  | ⟨.num, a⟩, ⟨.num, b⟩ =>
    decide (Prod.fst (α := Int64) (β := Unit) a = Prod.fst (α := Int64) (β := Unit) b)
  | ⟨.add, _⟩, ⟨.add, _⟩ => true
  | ⟨.neg, _⟩, ⟨.neg, _⟩ => true
  | _, _ => false

theorem arithTagEq_sound (a b : Σ t, arithSig.toAstSig.Arg t) (h : arithTagEq a b = true) :
    a = b := by
  obtain ⟨t, a⟩ := a
  obtain ⟨t', b⟩ := b
  cases t <;> cases t' <;> simp only [arithTagEq, Bool.false_eq_true] at h
  · have hab := of_decide_eq_true h
    obtain ⟨a, ⟨⟩⟩ := (a : Int64 × Unit)
    obtain ⟨b, ⟨⟩⟩ := (b : Int64 × Unit)
    cases hab
    rfl
  · cases a; cases b; rfl
  · cases a; cases b; rfl

/-! ## Decoding recorded moves -/

variable {S : WitSig}

/-- `astDecAsk` on a recorded import call `h args`. -/
def astAsk (ix : AstRImports S) (h : Nat) (args : List Val) : Option (AstEv S) :=
  if h = ix.accept then (i32Arg args).map .accept else none

/-- `astDecRead` on a recorded answer `b` of import `h` called with `args`. -/
def astRead (ix : AstRImports S) (h : Nat) (args : List Val) (b : Behaviour Val) :
    Option (AstQ (BitVec 32) × AstA S.toAstSig (BitVec 32)) := do
  let vs ← bValsG b
  if h = ix.tag then return (.tag (← i32Arg args), .tag (← decTag ix vs))
  else if h = ix.count then return (.count (← i32Arg args), .count (← i32Res vs).toNat)
  else if h = ix.child then
    match args with
    | [.num ⟨.int .i32, h⟩, .num ⟨.int .i32, i⟩] => return (.child h i.toNat, .handle (← i32Res vs))
    | _ => none
  else none

/-- `astDecAns` on a recorded answer. -/
def astAns (ix : AstRImports S) (h : Nat) (args : List Val) (b : Behaviour Val) :
    Option (AstEv S) :=
  (astRead ix h args b).map fun qa => .read qa.1 qa.2

variable {I : ScalarInstance}

theorem astDecAsk_eq (ix : AstRImports S) (e : I.E.Op) :
    astDecAsk ix e = astAsk ix e.1.val e.2.1 :=
  rfl

theorem astDecAns_eq (ix : AstRImports S) (e : I.E.Op) (v : I.E.Ar e) :
    astDecAns ix e v =
      astAns ix e.1.val e.2.1 (Answer.toBehaviour (ft := I.imports.get e.1) v) := by
  cases v <;> rfl

/-! ## Correct reads -/

/-- The read is valid and correctly answered in `ρ` (labels compared by `eq`). -/
def astOkR (eq : (Σ t, S.toAstSig.Arg t) → (Σ t, S.toAstSig.Arg t) → Bool)
    (ρ : Env (BitVec 32) (AST S.toAstSig)) :
    AstQ (BitVec 32) → AstA S.toAstSig (BitVec 32) → Bool
  | .tag h, .tag v =>
    match ρ h with
    | some (.tag v' _ _) => eq v' v
    | _ => false
  | .count h, .count k =>
    match ρ h with
    | some (.tag _ n _) => decide (n = k)
    | _ => false
  | .child h i, .handle h' =>
    match ρ h with
    | some (.tag _ n f) =>
      if hi : i < n then
        match ρ h' with
        | some c => texprEqB eq c (f ⟨i, hi⟩)
        | none => false
      else false
    | _ => false
  | _, _ => false

theorem astOkR_sound {eq : (Σ t, S.toAstSig.Arg t) → (Σ t, S.toAstSig.Arg t) → Bool}
    (heq : ∀ a b, eq a b = true → a = b) {ρ : Env (BitVec 32) (AST S.toAstSig)}
    (q : AstQ (BitVec 32)) (a : AstA S.toAstSig (BitVec 32)) (hb : astOkR eq ρ q a = true) :
    (astR S.toAstSig (BitVec 32)).valid ρ q ∧ (astR S.toAstSig (BitVec 32)).ok ρ q a := by
  cases q with
  | tag h =>
    cases a with
    | tag v =>
      simp only [astOkR] at hb
      split at hb
      · rename_i v' n f hx
        cases heq _ _ hb
        rw [texpr_tag_eq_ofList] at hx
        exact ⟨⟨_, hx⟩, _, hx⟩
      · cases hb
    | _ => simp [astOkR] at hb
  | count h =>
    cases a with
    | count k =>
      simp only [astOkR] at hb
      split at hb
      · rename_i v n f hx
        simp only [decide_eq_true_eq] at hb
        subst hb
        rw [texpr_tag_eq_ofList] at hx
        exact ⟨⟨_, hx⟩, _, _, hx, List.length_ofFn⟩
      · cases hb
    | _ => simp [astOkR] at hb
  | child h i =>
    cases a with
    | handle h' =>
      simp only [astOkR] at hb
      split at hb
      · rename_i v n f hx
        split at hb
        · rename_i hi
          split at hb
          · rename_i c hc
            have hce := texprEqB_sound heq hb
            rw [texpr_tag_eq_ofList] at hx
            exact ⟨⟨_, _, hx, by simpa using hi⟩, _, _, c, hx, by simp [hce, hi], hc⟩
          · cases hb
        · cases hb
      · cases hb
    | _ => simp [astOkR] at hb

/-! ## Acceptance from a replay -/

/-- **AST reader acceptance from a replay.** If the decoded replay of the call of export `j`
(candidate arguments `k`, script `sc`) has only reads correct in `ρ ∈ Envs` (labels compared by
the sound `eq`) and accepts of defined handles, and accepts the handle `h` denoting `x`, then `x`
is in the module's AST reader language, for every profile admitting the deterministic steps of
the replay interpreter. Both Boolean hypotheses are decidable by kernel evaluation. -/
theorem mem_astLang_of_replay {m : Module} (hm : (instance? m).isSome = true) {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
    (ix : AstRImports S) (pol : OnBadRead (AstQ (BitVec 32)) (AstA S.toAstSig (BitVec 32)))
    (oa : OnInvalid) {Envs : Set (Env (BitVec 32) (AST S.toAstSig))}
    {ρ : Env (BitVec 32) (AST S.toAstSig)} (hρ : ρ ∈ Envs)
    {eq : (Σ t, S.toAstSig.Arg t) → (Σ t, S.toAstSig.Arg t) → Bool}
    (heq : ∀ a b, eq a b = true → a = b) (sc : Script) (fuel n : Nat)
    (j : Fin (instOf m).exports.length) (k : Nat) (h : BitVec 32) {x : AST S.toAstSig}
    (hx : ρ h = some x)
    (hall : (rdecG (some .enter) (astAsk ix) (astAns ix) []
      (replayExport (instOf m) sc fuel n j k)).all
      (revOkB (astOkR eq ρ) fun h => (ρ h).isSome) = true)
    (hacc : (rdecG (some .enter) (astAsk ix) (astAns ix) []
      (replayExport (instOf m) sc fuel n j k)).any
      (revAcc h) = true) :
    x ∈ moduleAstLang P m ix pol oa Envs :=
  mem_readerLang_of_replay hm hP (astDecAsk ix) (astDecAns ix) (astAsk ix) (astAns ix)
    (astDecAsk_eq ix) (astDecAns_eq ix) (astR S.toAstSig (BitVec 32)) pol oa hρ
    (astOkR_sound heq) (fun _ h => h) sc fuel n j k h hx hall hacc

end Silmaril.Proofs.Wasm.Game.HandleAccept.Ast
