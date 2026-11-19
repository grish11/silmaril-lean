module

public import Silmaril.Wasm.Game.HandleAccept.Tree2.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.Replay

/-!
# Binary-tree reader acceptance from a replayed export call

The binary-tree reader instance of `Silmaril.Proofs.Wasm.Game.HandleAccept.Replay`:

* `t2Ask`, `t2Ans`: the decoders `t2DecAsk`, `t2DecAns` on recorded moves (`t2DecAsk_eq`,
  `t2DecAns_eq`);
* `t2OkR ρ q a`: the read is valid and correctly answered in `ρ` (`t2OkR_sound`);
* **`mem_tree2Lang_of_replay`**: if the decoded replay of an export call has only reads correct
  in `ρ ∈ Envs` and accepts of defined handles, and accepts `h` with `ρ h = some x`, then `x` is
  in the module's binary-tree reader language, for every profile admitting the deterministic
  steps of the replay interpreter.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Tree2

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Verify Silmaril.Wasm.Resource
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Tree2 Silmaril.Accept Silmaril.Accept.Handle Silmaril.Formats
  Silmaril.Formats.Api Silmaril.Proofs.Wasm.Game.HandleAccept.Replay
open Silmaril.Wasm.Numerics (Profile)

/-! ## Decoding recorded moves -/

/-- `t2DecAsk` on a recorded import call `h args`. -/
def t2Ask (ix : T2RImports) (h : Nat) (args : List Val) : Option T2Ev :=
  if h = ix.accept then (i32Arg args).map .accept else none

/-- `t2DecRead` on a recorded answer `b` of import `h` called with `args`. -/
def t2Read (ix : T2RImports) (h : Nat) (args : List Val) (b : Behaviour Val) :
    Option (T2Q (BitVec 32) × T2A (BitVec 64) (BitVec 32)) := do
  let x ← i32Arg args
  let vs ← bValsG b
  if h = ix.isAtom then return (.isAtom x, isAtomAns (← i32Res vs))
  else if h = ix.left then return (.left x, .handle (← i32Res vs))
  else if h = ix.right then return (.right x, .handle (← i32Res vs))
  else if h = ix.word then return (.word x, .word (← i64Res vs))
  else none

/-- `t2DecAns` on a recorded answer. -/
def t2Ans (ix : T2RImports) (h : Nat) (args : List Val) (b : Behaviour Val) : Option T2Ev :=
  (t2Read ix h args b).map fun qa => .read qa.1 qa.2

variable {I : ScalarInstance}

theorem t2DecAsk_eq (ix : T2RImports) (e : I.E.Op) : t2DecAsk ix e = t2Ask ix e.1.val e.2.1 :=
  rfl

theorem t2DecAns_eq (ix : T2RImports) (e : I.E.Op) (v : I.E.Ar e) :
    t2DecAns ix e v = t2Ans ix e.1.val e.2.1 (Answer.toBehaviour (ft := I.imports.get e.1) v) := by
  cases v <;> rfl

/-! ## Correct reads -/

/-- The read is valid and correctly answered in `ρ`. -/
def t2OkR (ρ : Env (BitVec 32) (Tree2 (BitVec 64))) :
    T2Q (BitVec 32) → T2A (BitVec 64) (BitVec 32) → Bool
  | .isAtom h, .isAtom b =>
    match ρ h with
    | some x => decide (isAtom x = b)
    | none => false
  | .word h, .word a => decide (ρ h = some (.atom a))
  | .left h, .handle h' =>
    match ρ h with
    | some (.cons x _) => decide (ρ h' = some x)
    | _ => false
  | .right h, .handle h' =>
    match ρ h with
    | some (.cons _ y) => decide (ρ h' = some y)
    | _ => false
  | _, _ => false

theorem t2OkR_sound {ρ : Env (BitVec 32) (Tree2 (BitVec 64))} (q : T2Q (BitVec 32))
    (a : T2A (BitVec 64) (BitVec 32)) (hb : t2OkR ρ q a = true) :
    (tree2R (BitVec 64) (BitVec 32)).valid ρ q ∧ (tree2R (BitVec 64) (BitVec 32)).ok ρ q a := by
  cases q with
  | isAtom h =>
    cases a with
    | isAtom b =>
      simp only [t2OkR] at hb
      split at hb
      · rename_i x hx
        simp only [decide_eq_true_eq] at hb
        exact ⟨⟨x, hx⟩, x, hx, hb.symm⟩
      · cases hb
    | _ => simp [t2OkR] at hb
  | word h =>
    cases a with
    | word w =>
      simp only [t2OkR, decide_eq_true_eq] at hb
      exact ⟨⟨w, hb⟩, hb⟩
    | _ => simp [t2OkR] at hb
  | left h =>
    cases a with
    | handle h' =>
      simp only [t2OkR] at hb
      split at hb
      · rename_i x y hx
        simp only [decide_eq_true_eq] at hb
        exact ⟨⟨x, y, hx⟩, x, y, hx, hb⟩
      · cases hb
    | _ => simp [t2OkR] at hb
  | right h =>
    cases a with
    | handle h' =>
      simp only [t2OkR] at hb
      split at hb
      · rename_i x y hx
        simp only [decide_eq_true_eq] at hb
        exact ⟨⟨x, y, hx⟩, x, y, hx, hb⟩
      · cases hb
    | _ => simp [t2OkR] at hb

/-! ## Acceptance from a replay -/

/-- **Binary-tree reader acceptance from a replay.** If the decoded replay of the call of export
`j` (candidate arguments `k`, script `sc`) has only reads correct in `ρ ∈ Envs` and accepts of
defined handles, and accepts the handle `h` denoting `x`, then `x` is in the module's binary-tree
reader language, for every profile admitting the deterministic steps of the replay interpreter.
Both Boolean hypotheses are decidable by kernel evaluation. -/
theorem mem_tree2Lang_of_replay {m : Module} (hm : (instance? m).isSome = true) {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
    (ix : T2RImports) (pol : OnBadRead (T2Q (BitVec 32)) (T2A (BitVec 64) (BitVec 32)))
    (oa : OnInvalid) {Envs : Set (Env (BitVec 32) (Tree2 (BitVec 64)))}
    {ρ : Env (BitVec 32) (Tree2 (BitVec 64))} (hρ : ρ ∈ Envs) (sc : Script) (fuel n : Nat)
    (j : Fin (instOf m).exports.length) (k : Nat) (h : BitVec 32) {x : Tree2 (BitVec 64)}
    (hx : ρ h = some x)
    (hall : (rdecG (some .enter) (t2Ask ix) (t2Ans ix) []
      (replayExport (instOf m) sc fuel n j k)).all
      (revOkB (t2OkR ρ) fun h => (ρ h).isSome) = true)
    (hacc : (rdecG (some .enter) (t2Ask ix) (t2Ans ix) []
      (replayExport (instOf m) sc fuel n j k)).any
      (revAcc h) = true) :
    x ∈ moduleTree2Lang P m ix pol oa Envs :=
  mem_readerLang_of_replay hm hP (t2DecAsk ix) (t2DecAns ix) (t2Ask ix) (t2Ans ix)
    (t2DecAsk_eq ix) (t2DecAns_eq ix) (tree2R (BitVec 64) (BitVec 32)) pol oa hρ t2OkR_sound
    (fun _ h => h) sc fuel n j k h hx hall hacc

end Silmaril.Proofs.Wasm.Game.HandleAccept.Tree2
