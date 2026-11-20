module

public import Silmaril.Wasm.Game.HandleAccept.Nary.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.Replay

/-!
# N-ary reader acceptance from a replayed export call

The n-ary instance of `Silmaril.Proofs.Wasm.Game.HandleAccept.Replay`:

* `sxAsk`, `sxAns`: the decoders `sxDecAsk`, `sxDecAns` on recorded moves (`sxDecAsk_eq`,
  `sxDecAns_eq`);
* `sexpEqB`: Boolean equality of S-expressions (`sexpEqB_sound`); `sexp_list_eq_ofList`;
* `sxOkR ρ q a`: the read is valid and correctly answered in `ρ` (`sxOkR_sound`);
* **`mem_sexpLang_of_replay`**: if the decoded replay of an export call has only reads correct in
  `ρ ∈ Envs` and accepts of defined handles, and accepts `h` with `ρ h = some x`, then `x` is in
  the module's n-ary reader language, for every profile admitting the deterministic steps of
  the replay interpreter.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Nary

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Verify Silmaril.Wasm.Resource
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Nary Silmaril.Accept Silmaril.Accept.Handle Silmaril.Formats
  Silmaril.Formats.Api Silmaril.Proofs.Wasm.Game.HandleAccept.Replay
open Silmaril.Wasm.Numerics (Profile)


/-! ## S-expressions -/

/-- Boolean equality of S-expressions. -/
def sexpEqB {α : Type} [DecidableEq α] : SExp α → SExp α → Bool
  | .atom a, .atom b => decide (a = b)
  | .list n f, .list m g =>
    if h : n = m then (List.finRange n).all fun i => sexpEqB (f i) (g (i.cast h)) else false
  | _, _ => false
termination_by structural x => x

theorem sexpEqB_sound {α : Type} [DecidableEq α] {x : SExp α} :
    ∀ {y : SExp α}, sexpEqB x y = true → x = y := by
  induction x with
  | atom a =>
    intro y h
    cases y with
    | atom b =>
      simp only [sexpEqB, decide_eq_true_eq] at h
      rw [h]
    | list => simp [sexpEqB] at h
  | list n f ih =>
    intro y h
    cases y with
    | atom => simp [sexpEqB] at h
    | list m g =>
      simp only [sexpEqB] at h
      split at h
      · rename_i hnm
        subst hnm
        simp only [List.all_eq_true, List.mem_finRange, true_implies] at h
        congr 1
        funext i
        exact ih i (by simpa using h i)
      · cases h

theorem sexp_list_eq_ofList {α : Type} {n : Nat} (f : Fin n → SExp α) :
    SExp.list n f = SExp.ofList (List.ofFn f) := by
  unfold SExp.ofList
  congr 1
  · exact List.length_ofFn.symm
  · exact (Fin.heq_fun_iff List.length_ofFn.symm).2 fun i => by simp

/-! ## Decoding recorded moves -/

/-- `sxDecAsk` on a recorded import call `h args`. -/
def sxAsk (ix : SxRImports) (h : Nat) (args : List Val) : Option SxEv :=
  if h = ix.accept then (i32Arg args).map .accept else none

/-- `sxDecRead` on a recorded answer `b` of import `h` called with `args`. -/
def sxRead (ix : SxRImports) (h : Nat) (args : List Val) (b : Behaviour Val) :
    Option (SxQ (BitVec 32) × SxA (BitVec 64) (BitVec 32)) := do
  let vs ← bValsG b
  if h = ix.kind then return (.kind (← i32Arg args), sxKindAns (← i32Res vs))
  else if h = ix.count then return (.count (← i32Arg args), .count (← i32Res vs).toNat)
  else if h = ix.child then
    let (a, i) ← i32Two args
    return (.child a i.toNat, .handle (← i32Res vs))
  else if h = ix.word then return (.atom (← i32Arg args), .atom (← i64Res vs))
  else none

/-- `sxDecAns` on a recorded answer. -/
def sxAns (ix : SxRImports) (h : Nat) (args : List Val) (b : Behaviour Val) : Option SxEv :=
  (sxRead ix h args b).map fun qa => .read qa.1 qa.2

variable {I : ScalarInstance}

theorem sxDecAsk_eq (ix : SxRImports) (e : I.E.Op) : sxDecAsk ix e = sxAsk ix e.1.val e.2.1 :=
  rfl

theorem sxDecAns_eq (ix : SxRImports) (e : I.E.Op) (v : I.E.Ar e) :
    sxDecAns ix e v = sxAns ix e.1.val e.2.1 (Answer.toBehaviour (ft := I.imports.get e.1) v) := by
  cases v <;> rfl

/-! ## Correct reads -/

/-- The read is valid and correctly answered in `ρ`. -/
def sxOkR (ρ : Env (BitVec 32) (SExp (BitVec 64))) :
    SxQ (BitVec 32) → SxA (BitVec 64) (BitVec 32) → Bool
  | .kind h, .isList b =>
    match ρ h with
    | some x => decide (isList x = b)
    | none => false
  | .atom h, .atom a =>
    match ρ h with
    | some (.atom a') => decide (a' = a)
    | _ => false
  | .count h, .count n =>
    match ρ h with
    | some (.list n' _) => decide (n' = n)
    | _ => false
  | .child h i, .handle h' =>
    match ρ h with
    | some (.list n f) =>
      if hi : i < n then
        match ρ h' with
        | some c => sexpEqB c (f ⟨i, hi⟩)
        | none => false
      else false
    | _ => false
  | _, _ => false

theorem sxOkR_sound {ρ : Env (BitVec 32) (SExp (BitVec 64))} (q : SxQ (BitVec 32))
    (a : SxA (BitVec 64) (BitVec 32)) (hb : sxOkR ρ q a = true) :
    (sexpR (BitVec 64) (BitVec 32)).valid ρ q ∧ (sexpR (BitVec 64) (BitVec 32)).ok ρ q a := by
  cases q with
  | kind h =>
    cases a with
    | isList b =>
      simp only [sxOkR] at hb
      split at hb
      · rename_i x hx
        simp only [decide_eq_true_eq] at hb
        exact ⟨⟨x, hx⟩, x, hx, hb.symm⟩
      · cases hb
    | _ => simp [sxOkR] at hb
  | atom h =>
    cases a with
    | atom w =>
      simp only [sxOkR] at hb
      split at hb
      · rename_i a' hx
        simp only [decide_eq_true_eq] at hb
        subst hb
        exact ⟨⟨_, hx⟩, hx⟩
      · cases hb
    | _ => simp [sxOkR] at hb
  | count h =>
    cases a with
    | count k =>
      simp only [sxOkR] at hb
      split at hb
      · rename_i n' f hx
        simp only [decide_eq_true_eq] at hb
        subst hb
        rw [sexp_list_eq_ofList] at hx
        exact ⟨⟨_, hx⟩, _, hx, List.length_ofFn⟩
      · cases hb
    | _ => simp [sxOkR] at hb
  | child h i =>
    cases a with
    | handle h' =>
      simp only [sxOkR] at hb
      split at hb
      · rename_i n f hx
        split at hb
        · rename_i hi
          split at hb
          · rename_i c hc
            have hce := sexpEqB_sound hb
            rw [sexp_list_eq_ofList] at hx
            exact ⟨⟨_, hx, by simpa using hi⟩, _, c, hx, by simp [hce, hi], hc⟩
          · cases hb
        · cases hb
      · cases hb
    | _ => simp [sxOkR] at hb
  | items h => simp [sxOkR] at hb

/-! ## Acceptance from a replay -/

/-- **N-ary reader acceptance from a replay.** If the decoded replay of the call of export `j`
(candidate arguments `k`, script `sc`) has only reads correct in `ρ ∈ Envs` and accepts of
defined handles, and accepts the handle `h` denoting `x`, then `x` is in the module's n-ary
reader language, for every profile admitting the deterministic steps of the replay interpreter.
Both Boolean hypotheses are decidable by kernel evaluation. -/
theorem mem_sexpLang_of_replay {m : Module} (hm : (instance? m).isSome = true) {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
    (ix : SxRImports) (pol : OnBadRead (SxQ (BitVec 32)) (SxA (BitVec 64) (BitVec 32)))
    (oa : OnInvalid) {Envs : Set (Env (BitVec 32) (SExp (BitVec 64)))}
    {ρ : Env (BitVec 32) (SExp (BitVec 64))} (hρ : ρ ∈ Envs) (sc : Script) (fuel n : Nat)
    (j : Fin (instOf m).exports.length) (k : Nat) (h : BitVec 32) {x : SExp (BitVec 64)}
    (hx : ρ h = some x)
    (hall : (rdecG (some .enter) (sxAsk ix) (sxAns ix) []
      (replayExport (instOf m) sc fuel n j k)).all
      (revOkB (sxOkR ρ) fun h => (ρ h).isSome) = true)
    (hacc : (rdecG (some .enter) (sxAsk ix) (sxAns ix) []
      (replayExport (instOf m) sc fuel n j k)).any
      (revAcc h) = true) :
    x ∈ moduleSExpLang P m ix pol oa Envs :=
  mem_readerLang_of_replay hm hP (sxDecAsk ix) (sxDecAns ix) (sxAsk ix) (sxAns ix)
    (sxDecAsk_eq ix) (sxDecAns_eq ix) (sexpR (BitVec 64) (BitVec 32)) pol oa hρ sxOkR_sound
    (fun _ h => h) sc fuel n j k h hx hall hacc

end Silmaril.Proofs.Wasm.Game.HandleAccept.Nary
