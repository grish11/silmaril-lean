module

public import Silmaril.Wasm.Game.HandleAccept.Defs
public import Silmaril.Wasm.Resource.Replay.Thms
public import Silmaril.Wasm.Verify.Check.Thms
public import Silmaril.Wasm.Game.Instantiate.Thms
public import Silmaril.Wasm.Game.Strategy.Thms

/-!
# Reader acceptance from a replayed export call

A replay of an export call (`Silmaril.Wasm.Resource.replayExport`, the verified interpreter with
scripted import answers) is a play of the instance's strategy (`replayExport_play`). This file
decodes the recorded moves into cons reader events and gives a kernel-checkable sufficient
condition for a tree to lie in a module's reader language:

* `rdec ix pa rs`: the cons reader events of the recorded moves `rs` (`RMove`), the answer of an
  import call decoded with the arguments of the call before it (`pa`: the pending arguments);
  `playEvents_path`: along a path of the instance's transition system, the decoded events of the
  play (`playEvents (some .enter) (consDecAsk ix) (consDecAns ix)`) are those of its recorded
  moves; a replay starts with its export call, so its trace starts with `enter`.
* `consOkB ρ e`: the event `e` is correct in the environment `ρ` (a read is valid and correctly
  answered, an accepted handle is defined, an export call); `run_of_consOkB`: a trace of
  correct events has a run of the reader host in `ρ`, under every read and accept policy,
  accepting every tree denoted by an accepted handle.
* **`mem_consLang_of_replay`**: if the decoded replay of an export call is correct in `ρ ∈ Envs`
  and accepts the handle `h` with `ρ h = some x`, then `x` is in the module's reader language,
  for every profile admitting the deterministic steps of the replay interpreter.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Verify Silmaril.Wasm.Resource
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game.HandleAccept
  Silmaril.Accept Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api
open Silmaril.Wasm.Numerics (Profile)

/-! ## Decoding recorded moves -/

/-- The returned values of a behaviour. -/
def bVals : Behaviour Val → Option (List Val)
  | .returns vs => some vs
  | _ => none

/-- `consDecAsk` on a recorded import call `h args`. -/
def rAsk (ix : ConsImports) (h : Nat) (args : List Val) : Option ConsEv :=
  if h = ix.accept then (i32Arg args).map .accept else none

/-- `consDecAns` on a recorded answer `b` of import `h` called with `args`. -/
def rAns (ix : ConsImports) (h : Nat) (args : List Val) (b : Behaviour Val) : Option ConsEv := do
  let x ← i32Arg args
  let vs ← bVals b
  if h = ix.kind then return .read (.kind x) (kindAns (← i32Res vs))
  else if h = ix.car then return .read (.car x) (.handle (← i32Res vs))
  else if h = ix.cdr then return .read (.cdr x) (.handle (← i32Res vs))
  else if h = ix.word then return .read (.atom x) (.atom (← i64Res vs))
  else none

/-- The cons reader events of recorded moves (export calls as `enter`); `pa` are the arguments of
the pending call. -/
def rdec (ix : ConsImports) : List Val → List RMove → List ConsEv
  | _, [] => []
  | _, .ask h a :: rs => (rAsk ix h a).toList ++ rdec ix a rs
  | pa, .ans h b :: rs => (rAns ix h pa b).toList ++ rdec ix pa rs
  | pa, .call _ _ :: rs => .enter :: rdec ix pa rs
  | pa, .ret _ _ :: rs => rdec ix pa rs

variable {I : ScalarInstance}

theorem consDecAns_eq (ix : ConsImports) (e : I.E.Op) (v : I.E.Ar e) :
    consDecAns ix e v = rAns ix e.1.val e.2.1 (Answer.toBehaviour (ft := I.imports.get e.1) v) := by
  cases v <;> rfl

/-- **Decoding a path**: the decoded events of a play read off a path are those of its recorded
moves, when the pending arguments `pa` are those of the pending import call, if any. -/
theorem playEvents_path (ix : ConsImports) {P : Profile} :
    ∀ {q : I.HState} {ms : List (Move I.E I.F)} {q' : I.HState}, I.Path P q ms q' →
      ∀ pa : List Val, (∀ f s t e, q = .waiting f s t e → pa = e.2.1) →
      playEvents (some .enter) (consDecAsk ix) (consDecAns ix) ms = rdec ix pa (ms.map rmv) := by
  intro q ms q' hp
  induction hp with
  | nil => intro _ _; rfl
  | @cons q₀ q₁ q₂ m p htr _ ih =>
    intro pa hpa
    cases htr with
    | call s f =>
      exact congrArg (List.cons .enter) (ih pa fun _ _ _ _ h => by cases h)
    | @ucall f s s' t t' h args e run callout op =>
      show (consDecAsk ix e).toList ++ _ = (rAsk ix e.1.val e.2.1).toList ++ _
      exact congrArg _ (ih e.2.1 fun _ _ _ _ h => by cases h; rfl)
    | @uret f s t e v =>
      have he : pa = e.2.1 := hpa f s t e rfl
      subst he
      show (consDecAns ix e v).toList ++ _ = (rAns ix e.1.val e.2.1 _).toList ++ _
      rw [consDecAns_eq]
      exact congrArg _ (ih e.2.1 fun _ _ _ _ h => by cases h)
    | oret run final answer =>
      exact ih pa fun _ _ _ _ h => by cases h

/-! ## Correct events and reader runs -/

/-- The event is correct in `ρ`: a valid, correctly answered read, or the accept of a defined
handle. -/
def consOkB (ρ : Env (BitVec 32) (SExp2 (BitVec 64))) : ConsEv → Bool
  | .read (.kind h) (.kind k) =>
    match ρ h with
    | some t => decide (consKind t = k)
    | none => false
  | .read (.atom h) (.atom a) => decide (ρ h = some (.atom a))
  | .read (.car h) (.handle h') =>
    match ρ h with
    | some (.cons x _) => decide (ρ h' = some x)
    | _ => false
  | .read (.cdr h) (.handle h') =>
    match ρ h with
    | some (.cons _ y) => decide (ρ h' = some y)
    | _ => false
  | .accept h => (ρ h).isSome
  | .enter => true
  | _ => false

/-- The event accepts the handle `h`. -/
def accIs (h : BitVec 32) : ConsEv → Bool
  | .accept h' => decide (h' = h)
  | _ => false

theorem consOkB_read {ρ : Env (BitVec 32) (SExp2 (BitVec 64))} {q : ConsQ (BitVec 32)}
    {a : ConsA (BitVec 64) (BitVec 32)} (hb : consOkB ρ (.read q a) = true) :
    (consR (BitVec 64) (BitVec 32)).valid ρ q ∧ (consR (BitVec 64) (BitVec 32)).ok ρ q a := by
  cases q with
  | kind h =>
    cases a with
    | kind k =>
      cases hρ : ρ h with
      | none => simp [consOkB, hρ] at hb
      | some t =>
        simp only [consOkB, hρ, decide_eq_true_eq] at hb
        exact ⟨⟨t, hρ⟩, t, hρ, hb.symm⟩
    | atom _ => simp [consOkB] at hb
    | handle _ => simp [consOkB] at hb
  | atom h =>
    cases a with
    | atom w =>
      simp only [consOkB, decide_eq_true_eq] at hb
      exact ⟨⟨w, hb⟩, hb⟩
    | kind _ => simp [consOkB] at hb
    | handle _ => simp [consOkB] at hb
  | car h =>
    cases a with
    | handle h' =>
      cases hρ : ρ h with
      | none => simp [consOkB, hρ] at hb
      | some t =>
        cases t with
        | cons x y =>
          simp only [consOkB, hρ, decide_eq_true_eq] at hb
          exact ⟨⟨x, y, hρ⟩, x, y, hρ, hb⟩
        | nil => simp [consOkB, hρ] at hb
        | atom _ => simp [consOkB, hρ] at hb
    | kind _ => simp [consOkB] at hb
    | atom _ => simp [consOkB] at hb
  | cdr h =>
    cases a with
    | handle h' =>
      cases hρ : ρ h with
      | none => simp [consOkB, hρ] at hb
      | some t =>
        cases t with
        | cons x y =>
          simp only [consOkB, hρ, decide_eq_true_eq] at hb
          exact ⟨⟨x, y, hρ⟩, x, y, hρ, hb⟩
        | nil => simp [consOkB, hρ] at hb
        | atom _ => simp [consOkB, hρ] at hb
    | kind _ => simp [consOkB] at hb
    | atom _ => simp [consOkB] at hb

/-- **A correct trace has a reader run** in `ρ` (every read and accept policy), accepting every
tree denoted by an accepted handle. -/
theorem run_of_consOkB {ρ : Env (BitVec 32) (SExp2 (BitVec 64))}
    {pol : OnBadRead (ConsQ (BitVec 32)) (ConsA (BitVec 64) (BitVec 32))} {oa : OnInvalid} :
    ∀ t : List ConsEv, t.all (consOkB ρ) = true →
      ∃ A, (reader (consR (BitVec 64) (BitVec 32)) pol oa ρ).Run .live t .live A ∧
        ∀ h x, t.any (accIs h) = true → ρ h = some x → x ∈ A
  | [], _ => ⟨∅, .nil _, fun _ _ h => by simp at h⟩
  | e :: t, hall => by
    simp only [List.all_cons, Bool.and_eq_true] at hall
    obtain ⟨B, hr, hB⟩ := run_of_consOkB t hall.2
    cases e with
    | read q a =>
      obtain ⟨hv, hok⟩ := consOkB_read hall.1
      have hans : answers (consR (BitVec 64) (BitVec 32)) pol ρ q =
          some {a | (consR (BitVec 64) (BitVec 32)).ok ρ q a} := by
        unfold answers
        split
        · rfl
        · contradiction
      refine ⟨∅ ∪ B, .cons (RStep.read hans hok) hr, fun h x hh hx => ?_⟩
      simp only [List.any_cons, accIs, Bool.false_or] at hh
      exact Or.inr (hB h x hh hx)
    | accept h' =>
      obtain ⟨t₀, ht₀⟩ := Option.isSome_iff_exists.1 hall.1
      refine ⟨{t₀} ∪ B, .cons (RStep.acceptOk ht₀) hr, fun h x hh hx => ?_⟩
      simp only [List.any_cons, accIs, Bool.or_eq_true, decide_eq_true_eq] at hh
      rcases hh with rfl | hh
      · rw [ht₀] at hx
        cases hx
        exact Or.inl rfl
      · exact Or.inr (hB h x hh hx)
    | enter =>
      refine ⟨∅ ∪ B, .cons RStep.enter hr, fun h x hh hx => ?_⟩
      simp only [List.any_cons, accIs, Bool.false_or] at hh
      exact Or.inr (hB h x hh hx)

/-! ## Acceptance from a replay -/

/-- **Acceptance from a replay.** If the decoded replay of the call of export `j` (candidate
arguments `k`, script `sc`) is correct in `ρ ∈ Envs` and accepts the handle `h` denoting `x`,
then `x` is in the module's reader language, for every profile `P` admitting the deterministic
steps of the replay interpreter. Both Boolean hypotheses are decidable by kernel evaluation. -/
theorem mem_consLang_of_replay {m : Module} (hm : (instance? m).isSome = true) {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
    (ix : ConsImports) (pol : OnBadRead (ConsQ (BitVec 32)) (ConsA (BitVec 64) (BitVec 32)))
    (oa : OnInvalid) {Envs : Set (Env (BitVec 32) (SExp2 (BitVec 64)))}
    {ρ : Env (BitVec 32) (SExp2 (BitVec 64))} (hρ : ρ ∈ Envs) (sc : Script) (fuel n : Nat)
    (j : Fin (instOf m).exports.length) (k : Nat) (h : BitVec 32) {x : SExp2 (BitVec 64)}
    (hx : ρ h = some x)
    (hall : (rdec ix [] (replayExport (instOf m) sc fuel n j k)).all (consOkB ρ) = true)
    (hacc : (rdec ix [] (replayExport (instOf m) sc fuel n j k)).any (accIs h) = true) :
    x ∈ moduleConsLang P m ix pol oa Envs := by
  obtain ⟨mt, hI⟩ := isInstance_instOf hm
  obtain ⟨ms, hms, hmap⟩ := replayExport_play hI.ok (sc := sc) (fuel := fuel) (n := n) hP j k
  obtain ⟨q, hp⟩ := ScalarInstance.mem_strategy_iff.1 hms
  have htr : playEvents (some .enter) (consDecAsk ix) (consDecAns ix) ms =
      rdec ix [] (replayExport (instOf m) sc fuel n j k) := by
    rw [← hmap]
    exact playEvents_path ix hp [] fun _ _ _ _ h => by cases h
  obtain ⟨A, hrun, hA⟩ := run_of_consOkB (pol := pol) (oa := oa) _ hall
  have hT : rdec ix [] (replayExport (instOf m) sc fuel n j k) ∈
      handleTraces ((instOf m).strategy P (instOf m).store) (some .enter) (consDecAsk ix)
        (consDecAns ix) :=
    ⟨ms, hms, htr.symm⟩
  exact Set.mem_iUnion.2 ⟨⟨ρ, hρ⟩, Set.mem_biUnion hT ⟨.live, A, hrun, hA h x hacc hx⟩⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers
