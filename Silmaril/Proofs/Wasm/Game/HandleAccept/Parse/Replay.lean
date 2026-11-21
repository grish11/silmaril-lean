module

public import Silmaril.Wasm.Game.HandleAccept.Parse.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.Replay

/-!
# Parsing relations from a replayed export call

The parsing APIs are **export-side**: a tree is related to an input when an export answers a
handle (`parseDec`). `Silmaril.Wasm.Resource.replayExport` stops at the last callout and records
no export answer, so this file extends it:

* `replayFromR`, `replayExportR`: as `replayFrom`, `replayExport`, and when the interpreter stops
  without a callout at a sequence of values typed by the export's results, the export answer
  `ret j (returns vs)` (`valsOf?` reads the values back, `valsOf?_eq`);
  **`replayExportR_play`**: such a replay is a play of the instance's strategy (the export answer
  is the `oret` transition).
* `rdecE dRet pa rs`: the events of the export answers of recorded moves, decoded with the
  arguments `pa` of the pending export call; `exportEvents_pathG`: along a path,
  `exportEvents dec` is `rdecE dRet` of the recorded moves when `dec` factors through `dRet`.
* `parseRet`: `parseDec` on recorded moves (`parseDec_eq`).
* `pOkB good`, `pAcc v h`: a trace of `parse` answers naming `good` handles, accepting `(v, h)`;
  `run_of_pOkB`: if good handles are defined and not the sentinel, such a trace has a run of the
  parsing host accepting `([v], x)` for `ρ h = some x`.
* **`mem_parseRel_of_replay`**: the module's input/tree relation contains `([v], x)`, for every
  profile admitting the deterministic steps of the replay interpreter.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Parsing

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Spec Silmaril.Wasm.Verify
  Silmaril.Wasm.Validation Silmaril.Wasm.Resource Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Parsing Silmaril.Accept Silmaril.Accept.Handle
  Silmaril.Accept.Parse Silmaril.Proofs.Wasm.Game.HandleAccept.Replay
open Silmaril.Wasm.Numerics (Profile)

/-! ## Replays with the export answer -/

/-- A list of value instructions, as values. -/
def valsOf? : List Admin → Option (List Val)
  | [] => some []
  | a :: as =>
    match a.val?, valsOf? as with
    | some v, some vs => some (v :: vs)
    | _, _ => none

theorem val?_eq {a : Admin} {v : Val} (h : a.val? = some v) : a = v.toAdmin := by
  unfold Admin.val? at h
  split at h <;> cases h <;> rfl

theorem valsOf?_eq : ∀ {code : List Admin} {vs : List Val}, valsOf? code = some vs → code = vals vs
  | [], vs, h => by
    simp only [valsOf?, Option.some.injEq] at h
    subst h
    rfl
  | a :: as, vs, h => by
    simp only [valsOf?] at h
    split at h
    · rename_i v vs' hv hvs
      simp only [Option.some.injEq] at h
      subst h
      rw [val?_eq hv, valsOf?_eq hvs]
      rfl
    · cases h

/-- **The replay with the export answer** of up to `n` callouts from `c` (the `k`-th callout
first), for export `j` with result types `rts`. -/
def replayFromR (I : ScalarInstance) (sc : Script) (fuel j : Nat) (rts : List ScalarType) :
    Nat → Nat → Config Nat → List RMove
  | 0, _, _ => []
  | n + 1, k, c =>
    match runTo? fuel c with
    | none =>
      match valsOf? (Exec.runI refOracle fuel c).1.code with
      | some vs => if typedB rts vs then [.ret j (.returns vs)] else []
      | none => []
    | some (d, E, a, h, args) =>
      if argsOk I h args then
        if ansOk I d.store a h (sc k h args) then
          .ask h args :: .ans h (.returns (sc k h args)) ::
            replayFromR I sc fuel j rts n (k + 1) ⟨d.store, d.frame, E.fill (vals (sc k h args))⟩
        else [.ask h args]
      else []

/-- The replay with the export answer of the call of export `j` with candidate arguments `k`. -/
def replayExportR (I : ScalarInstance) (sc : Script) (fuel n : Nat) (j : Fin I.exports.length)
    (k : Nat) : List RMove :=
  .call j.val (candArgs k (I.exports.get j).params) ::
    replayFromR I sc fuel j.val (I.exports.get j).results n 0
      (invoke I.store (I.addr j) (candArgs k (I.exports.get j).params))

variable {I : ScalarInstance}

/-- **A replay with the export answer is a path**, from a typed running state. -/
theorem replayFromR_path {sc : Script} {fuel : Nat} {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
    (f : I.F.Op) : ∀ (n k : Nat) (s : Store Nat) (t : Thread) (ts : List CValType),
      ConfigOk (t.config s) ts → ∃ (ms : List (Move I.E I.F)) (q : I.HState),
        I.Path P (.running f s t) ms q ∧
          ms.map rmv = replayFromR I sc fuel f.1.val (I.exports.get f.1).results n k (t.config s)
  | 0, _, _, _, _, _ => ⟨[], _, .nil _, by simp [replayFromR]⟩
  | n + 1, k, s, t, ts, hok => by
    cases hr : runTo? fuel (t.config s) with
    | none =>
      have hsteps := Exec.runI_steps_typed (o := refOracle) fuel hok
      obtain ⟨s', t', hreach, hcfg⟩ := reach_of_steps' (Relation.ReflTransGen.mono hP _ _ hsteps)
      cases hv : valsOf? (Exec.runI refOracle fuel (t.config s)).1.code with
      | none => exact ⟨[], _, .nil _, by simp [replayFromR, hr, hv]⟩
      | some vs =>
        by_cases hty : typedB (I.exports.get f.1).results vs = true
        · have hfin : ResultAt s' t' (.values vs) := by
            unfold ResultAt
            rw [hcfg]
            exact valsOf?_eq hv
          have hans : Answer.ofResult? (I.exports.get f.1) (.values vs) =
              some (.values ⟨vs, typedB_sound hty⟩) := by
            rw [Answer.ofResult?]
            split
            · rfl
            · exact absurd (typedB_sound hty) ‹_›
          refine ⟨[.inr (.ans f (.values ⟨vs, typedB_sound hty⟩))], _,
            .cons (.oret hreach hfin hans) (.nil _), ?_⟩
          simp only [replayFromR, hr, hv, hty, ↓reduceIte, List.map_cons, List.map_nil]
          rfl
        · have hty' : typedB (I.exports.get f.1).results vs = false := Bool.eq_false_iff.2 hty
          refine ⟨[], _, .nil _, ?_⟩
          simp only [replayFromR, hr, hv, hty', Bool.false_eq_true, ↓reduceIte, List.map_nil]
    | some x =>
      obtain ⟨⟨ds, df, dc⟩, E, a, h, args⟩ := x
      obtain ⟨y, hdec, hy⟩ := Option.map_eq_some_iff.1 hr
      simp only [Prod.mk.injEq] at hy
      obtain ⟨hrun, rfl⟩ := hy
      have hdec' : decompose? ds dc = some (E, a, h, args) := by rw [hrun] at hdec; exact hdec
      have hsteps := Exec.runI_steps_typed (o := refOracle) fuel hok
      have hokd := Exec.runI_typed (o := refOracle) fuel hok
      rw [hrun] at hsteps hokd
      obtain ⟨s', t', hreach, hcfg⟩ := reach_of_steps' (Relation.ReflTransGen.mono hP _ _ hsteps)
      have hs' : s' = ds := by rw [← Thread.config_store s' t', hcfg]
      subst hs'
      have hco : CalloutAt s' t' h args := ⟨E, a, by rw [hcfg]; exact hdec'⟩
      by_cases hargs : argsOk I h args = true
      · obtain ⟨hi, hty⟩ := argsOk_sound hargs
        obtain ⟨e, he, he1, he2⟩ := importOp?_of_typedB hi hty
        have hev : e.1.val = h := by rw [he1]
        have step₁ : I.Trans P (.running f s t) (.inl (.ask e)) (.waiting f s' t' e) :=
          .ucall hreach hco he
        by_cases hans : ansOk I s' a h (sc k h args) = true
        · simp only [ansOk, Bool.and_eq_true] at hans
          obtain ⟨⟨ft, hft, hvs⟩, ⟨ft', hft', hvs'⟩⟩ :=
            And.intro (resultsOk_sound hans.1) (resultsOk_sound hans.2)
          have hget : I.imports.get e.1 = ft := by
            rw [he1]
            exact (List.getElem?_eq_some_iff.1 hft).2
          let v : I.E.Ar e := .values ⟨sc k h args, hget ▸ hvs⟩
          have hres : resumeResult s' t' (Answer.toResult (ft := I.imports.get e.1) v) =
              .active df (E.fill (vals (sc k h args))) := by
            rw [resumeResult_of_decompose (by rw [hcfg]; exact hdec'), hcfg]
            rfl
          have hokr : ConfigOk ⟨s', df, E.fill (vals (sc k h args))⟩ ts :=
            fill_typed hokd hdec' hft' hvs'
          obtain ⟨ms, q, hp, hms⟩ := replayFromR_path hP f n (k + 1) s'
            (.active df (E.fill (vals (sc k h args)))) ts hokr
          have step₂ : I.Trans P (.waiting f s' t' e) (.inl (.ans e v))
              (.running f s' (.active df (E.fill (vals (sc k h args))))) := by
            have := ScalarInstance.Trans.uret (P := P) (f := f) (s := s') (t := t') v
            rwa [hres] at this
          refine ⟨.inl (.ask e) :: .inl (.ans e v) :: ms, q, .cons step₁ (.cons step₂ hp), ?_⟩
          simp only [replayFromR, hr, hargs, ↓reduceIte, List.map_cons, hms, ansOk, hans.1,
            hans.2, Bool.and_self, rmv_ask, rmv_ans, hev, he2]
          rfl
        · refine ⟨[.inl (.ask e)], _, .cons step₁ (.nil _), ?_⟩
          simp only [replayFromR, hr, hargs, ↓reduceIte, hans, Bool.false_eq_true,
            List.map_cons, List.map_nil, rmv_ask, hev, he2]
      · exact ⟨[], _, .nil _, by simp [replayFromR, hr, hargs]⟩

/-- **A replay with the export answer is a play** of the instance's strategy. -/
theorem replayExportR_play (hw : I.Ok) {sc : Script} {fuel n : Nat} {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
    (j : Fin I.exports.length) (k : Nat) :
    ∃ ms ∈ I.strategy P I.store, ms.map rmv = replayExportR I sc fuel n j k := by
  let w : Typed (I.exports.get j).params :=
    ⟨candArgs k (I.exports.get j).params, candArgs_typed k _⟩
  have hinv : InvokeOk I.store (I.addr j) w.1 := invokeOk_of_wellFormed hw j w
  obtain ⟨-, -, rs, -, -, hok⟩ := invoke_ok hw.storeOk hinv
  obtain ⟨ms, q, hp, hms⟩ := replayFromR_path (sc := sc) (fuel := fuel) hP ⟨j, w⟩ n 0 I.store
    (I.initThread ⟨j, w⟩) _ hok
  refine ⟨.inr (.ask ⟨j, w⟩) :: ms, ScalarInstance.mem_strategy_iff.2 ⟨q, .cons (.call _ _) hp⟩, ?_⟩
  rw [List.map_cons, hms]
  rfl

/-! ## Decoding export answers -/

/-- The events of the export answers of recorded moves through the raw decoder `dRet j args b`;
`pa` are the arguments of the pending export call. -/
def rdecE {Ev : Type} (dRet : Nat → List Val → Behaviour Val → Option Ev) :
    List Val → List RMove → List Ev
  | _, [] => []
  | _, .call _ a :: rs => rdecE dRet a rs
  | pa, .ret j b :: rs => (dRet j pa b).toList ++ rdecE dRet pa rs
  | pa, .ask _ _ :: rs => rdecE dRet pa rs
  | pa, .ans _ _ :: rs => rdecE dRet pa rs

/-- **Decoding the export answers of a path** with a decoder factoring through a raw one, when
`pa` are the arguments of the pending export call, if any. -/
theorem exportEvents_pathG {Ev : Type} (dec : (f : I.F.Op) → I.F.Ar f → Option Ev)
    (dRet : Nat → List Val → Behaviour Val → Option Ev)
    (hDec : ∀ f v, dec f v = dRet f.1.val f.2.1 (Answer.toBehaviour (ft := I.exports.get f.1) v))
    {P : Profile} :
    ∀ {q : I.HState} {ms : List (Move I.E I.F)} {q' : I.HState}, I.Path P q ms q' →
      ∀ pa : List Val, (∀ f s t, q = .running f s t → pa = f.2.1) →
      (∀ f s t e, q = .waiting f s t e → pa = f.2.1) →
      exportEvents dec ms = rdecE dRet pa (ms.map rmv) := by
  intro q ms q' hp
  induction hp with
  | nil => intro _ _ _; rfl
  | @cons q₀ q₁ q₂ m p htr _ ih =>
    intro pa hr hw
    cases htr with
    | call s f =>
      exact ih f.2.1 (fun _ _ _ h => by cases h; rfl) (fun _ _ _ _ h => by cases h)
    | @ucall f s s' t t' h args e run callout op =>
      exact ih pa (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h; exact hr f s t rfl)
    | @uret f s t e v =>
      exact ih pa (fun _ _ _ h => by cases h; exact hw f s t e rfl) (fun _ _ _ _ h => by cases h)
    | @oret f s s' t t' r v run final answer =>
      have he : pa = f.2.1 := hr f s t rfl
      subst he
      show (dec f v).toList ++ _ = (dRet f.1.val f.2.1 _).toList ++ _
      rw [hDec]
      exact congrArg _ (ih f.2.1 (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h))

variable {V : Type}

/-- `parseDec` on a recorded answer `b` of export `j` called with `args`. -/
def parseRet (ix : ParseExports V) (j : Nat) (args : List Val) (b : Behaviour Val) :
    Option (PEv V (BitVec 32)) := do
  let vs ← bValsG b
  if ix.parse = some j then
    return .parse (← ix.val args) (← i32Res vs)
  else if ix.append = some j then
    if vs = [] then return .append (← ix.val args) else none
  else if ix.done = some j then
    return .done (← i32Res vs)
  else if ix.feed = some j then
    if vs = [] then return .feed [← ix.val args] else none
  else if ix.finish = some j then
    let (u, h) ← i32Two vs
    return .finish u.toNat h
  else if ix.reset = some j then
    if vs = [] then return .reset else none
  else none

theorem parseDec_eq (ix : ParseExports V) (f : I.F.Op) (v : I.F.Ar f) :
    parseDec ix f v =
      parseRet ix f.1.val f.2.1 (Answer.toBehaviour (ft := I.exports.get f.1) v) := by
  cases v <;> rfl

/-! ## Parsing runs -/

section Run

variable {H X : Type} [DecidableEq H]

/-- A trace of `parse` answers naming `good` handles. -/
def pOkB (good : H → Bool) : PEv V H → Bool
  | .parse _ h => good h
  | _ => false

/-- The event is the answer `h` to `parse(v)`. -/
def pAcc [DecidableEq V] (v : V) (h : H) : PEv V H → Bool
  | .parse v' h' => decide (v' = v ∧ h' = h)
  | _ => false

/-- **A trace of good `parse` answers has a run** of the parsing host in `ρ`, accepting
`([v], x)` for every answer `h` to `parse(v)` with `ρ h = some x`, when good handles are defined
in `ρ` and are not the sentinel. -/
theorem run_of_pOkB [DecidableEq V] {pol : PPolicy H} {ρ : Env H X} {good : H → Bool}
    (hg : ∀ h, good h = true → h ≠ pol.sentinel ∧ (ρ h).isSome = true) :
    ∀ t : List (PEv V H), t.all (pOkB good) = true →
      ∃ A, (parser pol ρ).Run PState.init t PState.init A ∧
        ∀ v h x, t.any (pAcc v h) = true → ρ h = some x → ([v], x) ∈ A
  | [], _ => ⟨∅, .nil _, fun _ _ _ h => by simp at h⟩
  | e :: t, hall => by
    simp only [List.all_cons, Bool.and_eq_true] at hall
    obtain ⟨B, hr, hB⟩ := run_of_pOkB hg t hall.2
    cases e with
    | parse v₀ h₀ =>
      obtain ⟨hne, hdef⟩ := hg h₀ hall.1
      obtain ⟨x₀, hx₀⟩ := Option.isSome_iff_exists.1 hdef
      have hres : resolve pol ρ [v₀] h₀ = some {([v₀], x₀)} := by
        simp [resolve, hne, hx₀]
      refine ⟨{([v₀], x₀)} ∪ B, .cons (PStep.ret rfl ⟨rfl, rfl, rfl⟩ hres) hr, ?_⟩
      intro v h x hh hx
      simp only [List.any_cons, pAcc, Bool.or_eq_true, decide_eq_true_eq] at hh
      rcases hh with ⟨rfl, rfl⟩ | hh
      · rw [hx₀] at hx
        cases hx
        exact Or.inl rfl
      · exact Or.inr (hB v h x hh hx)
    | _ => simp [pOkB] at hall

end Run

/-! ## Relations from a replay -/

/-- **A parsing pair from a replay.** If the decoded export answers of the replay (with the
export answer) of the call of export `j` (candidate arguments `k`, script `sc`) are `parse`
answers naming good handles, good handles are defined in `ρ ∈ Envs` and are not the sentinel,
and the answer to `parse(v)` is `h` with `ρ h = some x`, then `([v], x)` is in the module's
input/tree relation, for every profile admitting the deterministic steps of the replay
interpreter. Both Boolean hypotheses are decidable by kernel evaluation. -/
theorem mem_parseRel_of_replay [DecidableEq V] {m : Module} (hm : (instance? m).isSome = true)
    {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
    (ix : ParseExports V) {X : Type} (pol : PPolicy (BitVec 32))
    {Envs : Set (Env (BitVec 32) X)} {ρ : Env (BitVec 32) X} (hρ : ρ ∈ Envs)
    {good : BitVec 32 → Bool} (hg : ∀ h, good h = true → h ≠ pol.sentinel ∧ (ρ h).isSome = true)
    (sc : Script) (fuel n : Nat) (j : Fin (instOf m).exports.length) (k : Nat) (v : V)
    (h : BitVec 32) {x : X} (hx : ρ h = some x)
    (hall : (rdecE (parseRet ix) [] (replayExportR (instOf m) sc fuel n j k)).all
      (pOkB good) = true)
    (hacc : (rdecE (parseRet ix) [] (replayExportR (instOf m) sc fuel n j k)).any
      (pAcc v h) = true) :
    ([v], x) ∈ moduleParseRel P m ix pol Envs := by
  obtain ⟨mt, hI⟩ := isInstance_instOf hm
  obtain ⟨ms, hms, hmap⟩ := replayExportR_play hI.ok (sc := sc) (fuel := fuel) (n := n) hP j k
  obtain ⟨q, hp⟩ := ScalarInstance.mem_strategy_iff.1 hms
  have htr : exportEvents (parseDec ix) ms =
      rdecE (parseRet ix) [] (replayExportR (instOf m) sc fuel n j k) := by
    rw [← hmap]
    exact exportEvents_pathG (parseDec ix) (parseRet ix) (parseDec_eq ix) hp []
      (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h)
  have hT : rdecE (parseRet ix) [] (replayExportR (instOf m) sc fuel n j k) ∈
      exportTraces ((instOf m).strategy P (instOf m).store) (parseDec ix) :=
    ⟨ms, hms, htr.symm⟩
  obtain ⟨A, hrun, hA⟩ := run_of_pOkB (pol := pol) hg _ hall
  exact Set.mem_iUnion.2 ⟨⟨ρ, hρ⟩, Set.mem_biUnion hT ⟨PState.init, A, hrun, hA v h x hacc hx⟩⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Parsing
