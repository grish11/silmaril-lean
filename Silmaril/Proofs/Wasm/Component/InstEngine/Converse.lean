module

public import Silmaril.Proofs.Wasm.Component.InstEngine.Basic
public import Silmaril.Proofs.Wasm.Component.InstSem.Plays

/-!
# The engine semantics with an instantiation phase: the export phase exactly

The converse of `engine_after_start`: every play of `engineStrategyI` that has passed a
successful instantiation is, after it, a play of `engineStrategy` from a store some start run
with the same import calls returns at.

* `run_ready_inv`: from `ready x`, the transition system moves as `engineLTS` (lifted);
* `run_starting_inv`: a run from `starting` through the calls `cs` and `ready` is a start run
  (`StartRunI`) returning values, followed by a run from `ready (idle s')`;
* `mem_after_of_inv`: the plays of a strategy of a transition system after a fixed Proponent
  prefix, from run inversions;
* `engine_after_start_iff`, `engine_after_noStart_iff`, `engine_noInst_not_ready`: the plays
  after instantiation, exactly.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.InstEngine

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.InstSem
open Silmaril.Wasm.Game (liftMove liftEv)

/-! ## Lifted moves -/

section Lift

variable {X F : Sig.{0}} {R : Type}

theorem liftMove_injective : Function.Injective (liftMove (E := X) (F := F) (R := R)) := by
  intro a b h
  rcases a with a | (⟨q⟩ | ⟨q, n⟩) <;> rcases b with b | (⟨q'⟩ | ⟨q', n'⟩) <;>
    simp only [liftMove, liftEv, Sum.map_inl, Sum.map_inr, id_eq, Sum.inl.injEq, Sum.inr.injEq,
      reduceCtorEq] at h
  · exact congrArg _ h
  · cases h; rfl
  · cases h; rfl

theorem isO_of_liftMove {o : Move X F} (h : (liftMove (R := R) o).IsO) : o.IsO := by
  rcases o with (_ | _) | (_ | _) <;> exact h

theorem map_liftMove_eq_nil {p : List (Move X F)} (h : p.map (liftMove (R := R)) = []) : p = [] :=
  List.map_eq_nil_iff.1 h

/-- **The plays of a transition system after a fixed prefix**: if the prefix `pre` is a
complete exchange ending in a Proponent move, and every run through `pre` followed by lifted
moves `p` yields a trace `p` of some `Lx a` with `A a`, then every play `pre ++ p` (lifted) of
the strategy gives a play `p` of some `Lx a`. -/
theorem mem_after_of_inv {L : LTS X (F.withInst R)} {α : Type} (Lx : α → LTS X F)
    (A : α → Prop) {pre : List (Move X (F.withInst R))} (hpath : Path .idle pre .idle)
    (hlast : ∃ pre₀ m, pre = pre₀ ++ [m] ∧ m.IsP)
    (hinv : ∀ {p : List (Move X F)} {z}, L.Run L.init (pre ++ p.map liftMove) z →
      ∃ a, A a ∧ p ∈ (Lx a).Traces)
    {p : List (Move X F)} (h : pre ++ p.map liftMove ∈ Strategy.ofLTS L) :
    ∃ a, A a ∧ p ∈ Strategy.ofLTS (Lx a) := by
  obtain ⟨pre₀, m, rfl, hm⟩ := hlast
  have hlegal : Legal (pre₀ ++ [m] ++ p.map liftMove) := (Strategy.ofLTS L).legal h
  -- the moves after the prefix are a legal play
  have hlift : ∀ {p' : List (Move X F)} {z}, Path .idle (pre₀ ++ [m] ++ p'.map liftMove) z →
      ∃ z', Path .idle p' z' := by
    intro p' z hz
    obtain ⟨y, hy, hy'⟩ := Path.of_append hz
    obtain rfl := Path.det hy hpath
    exact path_of_lift (R := R) (x := .idle) hy'
  -- every play is a trace, or a trace followed by an Opponent move
  have hcases : pre₀ ++ [m] ++ p.map liftMove ∈ L.Traces ∨
      ∃ p₀ o, pre₀ ++ [m] ++ p.map liftMove = p₀ ++ [o] ∧ p₀ ∈ L.Traces ∧ o.IsO := by
    obtain ⟨-, u, hu, hp⟩ := Strategy.mem_generate.1 h
    rcases hu with rfl | ⟨hu, -⟩
    · rcases hp with hp | ⟨p₀, o, he, hp₀, ho⟩
      · have := List.prefix_nil.1 hp
        simp at this
      · obtain rfl := List.prefix_nil.1 hp₀
        exact .inr ⟨[], o, he, ⟨_, .nil _⟩, ho⟩
    · rcases hp with hp | ⟨p₀, o, he, hp₀, ho⟩
      · exact .inl (LTS.traces_of_prefix hu hp)
      · exact .inr ⟨p₀, o, he, LTS.traces_of_prefix hu hp₀, ho⟩
  rcases hcases with ⟨z, hz⟩ | ⟨p₀, o, he, ⟨z, hz⟩, ho⟩
  · obtain ⟨a, ha, hp⟩ := hinv hz
    obtain ⟨_, hpz⟩ := hlegal
    exact ⟨a, ha, Strategy.mem_ofLTS_of_mem_traces hp (hlift hpz)⟩
  · -- the last move is an Opponent move after the prefix
    rcases List.eq_nil_or_concat' p with rfl | ⟨p₁, o', rfl⟩
    · simp only [List.map_nil, List.append_nil] at he
      obtain ⟨-, h1⟩ := List.append_inj' he rfl
      obtain rfl : m = o := by simpa using h1
      exact (Move.not_isO_of_isP hm ho).elim
    · simp only [List.map_append, List.map_cons, List.map_nil, ← List.append_assoc] at he
      obtain ⟨rfl, ho'⟩ := List.append_inj' he rfl
      obtain rfl : o = liftMove o' := by simpa using ho'.symm
      obtain ⟨a, ha, hp₁⟩ := hinv hz
      refine ⟨a, ha, ?_⟩
      obtain ⟨_, hpz⟩ := hlegal
      obtain ⟨_, hpath'⟩ := hlift (p' := p₁ ++ [o']) (by simpa only [List.map_append,
        List.map_cons, List.map_nil, List.append_assoc] using hpz)
      obtain ⟨x, hx, hxo⟩ := Path.concat_iff.1 hpath'
      exact (Strategy.ofLTS (Lx a)).receptive
        (Strategy.mem_ofLTS_of_mem_traces hp₁ ⟨x, hx⟩) hx hxo (isO_of_liftMove ho)

end Lift

/-- A play of `Strategy.ofLTS L` ending in a Proponent move is a trace of `L`. -/
theorem trace_of_mem_ofLTS {X F : Sig.{0}} {L : LTS X F} {s : List (Move X F)} {o : Move X F}
    (h : s ++ [o] ∈ Strategy.ofLTS L) (ho : o.IsP) : s ++ [o] ∈ L.Traces := by
  obtain ⟨-, u, hu, hp⟩ := Strategy.mem_generate.1 h
  have hO : ∀ p₀ o', s ++ [o] = p₀ ++ [o'] → ¬ o'.IsO := by
    intro p₀ o' he
    obtain ⟨-, h'⟩ := List.append_inj' he rfl
    obtain rfl : o = o' := by simpa using h'
    exact Move.not_isO_of_isP ho
  rcases hu with rfl | ⟨hu, -⟩
  · rcases hp with hp | ⟨p₀, o', he, -, ho'⟩
    · simpa using hp.length_le
    · exact (hO p₀ o' he ho').elim
  · rcases hp with hp | ⟨p₀, o', he, -, ho'⟩
    · exact LTS.traces_of_prefix hu hp
    · exact (hO p₀ o' he ho').elim

/-! ## Run inversions -/

/-- The first step of a run. -/
theorem run_cases {X F : Sig.{0}} {L : LTS X F} {x z : L.State} {l : List (Move X F)}
    (h : L.Run x l z) :
    (l = [] ∧ z = x) ∨ (∃ y, L.step x none y ∧ L.Run y l z) ∨
      ∃ o s y, l = o :: s ∧ L.step x (some o) y ∧ L.Run y s z := by
  cases h with
  | nil => exact .inl ⟨rfl, rfl⟩
  | tau hs hr => exact .inr (.inl ⟨_, hs, hr⟩)
  | vis hs hr => exact .inr (.inr ⟨_, _, _, rfl, hs, hr⟩)

variable {E : Engine} {I : Option (IInstance E)} {imps exps : CoreIface}

/-- **From `ready x` the moves are those of `engineLTS`, lifted.** -/
theorem run_ready_inv (s : E.Store Nat) :
    ∀ (l : List (Move (sigN imps.length) ((sigN exps.length).withInst Unit)))
      {x : EState E imps.length exps.length} {z : IState E imps.length exps.length},
    (engineLTSI E I imps exps).Run (.ready x) l z →
    ∃ p y, l = p.map liftMove ∧ z = .ready y ∧
      (engineLTS E ⟨s, addrsOf I⟩ imps exps).Run x p y
  | [], x, z, h => by
    rcases run_cases h with ⟨-, rfl⟩ | ⟨y, hs, -⟩ | ⟨o, l', y, hl, -, -⟩
    · exact ⟨[], x, rfl, rfl, .nil _⟩
    · cases hs
    · cases hl
  | o :: l, x, z, h => by
    rcases run_cases h with ⟨hl, -⟩ | ⟨y, hs, -⟩ | ⟨o', l', y, hl, hs, hr⟩
    · cases hl
    · cases hs
    · obtain ⟨rfl, rfl⟩ := List.cons.inj hl
      cases hs with
      | lift ht =>
        obtain ⟨p, y', rfl, rfl, hr'⟩ := run_ready_inv s l hr
        exact ⟨_ :: p, y', rfl, rfl, .vis ⟨_, rfl, ht⟩ hr'⟩

/-- A run from `readying` or `failing` whose first visible move is not the instantiation
answer of that state. -/
theorem run_readying_inv {s : E.Store Nat}
    {l : List (Move (sigN imps.length) ((sigN exps.length).withInst Unit))}
    {z : IState E imps.length exps.length}
    (h : (engineLTSI E I imps exps).Run (.readying s) l z) :
    l = [] ∨ ∃ rest, l = ansInst .ready :: rest ∧
      (engineLTSI E I imps exps).Run (.ready (.idle s)) rest z := by
  rcases run_cases h with ⟨rfl, -⟩ | ⟨y, hs, -⟩ | ⟨o, l', y, rfl, hs, hr⟩
  · exact .inl rfl
  · cases hs
  · cases hs with
    | ready => exact .inr ⟨l', rfl, hr⟩

theorem run_failing_inv
    {l : List (Move (sigN imps.length) ((sigN exps.length).withInst Unit))}
    {z : IState E imps.length exps.length}
    (h : (engineLTSI E I imps exps).Run .failing l z) :
    l = [] ∨ ∃ rest, l = ansInst (.fail ()) :: rest := by
  rcases run_cases h with ⟨rfl, -⟩ | ⟨y, hs, -⟩ | ⟨o, l', y, rfl, hs, -⟩
  · exact .inl rfl
  · cases hs
  · cases hs with
    | fail => exact .inr ⟨l', rfl⟩

theorem ansInst_ne_fail {X F : Sig.{0}} :
    (ansInst .ready : Move X (F.withInst Unit)) ≠ ansInst (.fail ()) := by
  intro h
  cases h

/-- **A run through the start phase and `ready`** is a start run returning values, followed
by a run from the store it returns at. -/
theorem run_starting_inv :
    ∀ (cs : List (Σ _ : (sigN imps.length).Op, Option Payload)) {s : E.Store Nat}
      {t : E.Thread Nat} {rest : List (Move (sigN imps.length) ((sigN exps.length).withInst Unit))}
      {z : IState E imps.length exps.length},
    (engineLTSI E I imps exps).Run (.starting s t)
      ((callEvs (E := sigN imps.length) cs).map .inl ++ ansInst .ready :: rest) z →
    ∃ (c' : E.Config Nat) (ys : List Flat), StartRunI E imps (s, t) cs c' ∧
      E.status c'.1 c'.2 = .returned (.values ys) ∧
      (engineLTSI E I imps exps).Run (.ready (.idle c'.1)) rest z
  | [], s, t, rest, z, h => by
    simp only [callEvs, List.map_nil, List.nil_append] at h
    rcases run_cases h with ⟨hl, -⟩ | ⟨y, hs, hr⟩ | ⟨o, l', y, hl, hs, -⟩
    · cases hl
    · cases hs with
      | sdone run final =>
        rcases run_readying_inv hr with hl | ⟨rest', hl, hr'⟩
        · cases hl
        · obtain ⟨-, rfl⟩ := List.cons.inj hl
          exact ⟨_, _, .nil run, final, hr'⟩
      | strap run final =>
        rcases run_failing_inv hr with hl | ⟨rest', hl⟩
        · cases hl
        · exact (ansInst_ne_fail (List.cons.inj hl).1).elim
    · obtain ⟨rfl, rfl⟩ := List.cons.inj hl
      cases hs
  | ⟨m, n⟩ :: cs, s, t, rest, z, h => by
    simp only [callEvs, List.map_cons, List.cons_append] at h
    rcases run_cases h with ⟨hl, -⟩ | ⟨y, hs, hr⟩ | ⟨o, l', y, hl, hs, hr⟩
    · cases hl
    · cases hs with
      | sdone run final =>
        rcases run_readying_inv hr with hl | ⟨rest', hl, -⟩
        · cases hl
        · cases (List.cons.inj hl).1
      | strap run final =>
        rcases run_failing_inv hr with hl | ⟨rest', hl⟩
        · cases hl
        · cases (List.cons.inj hl).1
    · obtain ⟨rfl, rfl⟩ := List.cons.inj hl
      cases hs with
      | scall run callout hh =>
        rcases run_cases hr with ⟨hl, -⟩ | ⟨y', hs', -⟩ | ⟨o', l'', y', hl', hs', hr'⟩
        · cases hl
        · cases hs'
        · obtain ⟨rfl, rfl⟩ := List.cons.inj hl'
          cases hs' with
          | sret r =>
            obtain ⟨c', ys, hrun, hf, hrest⟩ := run_starting_inv cs hr'
            exact ⟨c', ys, .call run callout hh n hrun, hf, hrest⟩

/-- From `fresh`, the first visible move is `inst`. -/
theorem run_fresh_inv
    {l : List (Move (sigN imps.length) ((sigN exps.length).withInst Unit))}
    {z : IState E imps.length exps.length}
    (h : (engineLTSI E I imps exps).Run .fresh (askInst :: l) z) :
    ∃ y, ITrans E I imps exps .fresh (some askInst) y ∧ (engineLTSI E I imps exps).Run y l z := by
  rcases run_cases h with ⟨hl, -⟩ | ⟨y, hs, -⟩ | ⟨o, l', y, hl, hs, hr⟩
  · cases hl
  · cases hs
  · obtain ⟨rfl, rfl⟩ := List.cons.inj hl
    exact ⟨y, hs, hr⟩

/-- The instantiation prefix `[inst] ++ cs ++ [ready]` is a complete exchange. -/
theorem instPlay_path (cs : List (Σ _ : (sigN imps.length).Op, Option Payload)) :
    Path .idle (instPlay (F := sigN exps.length) cs (InstAns.ready (R := Unit))) .idle := by
  rw [instPlay_eq]
  exact path_round _

theorem instPlay_last (cs : List (Σ _ : (sigN imps.length).Op, Option Payload)) :
    ∃ pre₀ m, instPlay (F := sigN exps.length) cs (InstAns.ready (R := Unit)) = pre₀ ++ [m] ∧
      m.IsP :=
  ⟨askInst :: cs.flatMap fun c => [.inl (.ask c.1), .inl (.ans c.1 c.2)], ansInst .ready,
    by simp only [instPlay, List.cons_append], trivial⟩

theorem instPlay_append (cs : List (Σ _ : (sigN imps.length).Op, Option Payload))
    (rest : List (Move (sigN imps.length) ((sigN exps.length).withInst Unit))) :
    instPlay (F := sigN exps.length) cs (InstAns.ready (R := Unit)) ++ rest =
      askInst :: ((callEvs (E := sigN imps.length) cs).map .inl ++ ansInst .ready :: rest) := by
  rw [instPlay_eq]
  simp only [Round.moves, List.cons_append, List.append_assoc]
  rfl

/-! ## The export phase exactly -/

/-- **After a successful start phase, exactly the plays of `engineStrategy`** from a store some
start run with the same import calls returns at. -/
theorem engine_after_start_iff {J : IInstance E} {a : E.FuncAddr} (hI : I = some J)
    (ha : J.start = some a) (cs : List (Σ _ : (sigN imps.length).Op, Option Payload))
    (p : List (Move (sigN imps.length) (sigN exps.length))) :
    instPlay (F := sigN exps.length) cs .ready ++ p.map liftMove ∈ engineStrategyI E I imps exps ↔
      ∃ (c' : E.Config Nat) (ys : List Flat), StartRunI E imps (J.store, E.invoke a []) cs c' ∧
        E.status c'.1 c'.2 = .returned (.values ys) ∧
        p ∈ engineStrategy E ⟨c'.1, J.addrs⟩ imps exps := by
  constructor
  · intro h
    have hJ : addrsOf I = J.addrs := by rw [hI]; rfl
    obtain ⟨c', ⟨ys, hr, hf⟩, hp⟩ := mem_after_of_inv
      (L := engineLTSI E I imps exps)
      (fun c' : E.Config Nat => engineLTS E ⟨c'.1, J.addrs⟩ imps exps)
      (fun c' => ∃ ys, StartRunI E imps (J.store, E.invoke a []) cs c' ∧
        E.status c'.1 c'.2 = .returned (.values ys))
      (instPlay_path cs) (instPlay_last cs) (fun {p z} hz => by
        rw [instPlay_append] at hz
        obtain ⟨y, hs, hr⟩ := run_fresh_inv hz
        cases hs with
        | start hI' ha' =>
          rw [hI] at hI'
          cases hI'
          rw [ha] at ha'
          cases ha'
          obtain ⟨c', ys, hrun, hf, hrest⟩ := run_starting_inv cs hr
          obtain ⟨p', y, hp', -, hy⟩ := run_ready_inv c'.1 _ hrest
          obtain rfl := List.map_injective_iff.2 liftMove_injective hp'
          rw [hJ] at hy
          exact ⟨c', ⟨ys, hrun, hf⟩, y, hy⟩
        | noStart hI' ha' =>
          rw [hI] at hI'
          cases hI'
          rw [ha] at ha'
          cases ha'
        | noInst hI' =>
          rw [hI] at hI'
          cases hI') h
    exact ⟨c', ys, hr, hf, hp⟩
  · rintro ⟨c', ys, hr, hf, hp⟩
    rw [instPlay_eq]
    exact engine_after_start hI ha hr hf hp

/-- **Without a start function, the export phase follows `[inst, ready]` exactly**: no import
call is made at instantiation, and the plays after it are those of `engineStrategy`. -/
theorem engine_after_noStart_iff {J : IInstance E} (hI : I = some J) (ha : J.start = none)
    (cs : List (Σ _ : (sigN imps.length).Op, Option Payload))
    (p : List (Move (sigN imps.length) (sigN exps.length))) :
    instPlay (F := sigN exps.length) cs .ready ++ p.map liftMove ∈ engineStrategyI E I imps exps ↔
      cs = [] ∧ p ∈ engineStrategy E J.toE imps exps := by
  constructor
  · intro h
    have hJ : addrsOf I = J.addrs := by rw [hI]; rfl
    obtain ⟨_, ⟨rfl⟩, hp⟩ := mem_after_of_inv
      (L := engineLTSI E I imps exps)
      (fun _ : Unit => engineLTS E J.toE imps exps) (fun _ => cs = [])
      (instPlay_path cs) (instPlay_last cs) (fun {p z} hz => by
        rw [instPlay_append] at hz
        obtain ⟨y, hs, hr⟩ := run_fresh_inv hz
        cases hs with
        | start hI' ha' =>
          rw [hI] at hI'
          cases hI'
          rw [ha] at ha'
          cases ha'
        | noStart hI' ha' =>
          rw [hI] at hI'
          cases hI'
          match cs, hr with
          | [], hr =>
            simp only [callEvs, List.map_nil, List.nil_append] at hr
            rcases run_readying_inv hr with hl | ⟨rest', hl, hr'⟩
            · cases hl
            · obtain ⟨-, rfl⟩ := List.cons.inj hl
              obtain ⟨p', y, hp', -, hy⟩ := run_ready_inv J.store _ hr'
              obtain rfl := List.map_injective_iff.2 liftMove_injective hp'
              rw [hJ] at hy
              exact ⟨(), rfl, y, hy⟩
          | ⟨m, n⟩ :: cs, hr =>
            simp only [callEvs, List.map_cons, List.cons_append] at hr
            rcases run_readying_inv hr with hl | ⟨rest', hl, -⟩
            · cases hl
            · cases (List.cons.inj hl).1
        | noInst hI' =>
          rw [hI] at hI'
          cases hI') h
    exact ⟨rfl, hp⟩
  · rintro ⟨rfl, hp⟩
    exact engine_after_noStart hI ha hp

/-- **Without an instance, instantiation never succeeds.** -/
theorem engine_noInst_not_ready (hI : I = none)
    (cs : List (Σ _ : (sigN imps.length).Op, Option Payload))
    (p : List (Move (sigN imps.length) (sigN exps.length))) :
    instPlay (F := sigN exps.length) cs .ready ++ p.map liftMove ∉ engineStrategyI E I imps exps := by
  intro h
  obtain ⟨_, hf, -⟩ := mem_after_of_inv
    (L := engineLTSI E I imps exps)
    (fun _ : Unit => engineLTS E ⟨E.empty Nat, []⟩ imps exps) (fun _ => False)
    (instPlay_path cs) (instPlay_last cs) (fun {p z} hz => by
      rw [instPlay_append] at hz
      obtain ⟨y, hs, hr⟩ := run_fresh_inv hz
      cases hs with
      | start hI' _ => rw [hI] at hI'; cases hI'
      | noStart hI' _ => rw [hI] at hI'; cases hI'
      | noInst _ =>
        match cs, hr with
        | [], hr =>
          simp only [callEvs, List.map_nil, List.nil_append] at hr
          rcases run_failing_inv hr with hl | ⟨rest', hl⟩
          · cases hl
          · exact (ansInst_ne_fail (List.cons.inj hl).1).elim
        | ⟨m, n⟩ :: cs, hr =>
          simp only [callEvs, List.map_cons, List.cons_append] at hr
          rcases run_failing_inv hr with hl | ⟨rest', hl⟩
          · cases hl
          · cases (List.cons.inj hl).1) h
  exact hf

/-- **The export phase from a unique post-start store**: when every start run with the calls
`cs` that returns values returns at the store `s'`, the plays after `[inst] ++ cs ++ [ready]`
are exactly those of `engineStrategy` from `s'`. -/
theorem engine_after_start_iff_of_unique {J : IInstance E} {a : E.FuncAddr} (hI : I = some J)
    (ha : J.start = some a) {cs : List (Σ _ : (sigN imps.length).Op, Option Payload)}
    {s' : E.Store Nat}
    (hu : ∀ (c' : E.Config Nat) (ys : List Flat), StartRunI E imps (J.store, E.invoke a []) cs c' →
      E.status c'.1 c'.2 = .returned (.values ys) → c'.1 = s')
    (hex : ∃ (c' : E.Config Nat) (ys : List Flat), StartRunI E imps (J.store, E.invoke a []) cs c' ∧
      E.status c'.1 c'.2 = .returned (.values ys))
    (p : List (Move (sigN imps.length) (sigN exps.length))) :
    instPlay (F := sigN exps.length) cs .ready ++ p.map liftMove ∈ engineStrategyI E I imps exps ↔
      p ∈ engineStrategy E ⟨s', J.addrs⟩ imps exps := by
  rw [engine_after_start_iff hI ha]
  constructor
  · rintro ⟨c', ys, hr, hf, hp⟩
    rwa [hu c' ys hr hf] at hp
  · intro hp
    obtain ⟨c', ys, hr, hf⟩ := hex
    refine ⟨c', ys, hr, hf, ?_⟩
    rwa [hu c' ys hr hf]

end Silmaril.Proofs.Wasm.Component.InstEngine
