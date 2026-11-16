module

public import Silmaril.Wasm.Component.Reference.SessionStrat.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy.Main
public import Silmaril.Games.Abstract.StratSession.Thms
public import Silmaril.Wasm.Game.Machine.Thms
public import Silmaril.Wasm.Game.Instantiate.Thms

/-!
# The session triple of a simple component: rounds

* the triple has no plain traps, no pending calls and no productive streams;
* `storeDet_compTripleS`: it is store-deterministic at the deterministic profiles;
* `spec_of_rounds`, `rounds_of_spec`: its completed rounds from a store are the sessions of the
  specification on their typed calls, the untyped questions trapping at once (`ShapedU`);
* generic facts on rounds of a store-deterministic triple (`rounds_functional`,
  `rounds_append`) and the shape of the plays of the threading of a triple with no lower
  interface and no plain traps (`trun_shape`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.SessionStrat

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Games.Abstract.StratThread (Rounds StoreDet roundsMoves roundMoves)
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core (Store)

local notation "IVal" => Silmaril.Wasm.Component.Val

universe u

/-! ## Generic facts on rounds -/

section Generic

variable {E : Sig.{u}} {S A B : Type u} {t : ObsTriple E S A B}

theorem rounds_functional (ht : StoreDet t) :
    ∀ {s s₁ s₂ : S} {rs : List (A × List (Call E) × B)}, Rounds t s rs s₁ → Rounds t s rs s₂ →
      s₁ = s₂
  | _, _, _, _, .nil _, .nil _ => rfl
  | _, _, _, _, .cons h₁ r₁, .cons h₂ r₂ => by
    obtain rfl := ht _ _ _ _ _ _ h₁ h₂
    exact rounds_functional ht r₁ r₂

theorem rounds_append :
    ∀ {s s'' : S} {rs rs' : List (A × List (Call E) × B)},
      Rounds t s (rs ++ rs') s'' ↔ ∃ s', Rounds t s rs s' ∧ Rounds t s' rs' s''
  | s, _, [], _ => ⟨fun h => ⟨s, .nil s, h⟩, fun ⟨_, h₁, h₂⟩ => by cases h₁; exact h₂⟩
  | _, _, _ :: rs, _ => by
    constructor
    · intro h
      cases h with
      | cons hb hr =>
        obtain ⟨s', h₁, h₂⟩ := rounds_append.mp hr
        exact ⟨s', .cons hb h₁, h₂⟩
    · rintro ⟨s', h₁, h₂⟩
      cases h₁ with
      | cons hb hr => exact .cons hb (rounds_append.mpr ⟨s', hr, h₂⟩)

theorem rounds_snoc {s s₂ : S} {rs : List (A × List (Call E) × B)} {a : A} {c : List (Call E)}
    {b : B} :
    Rounds t s (rs ++ [(a, c, b)]) s₂ ↔ ∃ s₁, Rounds t s rs s₁ ∧ (c, .ret b s₂) ∈ t.1 s₁ a := by
  rw [rounds_append]
  refine exists_congr fun s₁ => and_congr_right fun _ => ⟨fun h => ?_, fun h => .cons h (.nil _)⟩
  cases h with
  | cons hb hr => cases hr; exact hb

theorem streamTake_succ {α : Type u} (ω : ℕ → α) (k : ℕ) :
    streamTake ω (k + 1) = streamTake ω k ++ [ω k] := by
  simp only [streamTake]; rw [List.ofFn_succ_last]; rfl

/-- **A store-deterministic triple whose every finite prefix of rounds is completed has a
coherent infinite sequence of stores.** -/
theorem infRounds_of_rounds (ht : StoreDet t) {s₀ : S} {a : ℕ → A} {r : ℕ → List (Call E) × B}
    (h : ∀ k, ∃ s, Rounds t s₀ (streamTake (fun i => (a i, r i)) k) s) :
    ∃ s, StratThread.InfRounds t s₀ a r s := by
  choose s hs using h
  refine ⟨s, ?_, fun k => ?_⟩
  · have h0 := hs 0
    simp only [streamTake, List.ofFn_zero] at h0
    cases h0
    rfl
  · have h1 := hs (k + 1)
    rw [streamTake_succ] at h1
    obtain ⟨s₁, hr, hb⟩ := rounds_snoc.mp h1
    obtain rfl := rounds_functional ht (hs k) hr
    exact hb

end Generic

/-! ## Threading without a lower interface -/

/-- No call is possible at the interface `sigN 0`. -/
theorem calls_nil : ∀ l : List (Call (sigN 0)), l = []
  | [] => rfl
  | x :: _ => x.1.1.elim0

/-- **Plays of the threading of a triple without plain traps at the lower interface `sigN 0`**:
completed rounds, possibly followed by a pending question. -/
theorem trun_shape {S A B : Type} {t : ObsTriple (sigN 0) S A B}
    (hn : ∀ s a c, (c, End.trap) ∉ t.1 s a) :
    ∀ {s : S} {y : StratThread.TSt (sigN 0) S A} {p : List (Move (sigN 0) (sig1 A B))},
      StratThread.TRun t.1 (satP t) (.idle s) p y →
      ∃ rs s', Rounds t s rs s' ∧
        ((p = roundsMoves rs ∧ y = .idle s') ∨
          ∃ a, p = roundsMoves rs ++ [.inr (.ask a)] ∧ y = .run s' a [])
  | s, _, _, .nil _ => ⟨[], s, .nil s, .inl ⟨rfl, rfl⟩⟩
  | s, _, _, .cons (.ask _ a) (.nil _) => ⟨[], s, .nil s, .inr ⟨a, rfl, rfl⟩⟩
  | _, _, _, .cons (.ask _ _) (.cons (.call _ _ _ m _) _) => m.1.elim0
  | _, _, _, .cons (.ask _ _) (.cons (.trap _ _ _ hc) _) => (hn _ _ _ hc).elim
  | _, _, _, .cons (.ask _ a) (.cons (.ret _ _ _ b _ hb) hr) => by
    obtain ⟨rs, s', hrs, hp⟩ := trun_shape hn hr
    refine ⟨(a, [], b) :: rs, s', .cons hb hrs, ?_⟩
    rcases hp with ⟨rfl, rfl⟩ | ⟨a', rfl, rfl⟩
    · exact .inl ⟨rfl, rfl⟩
    · exact .inr ⟨a', by simp [roundsMoves, roundMoves, StratObs.callMoves], rfl⟩

/-! ## The triple -/

variable {P : Profile} {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}

theorem sessQ_eq (c : Simple) : c.sessQ = typedQ c := by
  funext q
  obtain ⟨j, p⟩ := q
  cases p <;> rfl

theorem mem_compFin_none {s : Store Nat} {q : Nat × Payload} (h : c.sessQ q = none)
    {x : CallBeh (sigN 0) (Store Nat) (Payload ⊕ PUnit)} :
    x ∈ compFin P c I s q ↔ x = ([], .ret (.inr PUnit.unit) s) := by
  simp only [compFin, h, Set.mem_singleton_iff]

theorem mem_compFin_some {s : Store Nat} {q : Nat × Payload} {j : Fin c.exports.length}
    {vs : List IVal} (h : c.sessQ q = some (j, vs))
    {x : CallBeh (sigN 0) (Store Nat) (Payload ⊕ PUnit)} :
    x ∈ compFin P c I s q ↔ x.1 = [] ∧
      ((∃ ws s', RetAt P c I c.exports[j] vs s ws s' ∧ x.2 = .ret (.inl (.vals ws)) s') ∨
        (∃ s', TrapAt P c I c.exports[j] vs s s' ∧ x.2 = .ret (.inr PUnit.unit) s') ∨
        (DivAt P I c.exports[j] vs s ∧ x.2 = .div)) := by
  simp only [compFin, h, Set.mem_ofPred_eq]

theorem noPlainTrap_compTripleS : StratSession.NoPlainTrap (compTripleS P c I) := by
  intro s q l hm
  cases hq : c.sessQ q with
  | none => cases (mem_compFin_none hq).mp hm
  | some jv =>
    obtain ⟨j, vs⟩ := jv
    obtain ⟨-, ⟨_, _, _, he⟩ | ⟨_, _, he⟩ | ⟨_, he⟩⟩ := (mem_compFin_some hq).mp hm <;> cases he

theorem satP_compTripleS (s : Store Nat) (q : Nat × Payload) :
    satP (compTripleS P c I) s q = ∅ := by
  ext x
  exact x.2.1.elim0

/-- Two host-free runs to results at a deterministic profile end in the same store. -/
theorem reach_result_unique {o : Silmaril.Wasm.SingleThreaded.GrowOracle}
    {x : Store Nat × Silmaril.Wasm.SingleThreaded.Thread} {s₁ s₂ : Store Nat}
    {t₁ t₂ : Silmaril.Wasm.SingleThreaded.Thread} {r₁ r₂ : Silmaril.Wasm.Execution.Core.Result}
    (h₁ : Silmaril.Wasm.Game.Reach (Silmaril.Wasm.SingleThreaded.profile o) x (s₁, t₁))
    (f₁ : Silmaril.Wasm.Game.ResultAt s₁ t₁ r₁)
    (h₂ : Silmaril.Wasm.Game.Reach (Silmaril.Wasm.SingleThreaded.profile o) x (s₂, t₂))
    (f₂ : Silmaril.Wasm.Game.ResultAt s₂ t₂ r₂) : s₁ = s₂ :=
  congrArg Prod.fst (Silmaril.Wasm.Game.reach_normal_unique h₁ h₂
    (Silmaril.Wasm.Game.resultAt_no_internal f₁) (Silmaril.Wasm.Game.resultAt_no_internal f₂))

/-- **Store determinism** at the deterministic profiles. -/
theorem storeDet_compTripleS (o : Silmaril.Wasm.SingleThreaded.GrowOracle) :
    StoreDet (compTripleS (Silmaril.Wasm.SingleThreaded.profile o) c I) := by
  intro s q l b s₁ s₂ h₁ h₂
  cases hq : c.sessQ q with
  | none =>
    have e₁ := (mem_compFin_none hq).mp h₁
    have e₂ := (mem_compFin_none hq).mp h₂
    simp only [Prod.mk.injEq, End.ret.injEq] at e₁ e₂
    rw [e₁.2.2, e₂.2.2]
  | some jv =>
    obtain ⟨j, vs⟩ := jv
    obtain ⟨-, ⟨ws, s', hr, he⟩ | ⟨s', hr, he⟩ | ⟨-, he⟩⟩ := (mem_compFin_some hq).mp h₁ <;>
      obtain ⟨-, ⟨ws', s'', hr', he'⟩ | ⟨s'', hr', he'⟩ | ⟨-, he'⟩⟩ :=
        (mem_compFin_some hq).mp h₂ <;>
      simp only [End.ret.injEq, reduceCtorEq] at he he'
    · obtain ⟨rfl, rfl⟩ := he
      obtain ⟨hb, rfl⟩ := he'
      obtain ⟨_, _, _, run, fin, -⟩ := hr.run
      obtain ⟨_, _, _, run', fin', -⟩ := hr'.run
      exact reach_result_unique run fin run' fin'
    · obtain ⟨rfl, rfl⟩ := he
      cases he'.1
    · obtain ⟨rfl, rfl⟩ := he
      cases he'.1
    · obtain ⟨rfl, rfl⟩ := he
      obtain ⟨-, rfl⟩ := he'
      obtain ⟨_, _, run, fin, -⟩ := hr.run
      obtain ⟨_, _, run', fin', -⟩ := hr'.run
      exact reach_result_unique run fin run' fin'

/-- A module has at most one instance. -/
theorem isInst_unique {m : NumModule} {I J : Silmaril.Wasm.Game.ScalarInstance} (hI : m.IsInst I)
    (hJ : m.IsInst J) : I = J := by
  obtain ⟨⟨mt, hmt⟩, -, -⟩ := hI
  obtain ⟨⟨mt', hmt'⟩, -, -⟩ := hJ
  have he : mt = mt' := Option.some.inj (hmt.valid.symm.trans hmt'.valid)
  rw [he] at hmt
  exact Silmaril.Wasm.Game.IsInstance.unique hmt hmt'

theorem compSession_eq (hI : c.mod.IsInst I) :
    compSession P c = StratSession.threadS (compTripleS P c I) I.store := by
  unfold compSession
  split
  · rename_i h
    rw [isInst_unique h.choose_spec hI]
  · rename_i h
    exact absurd ⟨I, hI⟩ h

/-! ## Rounds and specification sessions -/

/-- A completed round of the triple, read at `sigU`. -/
def toRound (r : (Nat × Payload) × List (Call (sigN 0)) × (Payload ⊕ PUnit.{1})) : Round sigU :=
  ⟨r.1, optAns r.2.2⟩

/-- A session answer from a `sigU` answer. -/
def ofAns : Option Payload → Payload ⊕ PUnit.{1}
  | some p => .inl p
  | none => .inr PUnit.unit

/-- A round at `sigU` as a round of the triple. -/
def ofRound (x : Round sigU) : (Nat × Payload) × List (Call (sigN 0)) × (Payload ⊕ PUnit.{1}) :=
  (x.1, [], ofAns x.2)

theorem ofRound_toRound (r : (Nat × Payload) × List (Call (sigN 0)) × (Payload ⊕ PUnit.{1})) :
    ofRound (toRound r) = r := by
  obtain ⟨a, l, b⟩ := r
  rw [calls_nil l]
  cases b <;> rfl

theorem toRound_ofRound (x : Round sigU) : toRound (ofRound x) = x := by
  obtain ⟨q, A⟩ := x
  cases A <;> rfl

theorem map_ofRound_toRound (rs : List ((Nat × Payload) × List (Call (sigN 0)) × (Payload ⊕ PUnit.{1}))) :
    (rs.map toRound).map ofRound = rs := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id rs]
  exact List.map_congr_left fun r _ => ofRound_toRound r

theorem map_toRound_ofRound (Lu : List (Round sigU)) : (Lu.map ofRound).map toRound = Lu := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id Lu]
  exact List.map_congr_left fun x _ => toRound_ofRound x

/-- Rounds whose untyped questions trap and whose typed calls answer values or a trap. -/
def ShapedU (c : Simple) (Lu : List (Round sigU)) : Prop :=
  ∀ x ∈ Lu, (typedQ c x.1 = none → x.2 = none) ∧
    (∀ q, typedQ c x.1 = some q → x.2 = none ∨ ∃ ws, x.2 = some (.vals ws))

theorem shaped_iff {Lu : List (Round sigU)} :
    Shaped c Lu ↔ (∀ x ∈ Lu, x.1.1 < c.exports.length) ∧ ShapedU c Lu :=
  ⟨fun h => ⟨fun x hx => (h x hx).1, fun x hx => (h x hx).2⟩,
    fun h x hx => ⟨h.1 x hx, h.2 x hx⟩⟩

theorem shapedU_cast {c c' : Simple} {len : c.exports.length = c'.exports.length}
    (hty : SameTy c c' len) {Lu : List (Round sigU)} (h : ShapedU c Lu) : ShapedU c' Lu := by
  intro x hx
  obtain ⟨hn, hs⟩ := h x hx
  refine ⟨fun hq => hn ?_, fun q hq => ?_⟩
  · rw [typedQ_cast hty] at hq
    cases hq' : typedQ c x.1 with
    | none => rfl
    | some _ => rw [hq'] at hq; cases hq
  · rw [typedQ_cast hty] at hq
    cases hq' : typedQ c x.1 with
    | none => rw [hq'] at hq; cases hq
    | some r => exact hs r hq'

theorem specCalls_cons (q : Fin c.exports.length × List IVal)
    (calls : List (Fin c.exports.length × List IVal)) :
    specCalls c (q :: calls) = (c.exports[q.1], q.2) :: specCalls c calls := rfl

/-- **Completed rounds are specification sessions** on their typed calls. -/
theorem spec_of_rounds :
    ∀ {s s' : Store Nat} {rs : List ((Nat × Payload) × List (Call (sigN 0)) × (Payload ⊕ PUnit))},
      Rounds (compTripleS P c I) s rs s' →
      SessSpec P c I s (specCalls c (sessCalls c (rs.map toRound))) (sessOuts c (rs.map toRound))
          s' ∧
        TypedCalls c (sessCalls c (rs.map toRound)) ∧ ShapedU c (rs.map toRound)
  | _, _, _, .nil s => ⟨.nil s, fun _ h => by simp [sessCalls] at h, fun _ h => by simp at h⟩
  | s, _, _, .cons (a := q) (c := l) (b := b) hm hr => by
    obtain ⟨hspec, hty, hsh⟩ := spec_of_rounds hr
    rw [List.map_cons]
    cases hq : c.sessQ q with
    | none =>
      have hq' : typedQ c (toRound (q, l, b)).1 = none := by rw [← sessQ_eq]; exact hq
      have e := (mem_compFin_none hq).mp hm
      simp only [Prod.mk.injEq, End.ret.injEq] at e
      obtain ⟨-, rfl, rfl⟩ := e
      rw [sessCalls_none hq', sessOuts_none hq']
      refine ⟨hspec, hty, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨fun _ => rfl, fun _ h => (by rw [hq'] at h; cases h)⟩
      · exact hsh x hx
    | some jv =>
      obtain ⟨j, vs⟩ := jv
      have hq' : typedQ c (toRound (q, l, b)).1 = some (j, vs) := by rw [← sessQ_eq]; exact hq
      obtain ⟨_, ⟨ws, s₁, hret, he⟩ | ⟨s₁, htrap, he⟩ | ⟨-, he⟩⟩ := (mem_compFin_some hq).mp hm <;>
        simp only [End.ret.injEq, reduceCtorEq] at he
      · obtain ⟨rfl, rfl⟩ := he
        rw [sessCalls_some hq', sessOuts_some hq', specCalls_cons]
        refine ⟨.ret hret hspec, fun x hx => ?_, fun x hx => ?_⟩
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact hret.typed
          · exact hty x hx
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨fun h => (by rw [hq'] at h; cases h), fun _ _ => .inr ⟨ws, rfl⟩⟩
          · exact hsh x hx
      · obtain ⟨rfl, rfl⟩ := he
        rw [sessCalls_some hq', sessOuts_some hq', specCalls_cons]
        refine ⟨.trap htrap hspec, fun x hx => ?_, fun x hx => ?_⟩
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact htrap.typed
          · exact hty x hx
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨fun _ => rfl, fun _ _ => .inl rfl⟩
          · exact hsh x hx

/-- **Specification sessions are completed rounds**, the untyped questions trapping at once. -/
theorem rounds_of_spec :
    ∀ {Lu : List (Round sigU)} {s s' : Store Nat}, ShapedU c Lu →
      SessSpec P c I s (specCalls c (sessCalls c Lu)) (sessOuts c Lu) s' →
      Rounds (compTripleS P c I) s (Lu.map ofRound) s'
  | [], s, s', _, h => by
    cases h
    exact .nil s
  | ⟨q, A⟩ :: Lu, s, s', hsh, h => by
    have hsh' : ShapedU c Lu := fun x hx => hsh x (List.mem_cons_of_mem _ hx)
    obtain ⟨hnone, hsome⟩ := hsh _ List.mem_cons_self
    rw [List.map_cons]
    cases hq : typedQ c q with
    | none =>
      rw [sessCalls_none hq, sessOuts_none hq] at h
      have hA : A = none := hnone hq
      subst hA
      refine .cons ((mem_compFin_none (by rw [sessQ_eq]; exact hq)).mpr rfl)
        (rounds_of_spec hsh' h)
    | some jv =>
      obtain ⟨j, vs⟩ := jv
      have hq₁ : c.sessQ q = some (j, vs) := by rw [sessQ_eq]; exact hq
      rw [sessCalls_some hq, sessOuts_some hq, specCalls_cons] at h
      rcases sessSpec_cons_inv h with ⟨ws, s₁, ho, hret, h'⟩ | ⟨s₁, ho, htrap, h'⟩
      · rcases hsome _ hq with hA | ⟨ws', hA⟩
        · subst hA
          cases ho
        · subst hA
          cases ho
          exact .cons ((mem_compFin_some hq₁).mpr ⟨rfl, .inl ⟨ws, s₁, hret, rfl⟩⟩)
            (rounds_of_spec hsh' h')
      · rcases hsome _ hq with hA | ⟨ws', hA⟩
        · subst hA
          exact .cons ((mem_compFin_some hq₁).mpr ⟨rfl, .inr (.inl ⟨s₁, htrap, rfl⟩)⟩)
            (rounds_of_spec hsh' h')
        · subst hA
          cases ho

/-- Divergent behaviours of the triple are diverging typed calls. -/
theorem div_iff {s : Store Nat} {q : Nat × Payload} {l : List (Call (sigN 0))} :
    (l, End.div) ∈ (compTripleS P c I).1 s q ↔
      ∃ j vs, c.sessQ q = some (j, vs) ∧ DivAt P I c.exports[j] vs s := by
  constructor
  · intro hm
    cases hq : c.sessQ q with
    | none => cases (mem_compFin_none hq).mp hm
    | some jv =>
      obtain ⟨j, vs⟩ := jv
      obtain ⟨-, ⟨_, _, _, he⟩ | ⟨_, _, he⟩ | ⟨hd, -⟩⟩ := (mem_compFin_some hq).mp hm
      · cases he
      · cases he
      · exact ⟨j, vs, rfl, hd⟩
  · rintro ⟨j, vs, hq, hd⟩
    exact (mem_compFin_some hq).mpr ⟨calls_nil l, .inr (.inr ⟨hd, rfl⟩)⟩

end Silmaril.Proofs.Wasm.Component.Reference.SessionStrat
