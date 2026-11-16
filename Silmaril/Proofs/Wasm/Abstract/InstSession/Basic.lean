module

public import Silmaril.Wasm.Abstract.InstSession.Defs
public import Silmaril.Wasm.Abstract.InstStrat.Thms
public import Silmaril.Games.Abstract.StratSession.Thms

/-!
# Scalar Core 3.0 instances as session play objects (proofs)

* `sAns_injective`, `srelabel_injective`, `comp_relabel`: the answer and move maps; the session
  move map is the `InstStrat` move map followed by the answer relabelling and `merge`.
* Relabelling the answers of a triple (`mapAns`): the call prefixes are unchanged
  (`satP_mapAns`), runs of the threading automaton correspond (`trun_map`, `trun_unmap`), so the
  threaded plays are the relabelled ones (`mem_threadT_mapAns`), and reachability is unchanged
  (`reach_mapAns`).
* `instTripleS_eq`: the store-retaining instance triple is `InstStrat.instTriple` with its
  answers relabelled; with `InstStrat.mem_instThread` this gives `mem_instSession`.
* `storeDet_instTripleS`: store determinism at the deterministic profiles.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.InstSession

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratThread
open Silmaril.Wasm.Abstract.InstSession
open Silmaril.Wasm.Abstract.InstStrat (Ans instTriple instThread relabel)
open Silmaril.Wasm.Game
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)

universe u

/-! ## The answer and move maps -/

theorem sAns_injective {ts : List FnType} (f : (ifaceSig ts).Op) : Function.Injective (sAns f) := by
  intro v w h
  cases v <;> cases w <;> simp_all [sAns]

theorem sAns_eq_inr {ts : List FnType} {f : (ifaceSig ts).Op} {v : Answer (ts.get f.1)} :
    sAns f v = .inr PUnit.unit ↔ v = .trap := by
  cases v <;> simp [sAns]

theorem srelabel_injective {E : Sig.{0}} {ts : List FnType} :
    Function.Injective (srelabel (E := E) (ts := ts)) := by
  intro x y h
  rcases x with e | (q | ⟨q, r⟩) <;> rcases y with e' | (q' | ⟨q', r'⟩) <;>
    simp only [srelabel, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h
  all_goals first
    | (subst h; rfl)
    | (cases h; rfl)
    | (obtain ⟨rfl, h⟩ := Ev.ans.inj h; rw [sAns_injective q (eq_of_heq h)])

theorem comp_relabel {E : Sig.{0}} {ts : List FnType} :
    (StratSession.relMove ∘ mapMove ansS) ∘ relabel (E := E) (F := ifaceSig ts) = srelabel := by
  funext o
  rcases o with e | (q | ⟨q, r⟩) <;> rfl

/-! ## Relabelling the answers of a triple -/

section Map

variable {E : Sig.{u}} {S A B B' : Type u} (g : B → B') {t : ObsTriple E S A B}

theorem satP_mapAns (t : ObsTriple E S A B) : satP (mapAns g t) = satP t := by
  funext s a; ext x
  constructor
  · rintro (h | h | ⟨d, e, ⟨y, hy, he⟩, hc⟩ | h)
    · exact .inl h
    · exact .inr (.inl h)
    · obtain rfl : y.1 = d := congrArg Prod.fst he
      exact .inr (.inr (.inl ⟨y.1, y.2, hy, hc⟩))
    · exact .inr (.inr (.inr h))
  · rintro (h | h | ⟨d, e, hy, hc⟩ | h)
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl ⟨d, mapEnd g e, ⟨(d, e), hy, rfl⟩, hc⟩))
    · exact .inr (.inr (.inr h))

theorem tstep_map {x y : TSt E S A} {o : Move E (sig1 A B)} (h : TStep t.1 (satP t) x o y) :
    TStep (mapAns g t).1 (satP (mapAns g t)) x (mapMove g o) y := by
  rw [satP_mapAns]
  cases h with
  | ask s a => exact .ask s a
  | call s a c m hm => exact .call s a c m hm
  | reply s a c m n => exact .reply s a c m n
  | ret s a c b s' hb => exact .ret s a c (g b) s' ⟨_, hb, rfl⟩
  | trap s a c hb => exact .trap s a c ⟨_, hb, rfl⟩
  | deadAsk a => exact .deadAsk a

theorem tstep_unmap {x y : TSt E S A} {o' : Move E (sig1 A B')}
    (h : TStep (mapAns g t).1 (satP (mapAns g t)) x o' y) :
    ∃ o, mapMove g o = o' ∧ TStep t.1 (satP t) x o y := by
  rw [satP_mapAns] at h
  cases h with
  | ask s a => exact ⟨.inr (.ask a), rfl, .ask s a⟩
  | call s a c m hm => exact ⟨.inl (.ask m), rfl, .call s a c m hm⟩
  | reply s a c m n => exact ⟨.inl (.ans m n), rfl, .reply s a c m n⟩
  | ret s a c b s' hb =>
    obtain ⟨⟨c', e⟩, he, hx⟩ := hb
    cases e with
    | ret b₀ s₁ =>
      simp only [mapEnd, Prod.mk.injEq, End.ret.injEq] at hx
      obtain ⟨rfl, rfl, rfl⟩ := hx
      exact ⟨.inr (.ans a (.inl b₀)), rfl, .ret s a c' b₀ s₁ he⟩
    | trap => simp [mapEnd] at hx
    | div => simp [mapEnd] at hx
  | trap s a c hb =>
    obtain ⟨⟨c', e⟩, he, hx⟩ := hb
    cases e with
    | ret => simp [mapEnd] at hx
    | trap =>
      obtain rfl : c' = c := congrArg Prod.fst hx
      exact ⟨.inr (.ans a (.inr PUnit.unit)), rfl, .trap s a c' he⟩
    | div => simp [mapEnd] at hx
  | deadAsk a => exact ⟨.inr (.ask a), rfl, .deadAsk a⟩

theorem trun_map {x y : TSt E S A} {p : List (Move E (sig1 A B))}
    (h : TRun t.1 (satP t) x p y) :
    TRun (mapAns g t).1 (satP (mapAns g t)) x (p.map (mapMove g)) y := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (tstep_map g h) ih

theorem trun_unmap {x y : TSt E S A} {p' : List (Move E (sig1 A B'))}
    (h : TRun (mapAns g t).1 (satP (mapAns g t)) x p' y) :
    ∃ p, p.map (mapMove g) = p' ∧ TRun t.1 (satP t) x p y := by
  induction h with
  | nil => exact ⟨[], rfl, .nil _⟩
  | cons h _ ih =>
    obtain ⟨o, rfl, ho⟩ := tstep_unmap g h
    obtain ⟨p, rfl, hp⟩ := ih
    exact ⟨o :: p, rfl, .cons ho hp⟩

theorem mem_threadT_mapAns {s₀ : S} {q : List (Move E (sig1 A B'))} :
    q ∈ (threadT (mapAns g t) s₀).toStrategy ↔
      ∃ p ∈ (threadT t s₀).toStrategy, p.map (mapMove g) = q := by
  rw [mem_threadT]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨p, rfl, hp⟩ := trun_unmap g hy
    exact ⟨p, mem_threadT.2 ⟨y, hp⟩, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨y, hy⟩ := mem_threadT.1 hp
    exact ⟨y, trun_map g hy⟩

theorem reach_mapAns {s₀ s : S} : Reach (mapAns g t) s₀ s ↔ Reach t s₀ s := by
  constructor
  · intro h
    induction h with
    | refl s => exact .refl s
    | step hb _ ih =>
      obtain ⟨⟨c', e⟩, he, hx⟩ := hb
      cases e with
      | ret b₀ s₁ =>
        simp only [mapEnd, Prod.mk.injEq, End.ret.injEq] at hx
        obtain ⟨rfl, -, rfl⟩ := hx
        exact .step he ih
      | trap => simp [mapEnd] at hx
      | div => simp [mapEnd] at hx
  · intro h
    induction h with
    | refl s => exact .refl s
    | step hb _ ih => exact .step ⟨_, hb, rfl⟩ ih

end Map

/-! ## The instance triple -/

variable {I : ScalarInstance} {P : Profile}

theorem instTripleS_eq : instTripleS I P = mapAns ansS (instTriple I P) := by
  refine Prod.ext ?_ rfl
  funext s a; ext ⟨c, e⟩
  constructor
  · rintro (⟨v, s', he, hp⟩ | ⟨he, h⟩)
    · obtain rfl : e = _ := he
      exact ⟨(c, .ret ⟨a, v⟩ s'), Or.inl ⟨v, s', rfl, hp⟩, rfl⟩
    · obtain rfl : e = _ := he
      exact ⟨(c, .div), Or.inr ⟨rfl, h⟩, rfl⟩
  · rintro ⟨⟨c', e'⟩, (⟨v, s', he, hp⟩ | ⟨he, h⟩), hx⟩
    · obtain rfl : e' = _ := he
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
      exact Or.inl ⟨v, s', rfl, hp⟩
    · obtain rfl : e' = _ := he
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
      exact Or.inr ⟨rfl, h⟩

theorem mem_trap {s s' : Store Nat} {a : I.F.Op} {c : List (Call I.E)} :
    (c, .ret (.inr PUnit.unit) s') ∈ (instTripleS I P).1 s a ↔
      I.Path P (.idle s) (.inr (.ask a) :: (callMoves c ++ [.inr (.ans a .trap)])) (.idle s') := by
  constructor
  · rintro (⟨v, s'', he, hp⟩ | ⟨he, -⟩)
    · obtain ⟨hv, rfl⟩ := End.ret.inj he
      obtain rfl := sAns_eq_inr.1 hv.symm
      exact hp
    · cases he
  · intro hp
    exact Or.inl ⟨.trap, s', rfl, hp⟩

theorem mem_instSession_iff {s₀ : Store Nat} {q : List (Move I.E (ssig I.exports))} :
    q ∈ (instSession I P s₀).toStrategy ↔
      ∃ p ∈ (instThread I P s₀).toStrategy, p.map (StratSession.relMove ∘ mapMove ansS) = q := by
  rw [instSession, StratSession.mem_threadS, instTripleS_eq]
  constructor
  · rintro ⟨p', hp', rfl⟩
    obtain ⟨p, hp, rfl⟩ := (mem_threadT_mapAns ansS).1 hp'
    exact ⟨p, hp, by rw [List.map_map]⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.map (mapMove ansS), (mem_threadT_mapAns ansS).2 ⟨p, hp, rfl⟩, by rw [List.map_map]⟩

theorem mem_instSession {s₀ : Store Nat} {q : List (Move I.E (ssig I.exports))} :
    q ∈ (instSession I P s₀).toStrategy ↔ ∃ p ∈ I.strategy P s₀, p.map srelabel = q := by
  rw [mem_instSession_iff]
  constructor
  · rintro ⟨p', hp', rfl⟩
    obtain ⟨p, hp, rfl⟩ := Silmaril.Wasm.Abstract.InstStrat.mem_instThread.1 hp'
    exact ⟨p, hp, by rw [List.map_map, comp_relabel]⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.map relabel, Silmaril.Wasm.Abstract.InstStrat.mem_instThread.2 ⟨p, hp, rfl⟩,
      by rw [List.map_map, comp_relabel]⟩

theorem map_srelabel_mem {s₀ : Store Nat} {p : List (Move I.E I.F)} :
    p.map srelabel ∈ (instSession I P s₀).toStrategy ↔ p ∈ I.strategy P s₀ := by
  rw [mem_instSession]
  exact ⟨fun ⟨p₀, hp₀, he⟩ => List.map_injective_iff.2 srelabel_injective he ▸ hp₀,
    fun hp => ⟨p, hp, rfl⟩⟩

theorem spull_instSession (s₀ : Store Nat) :
    spull (instSession I P s₀).toStrategy = I.strategy P s₀ :=
  le_antisymm (Strategy.generate_le fun _ hp _ => map_srelabel_mem.1 hp) (by
    intro p hp
    exact Strategy.subset_generate (map_srelabel_mem.2 hp) ((I.strategy P s₀).legal hp))

theorem reach_iff_reachableStore {s₀ s : Store Nat} :
    Reach (instTripleS I P) s₀ s ↔ I.ReachableStore P s₀ s := by
  rw [instTripleS_eq, reach_mapAns]
  exact Silmaril.Wasm.Abstract.InstStrat.reach_iff_reachableStore

/-! ## Store determinism -/

theorem storeDet_instTripleS (o : GrowOracle) : StoreDet (instTripleS I (profile o)) := by
  rintro s a c b s₁ s₂ h₁ h₂
  rcases h₁ with ⟨v, s', he, hp⟩ | ⟨he, -⟩
  swap; · cases he
  obtain ⟨rfl, rfl⟩ := End.ret.inj he
  rcases h₂ with ⟨v', s'', he', hp'⟩ | ⟨he', -⟩
  swap; · cases he'
  obtain ⟨hv, rfl⟩ := End.ret.inj he'
  obtain rfl := sAns_injective a hv
  exact ScalarInstance.activation_functional hp hp'

end Silmaril.Proofs.Wasm.Abstract.InstSession
