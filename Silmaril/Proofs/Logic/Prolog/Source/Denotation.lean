module

public import Silmaril.Logic.Prolog.Source.Denotation.Defs
public import Silmaril.Logic.Prolog.Source.Compilation.Thms

@[expose] public section
namespace Silmaril.Logic.Prolog.Source
open Silmaril.Logic.Institution.Examples

/-- Every indexed assignment comes from a named assignment on a duplicate-free
finite context. This works for empty contexts and empty model carriers. -/
theorem NamedValuation.indexed_surjective {V : Vocabulary} (M : FOL.Structure V.signature)
    (names : List Variable) (hn : names.Nodup) :
    Function.Surjective (NamedValuation.indexed (M := M) (names := names)) := by
  intro ρ
  let e := List.Nodup.getEquiv names hn
  refine ⟨fun v => ρ (e.symm v), ?_⟩
  funext i
  exact congrArg ρ (e.symm_apply_apply i)

/-- The direct named denotation of an erased term is its native value. -/
theorem Term.erase_denotes {V : Vocabulary} (M : FOL.Structure V.signature)
    (names : List Variable) (ρ : NamedValuation M names) (t : Term V names.length)
    (x : M.carrier ()) :
    (t.erase names).Denotes M ρ x ↔ t.eval M ρ.indexed = x := by
  induction t generalizing x with
  | var i =>
    constructor
    · rintro ⟨_, h⟩
      exact h
    · intro h
      exact ⟨List.get_mem names i, h⟩
  | app f args ih =>
    constructor
    · rintro ⟨known, values, hv, hx⟩
      have he : (fun i => (args i).eval M ρ.indexed) = values :=
        funext (fun i => (ih i (values i)).mp (hv i))
      change M.op f (fun i => (args i).eval M ρ.indexed) = x
      rw [he]
      exact hx
    · intro h
      exact ⟨f.property, fun i => (args i).eval M ρ.indexed,
        fun i => (ih i _).mpr rfl, h⟩

theorem resolveTerm_denotes {V : Vocabulary} (M : FOL.Structure V.signature)
    (names : List Variable) (ρ : NamedValuation M names) (t : NamedTerm)
    (resolved : Term V names.length) (h : resolveTerm? V names t = some resolved)
    (x : M.carrier ()) : t.Denotes M ρ x ↔ resolved.eval M ρ.indexed = x := by
  rw [← resolveTerm_erase V names t resolved h]
  exact resolved.erase_denotes M names ρ x

theorem Atom.erase_holds {V : Vocabulary} (M : FOL.Structure V.signature)
    (names : List Variable) (ρ : NamedValuation M names) (a : Atom V names.length) :
    (a.erase names).Holds M ρ ↔ a.Holds M ρ.indexed := by
  constructor
  · rintro ⟨known, values, hv, hrel⟩
    have he : (fun i => (a.arguments i).eval M ρ.indexed) = values :=
      funext (fun i => ((a.arguments i).erase_denotes M names ρ _).mp (hv i))
    change M.rel a.predicate (fun i => (a.arguments i).eval M ρ.indexed)
    rw [he]
    exact hrel
  · intro h
    exact ⟨a.predicate.property, fun i => (a.arguments i).eval M ρ.indexed,
      fun i => ((a.arguments i).erase_denotes M names ρ _).mpr rfl, h⟩

theorem resolveAtom_holds {V : Vocabulary} (M : FOL.Structure V.signature)
    (names : List Variable) (ρ : NamedValuation M names) (a : NamedAtom)
    (resolved : Atom V names.length) (h : resolveAtom? V names a = some resolved) :
    a.Holds M ρ ↔ resolved.Holds M ρ.indexed := by
  rw [← resolveAtom_erase V names a resolved h]
  exact resolved.erase_holds M names ρ

/-- Universal clauses and existential queries agree with their direct named
semantics. The only context hypothesis is absence of duplicate bindings. -/
theorem Sentence.erase_holdsIn {V : Vocabulary} (M : FOL.Structure V.signature)
    (s : Sentence V) (hn : s.context.Nodup) :
    s.erase.HoldsIn M s.context ↔ s.Holds M := by
  cases s with
  | clause c =>
    constructor
    · intro h ρ hb
      obtain ⟨env, he⟩ := NamedValuation.indexed_surjective M c.context hn ρ
      have hhead := h env (by
        intro b hb'
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb'
        apply (a.erase_holds M c.context env).mpr
        simpa only [he] using hb a ha)
      have hh := (c.head.erase_holds M c.context env).mp hhead
      simpa only [he] using hh
    · intro h env hb
      apply (c.head.erase_holds M c.context env).mpr
      apply h env.indexed
      intro a ha
      exact (a.erase_holds M c.context env).mp
        (hb _ (List.mem_map.mpr ⟨a, ha, rfl⟩))
  | query q =>
    constructor
    · rintro ⟨env, h⟩
      refine ⟨env.indexed, ?_⟩
      intro a ha
      exact (a.erase_holds M q.context env).mp
        (h _ (List.mem_map.mpr ⟨a, ha, rfl⟩))
    · rintro ⟨ρ, h⟩
      obtain ⟨env, he⟩ := NamedValuation.indexed_surjective M q.context hn ρ
      refine ⟨env, ?_⟩
      intro b hb
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
      apply (a.erase_holds M q.context env).mpr
      simpa only [he] using h a ha

theorem eraseDups_nodup (names : List Variable) : names.eraseDups.Nodup := by
  cases names with
  | nil => simp
  | cons v rest =>
    rw [List.eraseDups_cons]
    apply List.nodup_cons.mpr
    constructor
    · intro h
      have hh := (List.mem_filter.mp (List.mem_eraseDups.mp h)).2
      simp at hh
    · exact eraseDups_nodup (rest.filter (fun w => !w == v))
termination_by names.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- Generic semantic adequacy from raw named syntax to independently interpreted
native syntax, for every successful resolution and every public FOL model. -/
theorem resolveSentence_holds {V : Vocabulary} (M : FOL.Structure V.signature)
    (s : NamedSentence) (resolved : Sentence V)
    (h : resolveSentence? V s = some resolved) : resolved.Holds M ↔ s.Holds M := by
  obtain ⟨he, hc⟩ := resolveSentence_erase V s resolved h
  have hn : resolved.context.Nodup := by
    rw [hc]
    exact eraseDups_nodup _
  have hs := resolved.erase_holdsIn M hn
  rw [he, hc] at hs
  exact hs.symm

end Silmaril.Logic.Prolog.Source
