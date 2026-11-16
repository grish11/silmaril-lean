module

public import Silmaril.Logic.Consequence.Gentzen.Interp.Defs

/-!
# Gentzen operations on interpretations: definedness, soundness, completeness

* `closure_some`, `defined_closure_iff`: closing keeps exactly the defined readings.
* `soundFor_closure`: if `I` is sound for `ref` and every `ref e v` is closed under `rs e`
  (e.g. semantic validity under the default rules, `valid_closed`), the closure is sound for
  `ref`. `completeFor_closure`: completeness is kept with no hypothesis.
* `orBot_closure_of_eq_some`: on defined readings, closure commutes with core `orBot`;
  on undefined readings it does not, since the closure of `⊥` under reflexivity derives
  `[x] ⊢ [x]` (`…Gentzen.Interp.Examples.orBot_closure_ne`).
-/

@[expose] public section

namespace Silmaril.Consequence.Gentzen.GInterp

universe u v w

variable {Env : Type u} {Value : Type v} {F : Env → Type w} {rs : (e : Env) → Rules (F e)}
  {I : GInterp Env Value F}

theorem closure_some {e : Env} {v : Value} {S : Seq (F e)} (h : I e v = some S) :
    closure rs I e v = some (Derives (rs e) S) := by
  simp [closure, Interp.map, h]

theorem defined_closure_iff {e : Env} {v : Value} :
    (closure rs I).Defined e v ↔ I.Defined e v := by
  simp [closure, Interp.map, Interp.Defined]

theorem soundFor_closure {ref : (e : Env) → Value → Seq (F e)} (hs : I.SoundFor ref)
    (hc : ∀ e v, Closed (rs e) (ref e v)) : (closure rs I).SoundFor ref := by
  intro e v S h
  obtain ⟨S₀, h₀, rfl⟩ := Option.map_eq_some_iff.1 h
  exact derives_le (hs e v S₀ h₀) (hc e v)

theorem completeFor_closure {ref : (e : Env) → Value → Seq (F e)} (hc : I.CompleteFor ref) :
    (closure rs I).CompleteFor ref := by
  intro e v S h
  obtain ⟨S₀, h₀, rfl⟩ := Option.map_eq_some_iff.1 h
  exact (hc e v S₀ h₀).trans (le_derives _ _)

theorem orBot_closure_of_eq_some {e : Env} {v : Value} {S : Seq (F e)} (h : I e v = some S) :
    (closure rs I).orBot e v = Derives (rs e) (I.orBot e v) := by
  simp [Interp.orBot, closure_some h, h, sysOrBot]

end Silmaril.Consequence.Gentzen.GInterp
