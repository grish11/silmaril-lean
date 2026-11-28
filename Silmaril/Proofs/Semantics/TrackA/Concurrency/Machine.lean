module

public import Silmaril.Semantics.TrackA.Concurrency.Defs

@[expose] public section

namespace Silmaril.Proofs.Semantics.TrackA.Concurrency

open Silmaril.Semantics.TrackA.Concurrency

variable {T L R : Type} [DecidableEq T] [DecidableEq L] [DecidableEq R]

theorem primitive_thread {t : T} {s s' : Local T L R} {e : Event T L R}
    (h : primitive t s = some (e, s')) : e.thread = t := by
  obtain ⟨code, shared⟩ := s
  cases code <;> simp [primitive] at h
  · exact congrArg Event.thread h.1.symm
  · exact congrArg Event.thread h.1.symm
  · exact congrArg Event.thread h.2.1.symm
  · exact congrArg Event.thread h.2.1.symm

theorem stepFor_thread {t : T} {s s' : Config T L R} {e : Event T L R}
    (h : s.stepFor t = some (e, s')) : e.thread = t := by
  unfold Config.stepFor at h
  cases hs : primitive t (s.localState t) with
  | none => simp [hs] at h
  | some outcome =>
    obtain ⟨e', local'⟩ := outcome
    have eq : e' = e := by simpa [hs] using congrArg (Option.map Prod.fst) h
    subst e'
    exact primitive_thread hs

theorem replay_iff {threads : List T} {s t : Config T L R} {xs : List (Event T L R)} :
    replay s threads = some (xs, t) ↔ sc.MTr s xs t ∧ xs.map Event.thread = threads := by
  induction threads generalizing s t xs with
  | nil =>
    cases xs <;> simp [replay, Cslib.LTS.MTr.nil_iff]
  | cons thread rest ih =>
    cases xs with
    | nil =>
      cases step : s.stepFor thread with
      | none => simp [replay, step]
      | some outcome =>
        obtain ⟨event, next⟩ := outcome
        cases tail : replay next rest <;> simp [replay, step, tail]
    | cons event xs =>
      constructor
      · intro h
        simp only [replay, Option.bind_eq_bind] at h
        cases step : s.stepFor thread with
        | none => simp [step] at h
        | some outcome =>
          obtain ⟨e, u⟩ := outcome
          cases tail : replay u rest with
          | none => simp [step, tail] at h
          | some result =>
            obtain ⟨ys, v⟩ := result
            simp [step, tail] at h
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
            obtain ⟨run, schedule⟩ := ih.mp tail
            have same := stepFor_thread step
            cases same
            exact ⟨.stepL step run, congrArg (fun ts => e.thread :: ts) schedule⟩
      · rintro ⟨run, schedule⟩
        simp only [List.map_cons, List.cons.injEq] at schedule
        obtain ⟨rfl, rfl⟩ := schedule
        obtain ⟨u, step, tail⟩ := Cslib.LTS.MTr.cons_iff.mp run
        change s.stepFor event.thread = some (event, u) at step
        simp [replay, step, ih.mpr ⟨tail, rfl⟩]

theorem single_step_iff {s t : Local Unit L R} {e : Event Unit L R} :
    sc.Tr (Config.single s) e (Config.single t) ↔ (sequential ()).Tr s e t := by
  obtain ⟨⟨⟩, action⟩ := e
  change (primitive () s).map _ = some (_, _) ↔ primitive () s = some (_, _)
  cases step : primitive () s with
  | none => simp
  | some result =>
    obtain ⟨event, code, shared⟩ := result
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, eq⟩
      exact ⟨rfl, congrArg (fun c : Config Unit L R => c.localState ()) eq⟩
    · rintro ⟨rfl, eq⟩
      cases eq
      refine ⟨rfl, ?_⟩
      congr 1

theorem single_run_iff {s t : Local Unit L R} {xs : List (Event Unit L R)} :
    sc.MTr (Config.single s) xs (Config.single t) ↔ (sequential ()).MTr s xs t := by
  have eta (c : Config Unit L R) : Config.single (c.localState ()) = c := by
    cases c
    congr
  induction xs generalizing s t with
  | nil =>
    simp only [Cslib.LTS.MTr.nil_iff]
    exact ⟨congrArg (fun c : Config Unit L R => c.localState ()), congrArg Config.single⟩
  | cons e xs ih =>
    simp only [Cslib.LTS.MTr.cons_iff]
    constructor
    · rintro ⟨mid, first, rest⟩
      rw [← eta mid] at first rest
      exact ⟨mid.localState (), single_step_iff.mp first, ih.mp rest⟩
    · rintro ⟨mid, first, rest⟩
      exact ⟨Config.single mid, single_step_iff.mpr first, ih.mpr rest⟩

theorem waiting_iff_disabled {s : Config T L R} {t : T} {l : L} {next : Program L R}
    (head : s.code t = .acquire l next) :
    s.Waiting t l ↔ s.stepFor t = none := by
  simp [Config.Waiting, Config.stepFor, Config.localState, head, primitive]

theorem acquire_iff {t : T} {l : L} {next : Program L R} {shared : Shared T L R}
    {e : Event T L R} {s' : Local T L R} :
    (sequential t).Tr (.acquire l next, shared) e s' ↔
      shared.owner l = none ∧ e = ⟨t, .acquire l⟩ ∧
        s' = (next, { shared with owner := Function.update shared.owner l (some t) }) := by
  simp only [sequential, primitive]
  split <;> simp_all [eq_comm]

theorem release_iff {t : T} {l : L} {next : Program L R} {shared : Shared T L R}
    {e : Event T L R} {s' : Local T L R} :
    (sequential t).Tr (.release l next, shared) e s' ↔
      shared.owner l = some t ∧ e = ⟨t, .release l⟩ ∧
        s' = (next, { shared with owner := Function.update shared.owner l none }) := by
  simp only [sequential, primitive]
  split <;> simp_all [eq_comm]

/-- Every event in the executable enumerator belonged to its selected thread. -/
theorem successors_correct (threads : List T) (covers : ∀ t, t ∈ threads)
    (s : Config T L R) (e : Event T L R) (t : Config T L R) :
    (e, t) ∈ successors threads s ↔ sc.Tr s e t := by
  simp only [successors, List.mem_filterMap]
  constructor
  · rintro ⟨thread, _, step⟩
    obtain rfl := stepFor_thread step
    exact step
  · intro step
    exact ⟨e.thread, covers _, step⟩

end Silmaril.Proofs.Semantics.TrackA.Concurrency
