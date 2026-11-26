module

public import Silmaril.Semantics.Brookes.Parallel.Defs
import Silmaril.Semantics.Brookes.Thms

public section

namespace Silmaril.Proofs.Semantics.Brookes.ReturnedParallel

open Silmaril.Semantics.Brookes

universe u v w x y

variable {Store : Type u} {A : Type v} {B : Type w} {C : Type x} {D : Type y}

theorem parallel_accepts_iff {p : Behavior Store A} {q : Behavior Store B} {trace : Trace Store}
    {a : A} {b : B} :
    (p.parallel q).accepts trace (a, b) ↔
      ∃ left right merged, p.accepts left a ∧ q.accepts right b ∧
        Shuffle left right merged ∧ Reduces merged trace := by
  constructor
  · rintro ⟨merged, ⟨_, left, right, hl, hr, hs⟩, hd⟩
    exact ⟨left, right, merged, hl, hr, hs, hd⟩
  · rintro ⟨left, right, merged, hl, hr, hs, hd⟩
    have hn : merged ≠ [] := by
      rintro rfl
      cases hs
      exact p.nonempty hl rfl
    exact ⟨merged, ⟨hn, left, right, hl, hr, hs⟩, hd⟩

theorem mapResult_eq_bind (f : A → B) (p : Behavior Store A) :
    p.mapResult f = p.bind (Behavior.ret ∘ f) := by
  apply Behavior.ext
  intro trace b
  rw [Behavior.bind_accepts_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    have h : (p.bind Behavior.ret).accepts trace a := (Behavior.bind_ret p).symm ▸ ha
    obtain ⟨left, right, a', hl, hr, hd⟩ := Behavior.bind_accepts_iff.mp h
    obtain ⟨s, rfl, hs⟩ := Behavior.ret_accepts_iff.mp hr
    exact ⟨left, right, a, hl, Behavior.ret_accepts_iff.mpr ⟨s, rfl, hs⟩, hd⟩
  · rintro ⟨left, right, a, hl, hr, hd⟩
    obtain ⟨s, rfl, hs⟩ := Behavior.ret_accepts_iff.mp hr
    refine ⟨a, ?_, rfl⟩
    rw [← Behavior.bind_ret p]
    exact Behavior.bind_accepts_iff.mpr
      ⟨left, right, a, hl, Behavior.ret_accepts_iff.mpr ⟨s, rfl, hs⟩, hd⟩

theorem mapResult_ret (f : A → B) (a : A) :
    (Behavior.ret (Store := Store) a).mapResult f = Behavior.ret (f a) := by
  rw [mapResult_eq_bind, Behavior.ret_bind]
  rfl

theorem mapResult_bind (f : B → C) (p : Behavior Store A) (k : A → Behavior Store B) :
    (p.bind k).mapResult f = p.bind (fun a => (k a).mapResult f) := by
  simp only [mapResult_eq_bind, Behavior.bind_assoc]

theorem bind_mapResult (f : A → B) (p : Behavior Store A) (k : B → Behavior Store C) :
    (p.mapResult f).bind k = p.bind (k ∘ f) := by
  rw [mapResult_eq_bind, Behavior.bind_assoc]
  congr 1
  funext a
  exact Behavior.ret_bind (f a) k

theorem mapResult_comp (f : A → B) (g : B → C) (p : Behavior Store A) :
    (p.mapResult f).mapResult g = p.mapResult (g ∘ f) := by
  apply Behavior.ext
  intro trace c
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, eq⟩
    exact ⟨a, ha, eq⟩
  · rintro ⟨a, ha, eq⟩
    exact ⟨f a, ⟨a, ha, rfl⟩, eq⟩

private theorem mapResult_id (p : Behavior Store A) : p.mapResult id = p := by
  rw [mapResult_eq_bind]
  exact Behavior.bind_ret p

theorem parallel_generate (leftSeed : Trace Store → A → Prop)
    (rightSeed : Trace Store → B → Prop) :
    (Behavior.generate leftSeed).parallel (Behavior.generate rightSeed) =
      Behavior.generate (fun word result =>
        ∃ left right, left ≠ [] ∧ right ≠ [] ∧ leftSeed left result.1 ∧
          rightSeed right result.2 ∧ Shuffle left right word) := by
  apply Behavior.ext
  rintro trace ⟨a, b⟩
  rw [parallel_accepts_iff]
  constructor
  · rintro ⟨_, _, merged, ⟨left, ⟨hlne, hl⟩, hlr⟩, ⟨right, ⟨hrne, hr⟩, hrr⟩, hs, hd⟩
    obtain ⟨middle, hLeft, dLeft⟩ := Shuffle.of_reduces_left hlr hs
    obtain ⟨raw, hRaw, dRight⟩ := Shuffle.of_reduces_left hrr hLeft.comm
    have hn : raw ≠ [] := by
      rintro rfl
      cases hRaw
      exact hrne rfl
    exact ⟨raw, ⟨hn, left, right, hlne, hrne, hl, hr, hRaw.comm⟩,
      dRight.trans (dLeft.trans hd)⟩
  · rintro ⟨raw, ⟨_, left, right, hlne, hrne, hl, hr, hs⟩, hd⟩
    exact ⟨left, right, raw, Behavior.generate_accepts hlne hl,
      Behavior.generate_accepts hrne hr, hs, hd⟩

theorem parallel_natural (f : A → C) (g : B → D) (p : Behavior Store A) (q : Behavior Store B) :
    (p.parallel q).mapResult (Prod.map f g) = (p.mapResult f).parallel (q.mapResult g) := by
  apply Behavior.ext
  rintro trace ⟨c, d⟩
  rw [parallel_accepts_iff]
  constructor
  · rintro ⟨⟨a, b⟩, hab, eq⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq
    obtain ⟨left, right, merged, hl, hr, hs, hd⟩ := parallel_accepts_iff.mp hab
    exact ⟨left, right, merged, ⟨a, hl, rfl⟩, ⟨b, hr, rfl⟩, hs, hd⟩
  · rintro ⟨left, right, merged, ⟨a, hl, rfl⟩, ⟨b, hr, rfl⟩, hs, hd⟩
    exact ⟨(a, b), parallel_accepts_iff.mpr ⟨left, right, merged, hl, hr, hs, hd⟩, rfl⟩

theorem parallel_symm (p : Behavior Store A) (q : Behavior Store B) :
    (p.parallel q).mapResult Prod.swap = q.parallel p := by
  apply Behavior.ext
  rintro trace ⟨b, a⟩
  rw [parallel_accepts_iff]
  constructor
  · rintro ⟨⟨a', b'⟩, hab, eq⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq
    obtain ⟨left, right, merged, hl, hr, hs, hd⟩ := parallel_accepts_iff.mp hab
    exact ⟨right, left, merged, hr, hl, hs.comm, hd⟩
  · rintro ⟨right, left, merged, hr, hl, hs, hd⟩
    exact ⟨(a, b), parallel_accepts_iff.mpr ⟨left, right, merged, hl, hr, hs.comm, hd⟩, rfl⟩

private theorem shuffle_assoc {Step : Type u} {a b c ab word : List Step}
    (hab : Shuffle a b ab) (h : Shuffle ab c word) :
    ∃ bc, Shuffle b c bc ∧ Shuffle a bc word := by
  induction h generalizing a b with
  | nil =>
    cases hab
    exact ⟨[], .nil, .nil⟩
  | left step _ ih =>
    cases hab with
    | left _ hab =>
      obtain ⟨bc, hbc, hw⟩ := ih hab
      exact ⟨bc, hbc, .left step hw⟩
    | right _ hab =>
      obtain ⟨bc, hbc, hw⟩ := ih hab
      exact ⟨step :: bc, .left step hbc, .right step hw⟩
  | right step _ ih =>
    obtain ⟨bc, hbc, hw⟩ := ih hab
    exact ⟨step :: bc, .right step hbc, .right step hw⟩

theorem parallel_assoc (p : Behavior Store A) (q : Behavior Store B) (r : Behavior Store C) :
    ((p.parallel q).parallel r).mapResult (fun ((a, b), c) => (a, b, c)) =
      p.parallel (q.parallel r) := by
  apply Behavior.ext
  rintro trace ⟨a, b, c⟩
  rw [parallel_accepts_iff]
  constructor
  · rintro ⟨⟨⟨a', b'⟩, c'⟩, h, eq⟩
    change (a', b', c') = (a, b, c) at eq
    cases eq
    obtain ⟨_, cr, _, hpq, hc, hOuter, hFinal⟩ := parallel_accepts_iff.mp h
    obtain ⟨ar, br, _, ha, hb, hInner, hClose⟩ := parallel_accepts_iff.mp hpq
    obtain ⟨word, hRaw, hLift⟩ := Shuffle.of_reduces_left hClose hOuter
    obtain ⟨bc, hbc, hw⟩ := shuffle_assoc hInner hRaw
    exact ⟨ar, bc, word, ha, parallel_accepts_iff.mpr ⟨br, cr, bc, hb, hc, hbc, .refl _⟩,
      hw, hLift.trans hFinal⟩
  · rintro ⟨ar, _, _, ha, hqr, hOuter, hFinal⟩
    obtain ⟨br, cr, _, hb, hc, hInner, hClose⟩ := parallel_accepts_iff.mp hqr
    obtain ⟨word, hRaw, hLift⟩ := Shuffle.of_reduces_left hClose hOuter.comm
    obtain ⟨ba, hba, hw⟩ := shuffle_assoc hInner.comm hRaw
    exact ⟨((a, b), c), parallel_accepts_iff.mpr
      ⟨ba, cr, word, parallel_accepts_iff.mpr ⟨ar, br, ba, ha, hb, hba.comm, .refl _⟩,
        hc, hw.comm, hLift.trans hFinal⟩, rfl⟩

private theorem shuffle_nil_left {Step : Type u} {right merged : List Step}
    (h : Shuffle [] right merged) : merged = right := by
  generalize he : ([] : List Step) = left at h
  induction h with
  | nil => rfl
  | left _ _ _ => cases he
  | right step _ ih => exact congrArg (step :: ·) (ih he)

private theorem shuffle_identity {s : Store} {right merged : Trace Store}
    (h : Shuffle [(s, s)] right merged) : Reduces right merged := by
  generalize he : ([(s, s)] : Trace Store) = left at h
  induction h with
  | nil => cases he
  | left step h _ =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj he
    rw [shuffle_nil_left h]
    exact .tail (.refl _) (.stutter [] _ s)
  | right step _ ih => exact (ih he).append_left [step]

theorem parallel_ret_left (a : A) (q : Behavior Store B) :
    (Behavior.ret a).parallel q = q.strength a := by
  apply Behavior.ext
  rintro trace ⟨a', b⟩
  rw [parallel_accepts_iff]
  constructor
  · rintro ⟨left, right, merged, hl, hr, hs, hd⟩
    obtain ⟨s, rfl, hRet⟩ := Behavior.ret_accepts_iff.mp hl
    obtain ⟨raw, hRaw, hLift⟩ := Shuffle.of_reduces_left hRet hs
    exact ⟨b, q.stable hr ((shuffle_identity hRaw).trans (hLift.trans hd)), rfl⟩
  · rintro ⟨b', hb, eq⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq
    cases trace with
    | nil => exact (q.nonempty hb rfl).elim
    | cons head tail =>
      obtain ⟨s, t⟩ := head
      exact ⟨[(s, s)], _, _, Behavior.ret_accepts_iff.mpr ⟨s, rfl, .refl _⟩, hb,
        Shuffle.append [(s, s)] ((s, t) :: tail),
        .tail (.refl _) (.mumble [] tail s s t)⟩

theorem parallel_ret_right (p : Behavior Store A) (b : B) :
    p.parallel (Behavior.ret b) = p.mapResult (fun a => (a, b)) := by
  rw [← parallel_symm (Behavior.ret b) p, parallel_ret_left]
  apply Behavior.ext
  rintro trace ⟨a, b'⟩
  change (∃ result : B × A, (∃ a', p.accepts trace a' ∧ (b, a') = result) ∧
    result.swap = (a, b')) ↔ _
  constructor
  · rintro ⟨_, ⟨a', ha, rfl⟩, eq⟩
    exact ⟨a', ha, eq⟩
  · rintro ⟨a', ha, eq⟩
    exact ⟨(b, a'), ⟨a', ha, rfl⟩, eq⟩

theorem parallel_unit_left (p : Behavior Store A) :
    ((Behavior.ret ()).parallel p).mapResult Prod.snd = p := by
  rw [parallel_ret_left, Behavior.strength, mapResult_comp]
  exact mapResult_id p

theorem parallel_unit_right (p : Behavior Store A) :
    (p.parallel (Behavior.ret ())).mapResult Prod.fst = p := by
  rw [parallel_ret_right, mapResult_comp]
  exact mapResult_id p

theorem parallel_pure (a : A) (b : B) :
    (Behavior.ret (Store := Store) a).parallel (Behavior.ret b) = Behavior.ret (a, b) := by
  rw [parallel_ret_right, mapResult_eq_bind, Behavior.ret_bind]
  rfl

theorem forget_parallel (p : Behavior Store A) (q : Behavior Store B) :
    (p.parallel q).forget = Command.parallel p.forget q.forget := by
  apply Behavior.ext
  rintro trace ⟨⟩
  rw [Command.parallel_accepts_iff]
  constructor
  · rintro ⟨⟨a, b⟩, h⟩
    obtain ⟨left, right, merged, hl, hr, hs, hd⟩ := parallel_accepts_iff.mp h
    exact ⟨left, right, merged, ⟨a, hl⟩, ⟨b, hr⟩, hs, hd⟩
  · rintro ⟨left, right, merged, ⟨a, hl⟩, ⟨b, hr⟩, hs, hd⟩
    exact ⟨(a, b), parallel_accepts_iff.mpr ⟨left, right, merged, hl, hr, hs, hd⟩⟩

theorem bind_completes_iff {p : Behavior Store A} {k : A → Behavior Store B} {s t : Store}
    {b : B} :
    (p.bind k).completes s t b ↔
      ∃ m a, p.completes s m a ∧ (k a).completes m t b := by
  constructor
  · intro h
    obtain ⟨left, right, a, hl, hr, hd⟩ := Behavior.bind_accepts_iff.mp h
    obtain ⟨m, rl, rr⟩ := Runs.append_iff.mp (Runs.of_reduces hd (.cons (.nil t)))
    exact ⟨m, a, p.stable hl (rl.reduces_singleton (p.nonempty hl)),
      (k a).stable hr (rr.reduces_singleton ((k a).nonempty hr))⟩
  · rintro ⟨m, a, hl, hr⟩
    exact Behavior.bind_accepts_iff.mpr
      ⟨[(s, m)], [(m, t)], a, hl, hr, .tail (.refl _) (.mumble [] [] s m t)⟩

theorem parallel_completes_iff {p : Behavior Store A} {q : Behavior Store B} {s t : Store}
    {a : A} {b : B} :
    (p.parallel q).completes s t (a, b) ↔
      ∃ left right merged, p.accepts left a ∧ q.accepts right b ∧
        Shuffle left right merged ∧ Runs s merged t := by
  constructor
  · intro h
    obtain ⟨left, right, merged, hl, hr, hs, hd⟩ := parallel_accepts_iff.mp h
    exact ⟨left, right, merged, hl, hr, hs, Runs.of_reduces hd (.cons (.nil t))⟩
  · rintro ⟨left, right, merged, hl, hr, hs, run⟩
    have h : (p.parallel q).accepts merged (a, b) :=
      parallel_accepts_iff.mpr ⟨left, right, merged, hl, hr, hs, .refl _⟩
    exact (p.parallel q).stable h (run.reduces_singleton ((p.parallel q).nonempty h))

private theorem shuffle_append_both {Step : Type u} {a b c d p q : List Step}
    (first : Shuffle a b p) (second : Shuffle c d q) : Shuffle (a ++ c) (b ++ d) (p ++ q) := by
  induction first with
  | nil => exact second
  | left step _ ih => exact .left step ih
  | right step _ ih => exact .right step ih

theorem interchange_inclusion {p : Behavior Store A} {q : Behavior Store B}
    {k : A → Behavior Store C} {l : B → Behavior Store D} {trace : Trace Store} {c : C} {d : D}
    (h : ((p.parallel q).bind (fun (a, b) => (k a).parallel (l b))).accepts trace (c, d)) :
    ((p.bind k).parallel (q.bind l)).accepts trace (c, d) := by
  obtain ⟨_, _, ⟨a, b⟩, first, second, hFinal⟩ := Behavior.bind_accepts_iff.mp h
  obtain ⟨ar, br, _, ha, hb, hFirst, dFirst⟩ := parallel_accepts_iff.mp first
  obtain ⟨cr, dr, _, hc, hd, hSecond, dSecond⟩ := parallel_accepts_iff.mp second
  exact parallel_accepts_iff.mpr ⟨ar ++ cr, br ++ dr, _,
    Behavior.bind_accepts_iff.mpr ⟨ar, cr, a, ha, hc, .refl _⟩,
    Behavior.bind_accepts_iff.mpr ⟨br, dr, b, hb, hd, .refl _⟩,
    shuffle_append_both hFirst hSecond, (dFirst.append dSecond).trans hFinal⟩

private def write (v : Nat) : Behavior Nat Unit :=
  Behavior.atomic fun _ t _ => t = v

private def read : Behavior Nat Nat :=
  Behavior.atomic fun s t v => s = t ∧ v = s

theorem shared_store_interchange_strict :
    ∃ (p q : Behavior Nat Unit) (k : Unit → Behavior Nat Nat) (l : Unit → Behavior Nat Unit),
      ((p.bind k).parallel (q.bind l)).completes 0 2 (1, ()) ∧
      ¬((p.parallel q).bind (fun (a, b) => (k a).parallel (l b))).completes 0 2 (1, ()) := by
  refine ⟨write 1, write 2, fun _ => read, fun _ => Behavior.ret (), ?_, ?_⟩
  · apply parallel_completes_iff.mpr
    refine ⟨[(0, 1), (1, 1)], [(1, 2)], [(0, 1), (1, 1), (1, 2)], ?_, ?_,
      .left _ (.left _ (.right _ .nil)), .cons (.cons (.cons (.nil 2)))⟩
    · exact Behavior.bind_accepts_iff.mpr ⟨[(0, 1)], [(1, 1)], (),
        Behavior.atomic_completes_iff.mpr rfl, Behavior.atomic_completes_iff.mpr ⟨rfl, rfl⟩,
        .refl _⟩
    · rw [Behavior.bind_ret]
      exact Behavior.atomic_completes_iff.mpr rfl
  · intro h
    obtain ⟨m, ⟨⟨⟩, ⟨⟩⟩, _, hc⟩ := bind_completes_iff.mp h
    change (read.parallel (Behavior.ret ())).completes m 2 (1, ()) at hc
    rw [parallel_ret_right] at hc
    change (∃ n, read.completes m 2 n ∧ (n, ()) = (1, ())) at hc
    obtain ⟨n, hr, eq⟩ := hc
    have hRead : m = 2 ∧ n = m := Behavior.atomic_completes_iff.mp hr
    have hNum : n = 1 := congrArg Prod.fst eq
    exact (by decide : (1 : Nat) ≠ 2) (hNum.symm.trans (hRead.2.trans hRead.1))


end Silmaril.Proofs.Semantics.Brookes.ReturnedParallel
