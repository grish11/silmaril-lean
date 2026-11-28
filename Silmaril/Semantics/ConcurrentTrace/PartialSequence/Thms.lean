module

public import Silmaril.Semantics.ConcurrentTrace.PartialSequence.Defs
import Silmaril.Proofs.Semantics.ConcurrentTrace.Prefixes

public section

namespace Silmaril.Semantics.ConcurrentTrace.PartialSequence

variable {E R F S : Type*}

/-- A smaller cut is the corresponding truncation of any larger cut. -/
theorem prefix_take (s : PartialSequence E R) {m n : Nat} (h : m ≤ n) :
    (s.cut n).take m = s.cut m :=
  Proofs.Semantics.ConcurrentTrace.prefix_take s h

theorem length_prefix_le (s : PartialSequence E R) (n : Nat) : (s.cut n).length ≤ n :=
  Proofs.Semantics.ConcurrentTrace.length_prefix_le s n

theorem prefix_mono (s : PartialSequence E R) {m n : Nat} (h : m ≤ n) :
    s.cut m <+: s.cut n := by
  rw [← s.prefix_take h]
  exact List.take_prefix _ _

theorem hasPrefix_iff (s : PartialSequence E R) (w : List E) :
    s.HasPrefix w ↔ ∃ n, w <+: s.cut n :=
  Proofs.Semantics.ConcurrentTrace.hasPrefix_iff s w

@[simp] theorem prefix_finite (w : List E) (r : Option R) (n : Nat) :
    (finite w r).cut n = w.take n := by
  cases r <;> rfl

@[simp] theorem completion_finite (w : List E) (r : Option R) :
    (finite w r).completion = r := by
  cases r <;> rfl

/-- All raw finite words together with the optional result determine the partial sequence. -/
theorem eq_iff_observations (s t : PartialSequence E R) :
    s = t ↔ (∀ w, s.HasPrefix w ↔ t.HasPrefix w) ∧ s.completion = t.completion :=
  ⟨fun h => h ▸ ⟨fun _ => Iff.rfl, rfl⟩, fun ⟨hp, hr⟩ =>
    Proofs.Semantics.ConcurrentTrace.eq_of_prefix_eq s t
      (Proofs.Semantics.ConcurrentTrace.prefix_eq_of_rawPrefixes s t hp) hr⟩

@[simp] theorem prefix_map (s : PartialSequence E R) (f : E → F) (g : R → S) (n : Nat) :
    (s.map f g).cut n = (s.cut n).map f :=
  Proofs.Semantics.ConcurrentTrace.prefix_map s f g n

@[simp] theorem completion_map (s : PartialSequence E R) (f : E → F) (g : R → S) :
    (s.map f g).completion = s.completion.map g := by
  cases s <;> rfl

theorem completion_bounded (s : PartialSequence E R) (h : s.completion.isSome) :
    ∃ n, (s.cut n).length < n :=
  Proofs.Semantics.ConcurrentTrace.completion_bounded s h

/-- View a partial sequence as a coherent family of bounded observations. -/
@[expose] def toPrefixSequence (s : PartialSequence E R) : PrefixSequence E R where
  cut := s.cut
  length_le := s.length_prefix_le
  take_eq := s.prefix_take
  completion := s.completion
  completion_bounded := s.completion_bounded

/-- Coherent bounded observations are equivalent to finite pending or completed words
and infinite streams. -/
noncomputable def prefixEquiv : PartialSequence E R ≃ PrefixSequence E R :=
  Equiv.ofBijective toPrefixSequence ⟨
    fun _ _ h => Proofs.Semantics.ConcurrentTrace.eq_of_prefix_eq _ _
      (fun n => congrArg (fun p : PrefixSequence E R => p.cut n) h)
      (congrArg PrefixSequence.completion h),
    fun p => by
      obtain ⟨s, hs, hr⟩ := Proofs.Semantics.ConcurrentTrace.realize_prefixes p
      cases p
      exact ⟨s, by simp only [toPrefixSequence, funext hs, hr]⟩⟩

@[simp] theorem prefixEquiv_apply (s : PartialSequence E R) :
    prefixEquiv s = s.toPrefixSequence := by rfl

end Silmaril.Semantics.ConcurrentTrace.PartialSequence
