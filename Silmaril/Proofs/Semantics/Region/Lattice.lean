module

public import Silmaril.Semantics.Region.Abstract.Defs

@[expose] public section
namespace Silmaril.Semantics.Region.Abstract.Proofs
universe u v
variable {Atom : Type u} {rules : Rules Atom}

theorem closed_sInf (models : Set (RawModel Atom)) (h : ∀ M ∈ models, Closed rules M) :
    Closed rules (sInf models) := by
  intro r hr premises M hm
  exact h M hm r hr (fun a ha => premises ha M hm)

theorem closure_closed (M : RawModel Atom) : Closed rules (closure rules M) := by
  intro r hr premises N hn subset
  exact hn r hr (fun a ha => premises ha N hn subset)

theorem closure_le {M N : RawModel Atom} (closed : Closed rules N) (subset : M ⊆ N) :
    closure rules M ⊆ N := by
  intro a ha
  exact ha N closed subset

theorem closure_idempotent (M : RawModel Atom) : closure rules (closure rules M) = closure rules M := by
  apply Set.Subset.antisymm
  · exact closure_le (closure_closed M) (fun _ h => h)
  · intro a ha N hn subset
    exact subset ha

theorem reindex_closed {Other : Type v} {f : Atom → Other} {target : Rules Other}
    (transport : RuleMap f rules target) {M : RawModel Other} (closed : Closed target M) :
    Closed rules (reindex f M) := by
  intro r hr premises
  obtain ⟨t, ht, head, body⟩ := transport r hr
  rw [reindex, Set.mem_preimage, ← head]
  apply closed t ht
  intro a ha
  obtain ⟨b, hb, rfl⟩ := body ha
  exact premises hb

theorem forget_sSup {Other : Type v} (f : Atom → Other) (models : Set (RawModel Atom)) :
    forget f (sSup models) = sSup (forget f '' models) := by
  ext a
  constructor
  · rintro ⟨b, ⟨M, hm, hb⟩, rfl⟩
    exact ⟨forget f M, ⟨M, hm, rfl⟩, b, hb, rfl⟩
  · rintro ⟨_, ⟨M, hm, rfl⟩, b, hb, rfl⟩
    exact ⟨b, ⟨M, hm, hb⟩, rfl⟩

theorem reindex_sInf {Other : Type v} (f : Atom → Other) (models : Set (RawModel Other)) :
    reindex f (sInf models) = sInf (reindex f '' models) := by
  ext a
  constructor
  · intro h _ hn
    obtain ⟨M, hm, rfl⟩ := hn
    exact h M hm
  · intro h M hm
    exact h _ ⟨M, hm, rfl⟩

theorem reindex_sSup {Other : Type v} (f : Atom → Other) (models : Set (RawModel Other)) :
    reindex f (sSup models) = sSup (reindex f '' models) := by
  ext a
  constructor
  · rintro ⟨M, hm, ha⟩
    exact ⟨reindex f M, ⟨M, hm, rfl⟩, ha⟩
  · rintro ⟨_, ⟨M, hm, rfl⟩, ha⟩
    exact ⟨M, hm, ha⟩
end Silmaril.Semantics.Region.Abstract.Proofs
