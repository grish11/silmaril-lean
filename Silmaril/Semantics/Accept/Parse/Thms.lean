module

public import Silmaril.Semantics.Accept.Parse.Defs
public import Silmaril.Semantics.Accept.Host.Thms
import Silmaril.Proofs.Semantics.Accept.Parse.Basic

/-!
# Parsing sessions: laws

* projections: `mem_inputLang`, `mem_treeLang`, `mem_oneShotRel`; both projections are
  monotone and preserve unions (`inputLang_union`, `treeLang_union`), and only include the
  projection of an intersection (`inputLang_inter_subset`, `treeLang_inter_subset`; strict in
  `Examples`);
* the relation of a module is monotone in its traces and environments (`parseRel_mono`,
  `parseRel_mono_envs`) and preserves unions of trace sets (`parseRel_union`);
* the chunk cursor: along a live run the buffer is the fed input after the consumed prefix
  (`run_cursor`), and every accepted pair of a chunked module relates exactly the `used` slice
  after the cursor (`parseRel_slice`), so failures still advance the cursor. Both are stated for
  the session-abort overrun policy (`onOverrun = .sessionTrap`): a call-locally trapped overrun
  leaves the cursor while `consumed` counts its `used`. For every policy without UB, including
  the call-local trap, see `Silmaril.Semantics.Accept.Parse.Cursor` (`run_cursor_eff`,
  `parseRel_slice_eff`, counting only answered `finish` calls);
* append/done: every accepted pair relates the pending append buffer (`parseRel_done`);
* `usedOfI32_lt`: a decoded `used` count is below `2 ^ 31`.
-/

@[expose] public section

namespace Silmaril.Accept.Parse

open Silmaril.Accept.Handle

universe u v w

variable {V : Type u} {H : Type v} {X : Type w}

@[simp] theorem mem_inputLang {R : Set (List V × X)} {w : List V} :
    w ∈ inputLang R ↔ ∃ x, (w, x) ∈ R := by simp [inputLang]

@[simp] theorem mem_treeLang {R : Set (List V × X)} {x : X} :
    x ∈ treeLang R ↔ ∃ w, (w, x) ∈ R := by simp [treeLang]

@[simp] theorem mem_oneShotRel {R : Set (List V × X)} {v : V} {x : X} :
    (v, x) ∈ oneShotRel R ↔ ([v], x) ∈ R := Iff.rfl

theorem inputLang_mono {R S : Set (List V × X)} (h : R ⊆ S) : inputLang R ⊆ inputLang S :=
  Set.image_mono h

theorem treeLang_mono {R S : Set (List V × X)} (h : R ⊆ S) : treeLang R ⊆ treeLang S :=
  Set.image_mono h

theorem inputLang_union (R S : Set (List V × X)) :
    inputLang (R ∪ S) = inputLang R ∪ inputLang S := Set.image_union _ _ _

theorem treeLang_union (R S : Set (List V × X)) :
    treeLang (R ∪ S) = treeLang R ∪ treeLang S := Set.image_union _ _ _

theorem inputLang_iUnion {ι : Sort*} (R : ι → Set (List V × X)) :
    inputLang (⋃ i, R i) = ⋃ i, inputLang (R i) := Set.image_iUnion

theorem treeLang_iUnion {ι : Sort*} (R : ι → Set (List V × X)) :
    treeLang (⋃ i, R i) = ⋃ i, treeLang (R i) := Set.image_iUnion

theorem inputLang_inter_subset (R S : Set (List V × X)) :
    inputLang (R ∩ S) ⊆ inputLang R ∩ inputLang S := Set.image_inter_subset _ _ _

theorem treeLang_inter_subset (R S : Set (List V × X)) :
    treeLang (R ∩ S) ⊆ treeLang R ∩ treeLang S := Set.image_inter_subset _ _ _

variable [DecidableEq H] {pol : PPolicy H}

theorem parseRel_mono {Envs : Set (Env H X)} {T T' : Set (List (PEv V H))} (h : T ⊆ T') :
    parseRel pol Envs T ⊆ parseRel pol Envs T' :=
  Set.iUnion_mono fun _ => Host.lang_mono h

theorem parseRel_union (Envs : Set (Env H X)) (T T' : Set (List (PEv V H))) :
    parseRel pol Envs (T ∪ T') = parseRel pol Envs T ∪ parseRel pol Envs T' := by
  simp only [parseRel, langOver, Host.lang_union, Set.iUnion_union_distrib]

theorem parseRel_mono_envs {Envs Envs' : Set (Env H X)} (h : Envs ⊆ Envs')
    (T : Set (List (PEv V H))) : parseRel pol Envs T ⊆ parseRel pol Envs' T := by
  intro p hp
  simp only [parseRel, langOver, Set.mem_iUnion] at hp ⊢
  obtain ⟨ρ, hp⟩ := hp
  exact ⟨⟨ρ.1, h ρ.2⟩, hp⟩

theorem run_cursor {ρ : Env H X} (ho : pol.onOverrun = .sessionTrap) {s s' : PState V}
    {t : List (PEv V H)} {A : Set (List V × X)} (hr : (parser pol ρ).Run s t s' A)
    (hc : ChunkOnly t) (hl : s'.phase = .live) :
    s'.buf = (s.buf ++ fed t).drop (consumed t) ∧ consumed t ≤ (s.buf ++ fed t).length :=
  Silmaril.Proofs.Semantics.Accept.Parse.run_cursor ho hr hc hl

/-- **Chunked parsing relates the `used` slice after the cursor.** -/
theorem parseRel_slice (ho : pol.onOverrun = .sessionTrap) (hb : pol.onBadHandle ≠ .ub)
    {Envs : Set (Env H X)} {T : Set (List (PEv V H))} (hT : ∀ t ∈ T, ChunkOnly t)
    {p : List V × X} (hp : p ∈ parseRel pol Envs T) :
    ∃ t ∈ T, ∃ u n h v, t = u ++ PEv.finish n h :: v ∧
      p.1 = ((fed u).drop (consumed u)).take n ∧ consumed u + n ≤ (fed u).length ∧
      h ≠ pol.sentinel ∧ ∃ ρ ∈ Envs, ρ h = some p.2 :=
  Silmaril.Proofs.Semantics.Accept.Parse.rel_slice ho hb hT hp

/-- **Append/done parsing relates the pending buffer.** -/
theorem parseRel_done (hb : pol.onBadHandle ≠ .ub) (ho : pol.onOverrun ≠ .ub)
    {Envs : Set (Env H X)} {T : Set (List (PEv V H))} (hT : ∀ t ∈ T, AppendOnly t)
    {p : List V × X} (hp : p ∈ parseRel pol Envs T) :
    ∃ t ∈ T, ∃ u h v, t = u ++ PEv.done h :: v ∧ p.1 = pending pol.doneClears [] u :=
  Silmaril.Proofs.Semantics.Accept.Parse.rel_done hb ho hT hp

theorem usedOfI32_lt {b : BitVec 32} {n : Nat} (h : usedOfI32 b = some n) : n < 2 ^ 31 := by
  unfold usedOfI32 at h
  split at h
  · cases h
  · rename_i hm
    cases h
    have := BitVec.msb_eq_decide (x := b)
    simp only [Bool.not_eq_true] at hm
    rw [hm] at this
    simp at this
    omega

end Silmaril.Accept.Parse
