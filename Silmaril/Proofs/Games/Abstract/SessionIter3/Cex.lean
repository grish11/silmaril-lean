module

public import Silmaril.Games.Abstract.SessionIter3.Defs
public import Silmaril.Games.Abstract.SessionIter2.Thms
public import Silmaril.Proofs.Games.Abstract.SessionIter3.Iter

/-!
# Call prefixes of a session iteration: totality is needed (proof)

The body on `Bool` calls once and continues from `true` to `false`, and has no observation at
`false`. The call is a call prefix of the body at `true` (`contSatP`, with the empty chain), but
`iterS` has no observation at all from `true`: its only continuing return reaches `false`,
where nothing can follow.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionIter3

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratOps Silmaril.Games.Abstract.SessionIter
  Silmaril.Games.Abstract.SessionIter2 Silmaril.Games.Abstract.SessionIter3

/-- The signature with one operation and one answer. -/
abbrev cexSig : Sig.{0} := ⟨PUnit, fun _ => PUnit⟩

/-- The body: from `true`, call once and continue with `false`; nothing from `false`. -/
def cexBody : ObsTriple cexSig PUnit Bool ((PUnit ⊕ Bool) ⊕ PUnit) :=
  (fun _ a => cond a {([⟨⟨⟩, ⟨⟩⟩], End.ret (.inl (.inr false)) ⟨⟩)} ∅,
    fun _ _ => ∅, fun _ _ => ∅)

theorem cex_false {s : PUnit} {x} : x ∉ (mapT cexBody iterAssoc).1 s false := by
  rintro ⟨z, hz, -⟩
  exact hz

theorem cex_true {s : PUnit} {x} (h : x ∈ (mapT cexBody iterAssoc).1 s true) :
    x = ([⟨⟨⟩, ⟨⟩⟩], End.ret (.inr false) ⟨⟩) := by
  obtain ⟨z, hz, rfl⟩ := h
  cases Set.mem_singleton_iff.1 hz
  rfl

theorem cex_noBeh_false {s : PUnit} {y} : ¬ AFun.IterBeh (mapT cexBody iterAssoc).1 s false y := by
  intro h
  cases h with
  | exit h => exact cex_false h
  | trap h => exact cex_false h
  | div h => exact cex_false h
  | step h _ => exact cex_false h
  | spin σ h0 hσ =>
    have := hσ 0
    rw [h0] at this
    exact cex_false this

theorem cex_noBeh_true {s : PUnit} {y} : ¬ AFun.IterBeh (mapT cexBody iterAssoc).1 s true y := by
  intro h
  cases h with
  | exit h => cases cex_true h
  | trap h => cases cex_true h
  | div h => cases cex_true h
  | step h h₂ =>
    cases cex_true h
    exact cex_noBeh_false h₂
  | spin σ h0 hσ =>
    have := hσ 0
    rw [h0] at this
    cases cex_true this

/-- **The hypothesis of `mem_satP_iterS_of_total` is needed**: without totality, a call prefix
of the body (with the empty continuing chain) need not be a call prefix of the iteration. -/
theorem not_contSatP_subset :
    ∃ (E : Sig.{0}) (t : ObsTriple E PUnit Bool ((PUnit ⊕ Bool) ⊕ PUnit)),
      ¬ ∀ s a, contSatP t s a ⊆ satP (iterS t) s a := by
  refine ⟨cexSig, cexBody, fun h => ?_⟩
  have hm : (([], ⟨⟩) : List (Call cexSig) × cexSig.Op) ∈ contSatP cexBody ⟨⟩ true :=
    ⟨[], ⟨⟩, true, [], .refl, beh_satP (X := cexBody) rfl ⟨⟨⟩, [], rfl⟩, rfl⟩
  rcases h _ _ hm with ⟨_, _, _, _, _, _, hp, _⟩ | ⟨_, _, ⟨_, _, _, _, _, _, hp, _⟩, -⟩ |
      ⟨_, _, hb, -⟩ | ⟨ω, ⟨_, _, _, _, _, hp, _⟩ | ⟨σ, l, h0, hσ, -⟩, -⟩
  · exact hp
  · exact hp
  · exact cex_noBeh_true hb
  · exact hp
  · have h1 := hσ 0
    rw [h0] at h1
    have h1 := cex_true h1
    simp only [Prod.mk.injEq, End.ret.injEq, Sum.inr.injEq] at h1
    have h2 := hσ 1
    rw [h1.2.1] at h2
    exact cex_false h2

end Silmaril.Proofs.Games.Abstract.SessionIter3
