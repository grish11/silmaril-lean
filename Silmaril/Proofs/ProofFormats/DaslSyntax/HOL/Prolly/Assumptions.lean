module

public import Silmaril.ProofFormats.DaslSyntax.HOL.Prolly.Assumptions.Defs
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.ProofFormats.DaslSyntax.HOL.Prolly

open Silmaril.Formats.Dasl
open Silmaril.Formats.Dasl.Prolly (Read ByteKey closedSet setNames)
open Silmaril.Logic.HOLLight
open Silmaril.ProofFormats.DaslSyntax.HOL (hypothesisKey)
open Silmaril.ProofFormats.DaslSyntax.HOL.Prolly

variable {Name : Type}

local instance : DecidableEq ByteKey := (inferInstance : LinearOrder ByteKey).toDecidableEq

private theorem readKey_iff {key : ByteKey} {term : Tm} :
    readKey (Name := Name) key = .ok term ↔ hypothesisKey.encode term = key := by
  constructor
  · unfold readKey
    split
    · split
      · intro hit
        cases hit
        assumption
      · simp
    · simp
  · rintro rfl
    simp [readKey, hypothesisKey.recovers]

private theorem readKeys_iff {keys : List ByteKey} {terms : List Tm} :
    keys.mapM (readKey (Name := Name)) = .ok terms ↔ terms.map hypothesisKey.encode = keys := by
  rw [List.mapM_eq_ok_iff_forall₂]
  induction keys generalizing terms with
  | nil => cases terms <;> simp
  | cons key keys ih =>
    cases terms with
    | nil => simp
    | cons term terms => rw [List.forall₂_cons, ih, readKey_iff, List.map_cons, List.cons.injEq]

private theorem keys_image (terms : List Tm) :
    (terms.map hypothesisKey.encode).toFinset = terms.toFinset.image hypothesisKey.encode := by
  ext key
  simp

private theorem exists_terms {keys : List ByteKey} {premises : Hyps}
    (same : keys.toFinset = premises.image hypothesisKey.encode) :
    ∃ terms : List Tm, terms.map hypothesisKey.encode = keys ∧ terms.toFinset = premises := by
  have range : ∀ key ∈ keys, ∃ term, hypothesisKey.encode term = key := by
    intro key member
    obtain ⟨term, _, equal⟩ := Finset.mem_image.mp (same ▸ List.mem_toFinset.mpr member)
    exact ⟨term, equal⟩
  have lift : ∀ keys : List ByteKey, (∀ key ∈ keys, ∃ term, hypothesisKey.encode term = key) →
      ∃ terms, List.map hypothesisKey.encode terms = keys := by
    intro keys supported
    induction keys with
    | nil => exact ⟨[], rfl⟩
    | cons key keys ih =>
      obtain ⟨term, head⟩ := supported key (List.mem_cons_self ..)
      obtain ⟨terms, tail⟩ := ih fun child member => supported child (List.mem_cons_of_mem _ member)
      exact ⟨term :: terms, congrArg₂ List.cons head tail⟩
  obtain ⟨terms, encoded⟩ := lift keys range
  refine ⟨terms, encoded, Finset.image_injective hypothesisKey.injective ?_⟩
  rw [← keys_image, encoded, same]

theorem assumptions_iff_read {read : Read Name} {width fuel : Nat} {root : Name} {premises : Hyps} :
    assumptions read width fuel root premises ↔
      ∃ terms, readAssumptions read width fuel root = .ok terms ∧ terms.toFinset = premises := by
  unfold assumptions Lift.codedSet setNames readAssumptions
  cases closedSet assumptionCodec read width fuel root with
  | error fault => simp
  | ok view =>
    constructor
    · rintro ⟨_, scanned, same⟩
      cases scanned
      obtain ⟨terms, encoded, identified⟩ := exists_terms same
      exact ⟨terms, readKeys_iff.mpr encoded, identified⟩
    · rintro ⟨terms, checked, rfl⟩
      exact ⟨view, rfl, (congrArg List.toFinset (readKeys_iff.mp checked)).symm.trans (keys_image terms)⟩

end Silmaril.Proofs.ProofFormats.DaslSyntax.HOL.Prolly
