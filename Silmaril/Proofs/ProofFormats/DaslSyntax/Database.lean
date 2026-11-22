module

public import Silmaril.ProofFormats.DaslSyntax.Database.Defs
public import Silmaril.ProofFormats.DaslSyntax.Thms

public section

namespace Silmaril.Proofs.ProofFormats.DaslSyntax.Database

open Silmaril.ProofFormats.DaslSyntax.Database
open Silmaril.ProofFormats.DaslSyntax (system_iff)
open Silmaril.Semantics.Naming (Binding Relation)
open Silmaril.Logic.HOLLight (Tm Hyps Signature Theory)
open Silmaril.Formats.Dasl (Value)

theorem valueSystem_names {ContextName StatementName Context Statement : Type}
    (contextNames : Relation ContextName Value) (statementNames : Relation StatementName Value)
    (contexts : Relation Value Context) (statements : Relation Value Statement)
    (source : Consequence.System Context Statement) (ctx : ContextName) (result : StatementName) :
    namedSystem contextNames statementNames (valueSystem contexts statements source) ctx result ↔
      namedSystem (Semantics.Naming.push contextNames contexts) (Semantics.Naming.push statementNames statements)
        source ctx result := by
  constructor
  · rintro ⟨⟨left, right, _⟩, ⟨lc, rc, _⟩, ⟨⟨premises, statement, _⟩, ⟨ld, rd, _⟩, holds⟩⟩
    exact system_iff.mpr ⟨premises, statement, ⟨left, lc, ld⟩, ⟨right, rc, rd⟩, holds⟩
  · rintro ⟨⟨premises, statement, _⟩, ⟨⟨left, lc, ld⟩, ⟨right, rc, rd⟩, _⟩, holds⟩
    exact system_iff.mpr ⟨left, right, lc, rc, system_iff.mpr ⟨premises, statement, ld, rd, holds⟩⟩

private theorem knownLeft {Name : Type} {terms : Relation Name Tm} {names : List Name} {decoded : List Tm}
    (listed : List.Forall₂ terms names decoded) {name : Name} (hit : name ∈ names) :
    ∃ term ∈ decoded, terms name term := by
  induction listed with
  | nil => simp at hit
  | cons matched _ ih =>
    rcases List.mem_cons.mp hit with rfl | tail
    · exact ⟨_, .head _, matched⟩
    · obtain ⟨term, member, known⟩ := ih tail
      exact ⟨term, .tail _ member, known⟩

private theorem knownRight {Name : Type} {terms : Relation Name Tm} {names : List Name} {decoded : List Tm}
    (listed : List.Forall₂ terms names decoded) {term : Tm} (hit : term ∈ decoded) :
    ∃ name ∈ names, terms name term := by
  induction listed with
  | nil => simp at hit
  | cons matched _ ih =>
    rcases List.mem_cons.mp hit with rfl | tail
    · exact ⟨_, .head _, matched⟩
    · obtain ⟨name, member, known⟩ := ih tail
      exact ⟨name, .tail _ member, known⟩

private theorem hypsSubset {Name : Type} {terms : Relation Name Tm} (bound : Binding terms)
    {left right : List Name} {leftHyps rightHyps : Hyps}
    (leftHit : HOL.listAssumptions terms left leftHyps) (rightHit : HOL.listAssumptions terms right rightHyps)
    (subset : ∀ name ∈ left, name ∈ right) : leftHyps ⊆ rightHyps := by
  obtain ⟨leftDecoded, leftMatched, rfl⟩ := leftHit
  obtain ⟨rightDecoded, rightMatched, rfl⟩ := rightHit
  intro term member
  obtain ⟨name, nameMem, nameHit⟩ := knownRight leftMatched (List.mem_toFinset.mp member)
  obtain ⟨other, otherMem, otherHit⟩ := knownLeft rightMatched (subset name nameMem)
  exact List.mem_toFinset.mpr (bound nameHit otherHit ▸ otherMem)

theorem listAgreement {Name : Type} {terms : Relation Name Tm} (bound : Binding terms)
    {left right : List Name} {leftHyps rightHyps : Hyps}
    (leftHit : HOL.listAssumptions terms left leftHyps) (rightHit : HOL.listAssumptions terms right rightHyps)
    (same : ∀ name, name ∈ left ↔ name ∈ right) : leftHyps = rightHyps :=
  Finset.Subset.antisymm (hypsSubset bound leftHit rightHit (fun name => (same name).mp))
    (hypsSubset bound rightHit leftHit (fun name => (same name).mpr))

theorem listFiniteAgreement {Name : Type} {terms : Relation Name Tm} (bound : Binding terms)
    {listed : List Name} {names : Finset Name} {hyps : Hyps}
    (covers : ∀ name, name ∈ listed ↔ name ∈ names) (known : HOL.listAssumptions terms listed hyps) :
    ∀ decoded, HOL.finiteAssumptions terms names decoded ↔ decoded = hyps := by
  intro decoded
  constructor
  · rintro ⟨other, otherCover, hit⟩
    exact listAgreement bound hit known (fun name => (otherCover name).trans (covers name).symm)
  · rintro rfl
    exact ⟨listed, covers, known⟩

theorem derivesList_iff_finite {Name : Type} {terms : Relation Name Tm} {sig : Signature} {theory : Theory}
    {listed : List Name} {names : Finset Name} {hyps : Hyps} {result : Name}
    (bound : Binding terms) (covers : ∀ name, name ∈ listed ↔ name ∈ names)
    (known : HOL.listAssumptions terms listed hyps) :
    HOL.derivesList terms sig theory listed result ↔ HOL.derivesFinite terms sig theory names result := by
  constructor
  · intro row
    obtain ⟨decoded, term, hit, termHit, proof⟩ := system_iff.mp row
    exact system_iff.mpr ⟨decoded, term, ⟨listed, covers, hit⟩, termHit, proof⟩
  · intro row
    obtain ⟨decoded, term, hit, termHit, proof⟩ := system_iff.mp row
    have same := (listFiniteAgreement bound covers known decoded).mp hit
    exact system_iff.mpr ⟨hyps, term, known, termHit, same ▸ proof⟩

end Silmaril.Proofs.ProofFormats.DaslSyntax.Database
