module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.WriteAdmission.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization.Ports.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Thms

/-! Certify the oriented typed witness returned by the search. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.WriteAdmission.Proofs

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Loop.MLIR.CF (Op)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Port)
open Identification (BankMap ports quads)
open Factorization (preimage preimage_isSome preimageCandidate preimageCandidate_sound)

variable {old middle new : List (ValueSort Width)} {out : ValueSort Width}
variable {t : SeaOfNodes.Diamond.Ty Width}

private theorem alias_sound (first : BankMap old middle) (second : BankMap middle new)
    (written other : Port (dataPorts middle) t)
    (found : findOutsideAlias first second written = some other) : OutsideAlias first second written other := by
  obtain ⟨_, candidate, _, _, hit, _⟩ := List.findSome?_eq_some_iff.mp found
  obtain ⟨typed, passed⟩ := Option.filter_eq_some_iff.mp hit
  rw [Bool.and_eq_true] at passed
  obtain ⟨apart, unused⟩ := passed
  refine ⟨bne_iff_ne.mp apart, preimageCandidate_sound second _ candidate other typed, ?_⟩
  intro present
  have hasSource := (preimage_isSome first other).mpr present
  rw [Option.isNone_iff_eq_none.mp unused] at hasSource
  cases hasSource

private theorem alias_complete (first : BankMap old middle) (second : BankMap middle new)
    (written other : Port (dataPorts middle) t) (valid : OutsideAlias first second written other) :
    (findOutsideAlias first second written).isSome := by
  obtain ⟨apart, shared, unused⟩ := valid
  have typed : preimageCandidate second (second t written) ⟨t, other⟩ = some other := by
    rw [← shared]
    simp [preimageCandidate]
  have noOld : preimage first other = none :=
    Option.not_isSome_iff_eq_none.mp fun hit => unused ((preimage_isSome first other).mp hit)
  apply List.findSome?_isSome_iff.mpr
  refine ⟨⟨t, other⟩, Identification.ports_complete other, ?_⟩
  apply Option.isSome_iff_exists.mpr
  refine ⟨other, Option.filter_eq_some_iff.mpr ⟨typed, ?_⟩⟩
  rw [Bool.and_eq_true]
  exact ⟨bne_iff_ne.mpr apart, Option.isNone_iff_eq_none.mpr noOld⟩

theorem diagnose_sound (first : BankMap old middle) (second : BankMap middle new)
    {p : Program Op middle out} {collision : Conflict p}
    (found : diagnose first second p = some collision) : collision.Valid first second := by
  obtain ⟨_, occurrence, _, _, hit, _⟩ := List.findSome?_eq_some_iff.mp found
  obtain ⟨other, searched, packed⟩ := Option.map_eq_some_iff.mp hit
  subst collision
  exact alias_sound first second _ other searched

theorem diagnose_isSome (first : BankMap old middle) (second : BankMap middle new)
    (p : Program Op middle out) : (diagnose first second p).isSome ↔ ∃ c : Conflict p, c.Valid first second := by
  constructor
  · intro found
    obtain ⟨c, equation⟩ := Option.isSome_iff_exists.mp found
    exact ⟨c, diagnose_sound first second equation⟩
  · rintro ⟨c, valid⟩
    apply List.findSome?_isSome_iff.mpr
    refine ⟨c.occurrence, List.mem_finRange c.occurrence, ?_⟩
    rw [Option.isSome_map]
    exact alias_complete first second c.written c.other valid

theorem diagnose_none_iff (first : BankMap old middle) (second : BankMap middle new)
    (p : Program Op middle out) :
    diagnose first second p = none ↔ ∀ c : Conflict p, ¬ c.Valid first second :=
  Option.not_isSome_iff_eq_none.symm.trans ((not_congr (diagnose_isSome first second p)).trans not_exists)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.WriteAdmission.Proofs
