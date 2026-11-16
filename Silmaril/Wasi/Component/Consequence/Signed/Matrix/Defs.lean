module

public import Silmaril.Wasi.Component.Consequence.Signed.Spec.Thms
public import Silmaril.Wasi.Component.Consequence.Interp.Thms

/-! # Coverage of the signed and two-sided protocols

One cell per protocol variant of `Silmaril.Wasi.Component.Consequence.Signed`, with the reading,
the theorems that carry its evidence (checked Lean names), what the evidence rests on and how
strong it is. The variants:

* `importBatch` at each boundary, with and without a reset function;
* `seqCheck`, plain and signed;
* `coreSeq` over the two verified core modules;
* `exportAssumeAssert` at each boundary and each snapshot.

What the evidence rests on (`Evidence`): `definitions` (the reading for every component, with
general laws), `specStrategy` (exact theorems for a specification strategy, not a compiled
component), or `execution` (a core module verified against Core execution, through an explicit
byte codec; no component wraps it).

How strong it is (`Strength`): `exact`, `sound`, `boundedComplete` (sound, and complete on a
stated slice under stated hypotheses), or `laws` (general laws only).

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasi.Consequence.SignedMatrix

open Lean (Name)

/-- The protocol variants. -/
inductive Variant where
  | batch (b : Boundary) (withReset : Bool)
  | seqPlain
  | seqSigned
  | coreMember
  | coreEmpty
  | assumeAssert (b : Boundary) (snap : SnapshotAt)
  deriving DecidableEq, Repr

/-- What the evidence rests on. -/
inductive Evidence where
  | definitions
  | specStrategy
  | execution
  deriving DecidableEq, Repr

/-- How strong the evidence is. -/
inductive Strength where
  | exact
  | sound
  | boundedComplete
  | laws
  deriving DecidableEq, Repr

/-- One cell. -/
structure Cell where
  variant : Variant
  reading : Name
  theorems : List Name
  evidence : Evidence
  strength : Strength
  /-- Scope and limits, one sentence. -/
  note : String
  deriving Repr

/-- Every variant. -/
def Variant.all : List Variant :=
  [.batch .call false, .batch .call true, .batch .answer false, .batch .answer true,
    .seqPlain, .seqSigned, .coreMember, .coreEmpty,
    .assumeAssert .call .ret, .assumeAssert .call .call, .assumeAssert .answer .ret,
    .assumeAssert .answer .call]

/-- The laws of the batch readings. -/
def batchLaws : List Name :=
  [``batchUnsat_iff, ``batchTaut_iff, ``batchUnsat_le_valid, ``derives_batchUnsat_le_valid,
    ``batchTaut_le_valid, ``derives_batchTaut_le_valid, ``batchFinset_of_batches,
    ``batchFinset_unsat, ``batchInterp_eq]

/-- **The cell of a variant.** -/
def cell : Variant → Cell
  | .batch .call false => ⟨.batch .call false, ``importBatch,
      batchLaws ++ [``batches_batchEmitter, ``batchUnsat_batchEmitter_le_valid], .specStrategy,
      .exact, "The specification emitter's batches are exactly its set L; no compiled component."⟩
  | .batch b r => ⟨.batch b r, ``importBatch, batchLaws, .definitions, .laws,
      "Raw Gentzen readings; validity needs emitter soundness and a negation law as hypotheses."⟩
  | .seqPlain => ⟨.seqPlain, ``seqCheck, [``seqInterp_eq], .definitions, .laws,
      "The reading for every component; no specification or module yet."⟩
  | .seqSigned => ⟨.seqSigned, ``seqCheck,
      [``seqOf_idChecker, ``reflexive_idChecker, ``idChecker_le_valid], .specStrategy, .exact,
      "The identity checker over signed u32 lists; a specification strategy."⟩
  | .coreMember => ⟨.coreMember, ``coreSeq,
      [``coreSeq_member_sound, ``coreSeq_member_iff, ``coreSeq_member_not_singleton,
        ``coreBytesInterp_member, ``member_sound, ``member_completeOn], .execution,
      .boundedComplete,
      "Sound for every host set; complete for singleton succedents below 2^32 with a " ++
        "nonempty host set."⟩
  | .coreEmpty => ⟨.coreEmpty, ``coreSeq, [``coreSeq_empty, ``coreBytesInterp_empty], .execution,
      .exact, "Derives nothing through any codec, for every host set; its bytes read as some ⊥."⟩
  | .assumeAssert b s => ⟨.assumeAssert b s, ``exportAssumeAssert,
      [``assumeAssertSeqInterp_eq], .definitions, .laws,
      "Definitions only; the two snapshots are not identified by any theorem."⟩

/-- Every cell. -/
def cells : List Cell := Variant.all.map cell

end Silmaril.Wasi.Consequence.SignedMatrix
