module

public import Mathlib.Order.SetNotation
public import Mathlib.Data.Set.Basic

/-!
# The SZS ontology: semantic status values

The SZS ontology (Sutcliffe) gives each status a three-letter code and a one-word name, and
defines the semantic ("deductive", now "semantic success") statuses by what is true of the
models of the axioms `Ax` and of the conjecture `C`. This module transcribes those definitions
over an abstract semantics:

* `Problem I`: a type `I` of interpretations, the set `ax` of interpretations that are models of
  `Ax`, and the set `conj` of models of `C`. "A model of `~C`" is an interpretation outside
  `conj` (two-valued semantics). Every status depends only on these two sets.
* Two sources, kept apart, since their texts differ:
  - `V2007`: G. Sutcliffe, "The SZS Ontology", TPTP T-Party 2007 position statement
    (`szs-2007`). The deductive statuses, transcribed **literally**, including where the text
    disagrees with its own diagram (see `Silmaril.Logic.Szs.Thms`).
  - `Current`: the Success ontology at szs.tptp.org (`szs-success`, retrieved 2026-11-16), where
    `C` is a conjunction of conjectures. The same codes with their current wording, plus the
    semantic codes added since 2007 that need no notion of finiteness or signature (`STH`,
    `SCT`, `WEC`, `WTC`, `WCC`, `WUC`, `WCA` and the preservation statuses). The finite
    statuses (`FSA`, `FTH`, `FTT`, `FUN`, `FCS`, `FCT`) and the model-extension statuses
    (`MEX`, `CMX`) are not given semantics here.
* `Status`: the three-letter codes of both, with `code`, `oneWord`, and `ofCode?`.
* `monolithic C`: a problem without axioms (`Ax` is TRUE, every interpretation is a model of it).
  Both sources say a non-`Ax => C` input is read this way; the project's `@[answers]` statuses
  (`thm`, `sat`, `uns`, `csa` over a predicate) are statuses of such problems
  (`Silmaril.Logic.Szs.Thms`: `ofPred_*`).

References (`references.bib`): `szs-2007`, `szs-success`, `sutcliffe-2008-szs`.
-/

@[expose] public section

namespace Silmaril.Logic.Szs

universe u

/-- A problem `Ax => C` read semantically: the models of `Ax` and the models of `C` among the
interpretations `I`. -/
structure Problem (I : Type u) where
  /-- The interpretations that are models of the axioms. -/
  ax : Set I
  /-- The interpretations that are models of the conjecture. -/
  conj : Set I

namespace Problem

variable {I : Type u}

/-- A problem with no axioms: every interpretation is a model of `Ax`. -/
def monolithic (C : Set I) : Problem I := ⟨Set.univ, C⟩

/-- A project predicate `P` over arguments `α`, as a problem: the interpretations are the
arguments, and there are no axioms. -/
def ofPred {α : Type u} (P : α → Prop) : Problem α := monolithic {x | P x}

/-- "Some, but not all, interpretations are models of" `s`. -/
def SomeNotAll (s : Set I) : Prop := s.Nonempty ∧ s ≠ Set.univ

end Problem

open Problem

/-! ## The 2007 text (`szs-2007`), literally -/

namespace V2007

variable {I : Type u} (P : Problem I)

/-- Satisfiable (SAT): some interpretations are models of Ax; some models of Ax are models of C. -/
def SAT : Prop := P.ax.Nonempty ∧ ∃ i ∈ P.ax, i ∈ P.conj
/-- Theorem (THM): all models of Ax are models of C. -/
def THM : Prop := P.ax ⊆ P.conj
/-- Equivalent (EQV): all models of Ax are models of C; all models of C are models of Ax. -/
def EQV : Prop := P.ax ⊆ P.conj ∧ P.conj ⊆ P.ax
/-- WeakerTheorem (WTH): some, but not all, interpretations are models of Ax; all models of Ax
are models of C; some models of C are not models of Ax. -/
def WTH : Prop := SomeNotAll P.ax ∧ P.ax ⊆ P.conj ∧ ∃ i ∈ P.conj, i ∉ P.ax
/-- TautologousConclusion (TAC): some, but not all, interpretations are models of Ax; all
interpretations are models of C. -/
def TAC : Prop := SomeNotAll P.ax ∧ P.conj = Set.univ
/-- EquivalentTheorem (ETH): some, but not all, interpretations are models of Ax; all models of
Ax are models of C; all models of C are models of Ax. -/
def ETH : Prop := SomeNotAll P.ax ∧ P.ax ⊆ P.conj ∧ P.conj ⊆ P.ax
/-- Tautology (TAU): all interpretations are models of Ax; all interpretations are models of C. -/
def TAU : Prop := P.ax = Set.univ ∧ P.conj = Set.univ
/-- ContradictoryAxioms (CAX): no interpretations are models of Ax. -/
def CAX : Prop := P.ax = ∅
/-- SatisfiableConclusionContradictoryAxioms (SCA): no interpretations are models of Ax; some
interpretations are models of C. -/
def SCA : Prop := P.ax = ∅ ∧ P.conj.Nonempty
/-- TautologousConclusionContradictoryAxioms (TCA): no interpretations are models of Ax; all
interpretations are models of C. -/
def TCA : Prop := P.ax = ∅ ∧ P.conj = Set.univ
/-- CounterSatisfiable (CSA): some interpretations are models of Ax; some models of Ax are models
of ~C. -/
def CSA : Prop := P.ax.Nonempty ∧ ∃ i ∈ P.ax, i ∉ P.conj
/-- CounterTheorem (CTH): all models of Ax are models of ~C. -/
def CTH : Prop := P.ax ⊆ P.conjᶜ
/-- CounterEquivalent (CEQ), as written: all models of Ax are models of ~C; all models of **C**
are models of Ax. (Its gloss "Ax xor C" needs "models of ~C"; see `V2007.ceq_conj_eq_empty`.) -/
def CEQ : Prop := P.ax ⊆ P.conjᶜ ∧ P.conj ⊆ P.ax
/-- WeakerCounterTheorem (WCT): some, but not all, interpretations are models of Ax; all models of
Ax are models of ~C; some models of ~C are not models of Ax. -/
def WCT : Prop := SomeNotAll P.ax ∧ P.ax ⊆ P.conjᶜ ∧ ∃ i ∉ P.conj, i ∉ P.ax
/-- UnsatisfiableConclusion (UNC): some, but not all, interpretations are models of Ax; all
interpretations are models of ~C. -/
def UNC : Prop := SomeNotAll P.ax ∧ P.conj = ∅
/-- EquivalentCounterTheorem (ECT): some, but not all, interpretations are models of Ax; all
models of Ax are models of ~C; all models of ~C are models of Ax. -/
def ECT : Prop := SomeNotAll P.ax ∧ P.ax ⊆ P.conjᶜ ∧ P.conjᶜ ⊆ P.ax
/-- Unsatisfiable (UNS): all interpretations are models of Ax; all interpretations are models of
~C. -/
def UNS : Prop := P.ax = Set.univ ∧ P.conj = ∅
/-- SatisfiableCounterConclusionContradictoryAxioms (SCC): no interpretations are models of Ax;
some interpretations are models of ~C; some interpretations are models of C. -/
def SCC : Prop := P.ax = ∅ ∧ P.conjᶜ.Nonempty ∧ P.conj.Nonempty
/-- UnsatisfiableConclusionContradictoryAxioms (UCA): no interpretations are models of Ax; all
interpretations are models of ~C. -/
def UCA : Prop := P.ax = ∅ ∧ P.conj = ∅
/-- NoConsequence (NOC): some interpretations are models of Ax; some models of Ax are models of
C; some models of Ax are models of ~C. -/
def NOC : Prop := P.ax.Nonempty ∧ (∃ i ∈ P.ax, i ∈ P.conj) ∧ ∃ i ∈ P.ax, i ∉ P.conj

end V2007

/-! ## The current Success ontology (`szs-success`) -/

namespace Current

variable {I : Type u} (P : Problem I)

/-- UnsatisfiabilityPreserving (UNP): if Ax is unsatisfiable then C is unsatisfiable. -/
def UNP : Prop := P.ax = ∅ → P.conj = ∅
/-- SatisfiabilityPreserving (SAP): if Ax is satisfiable then C is satisfiable. -/
def SAP : Prop := P.ax.Nonempty → P.conj.Nonempty
/-- TautologyPreserving (TAP): if Ax is a tautology then C is a tautology. -/
def TAP : Prop := P.ax = Set.univ → P.conj = Set.univ
/-- EquiSatisfiable (ESA): Ax is satisfiable iff C is satisfiable. -/
def ESA : Prop := P.ax.Nonempty ↔ P.conj.Nonempty
/-- EquiTautologous (ETA): Ax is a tautology iff C is a tautology. -/
def ETA : Prop := P.ax = Set.univ ↔ P.conj = Set.univ
/-- Satisfiable (SAT): some interpretations are models of Ax, and some models of Ax are models
of C. -/
def SAT : Prop := P.ax.Nonempty ∧ ∃ i ∈ P.ax, i ∈ P.conj
/-- Theorem (THM): all models of Ax are models of C. -/
def THM : Prop := P.ax ⊆ P.conj
/-- SatisfiableAxiomsTheorem (STH): some interpretations are models of Ax, and all models of Ax
are models of C. -/
def STH : Prop := P.ax.Nonempty ∧ P.ax ⊆ P.conj
/-- Equivalent (EQV): some interpretations are models of Ax, all models of Ax are models of C,
and all models of C are models of Ax. -/
def EQV : Prop := P.ax.Nonempty ∧ P.ax ⊆ P.conj ∧ P.conj ⊆ P.ax
/-- TautologousConclusion (TAC): some interpretations are models of Ax, and all interpretations
are models of C. -/
def TAC : Prop := P.ax.Nonempty ∧ P.conj = Set.univ
/-- WeakerConclusion (WEC): some interpretations are models of Ax, all models of Ax are models of
C, and some models of C are not models of Ax. -/
def WEC : Prop := P.ax.Nonempty ∧ P.ax ⊆ P.conj ∧ ∃ i ∈ P.conj, i ∉ P.ax
/-- EquivalentTheorem (ETH): some, but not all, interpretations are models of Ax, all models of
Ax are models of C, and all models of C are models of Ax. -/
def ETH : Prop := SomeNotAll P.ax ∧ P.ax ⊆ P.conj ∧ P.conj ⊆ P.ax
/-- Tautology (TAU): all interpretations are models of Ax, and all interpretations are models of
C. -/
def TAU : Prop := P.ax = Set.univ ∧ P.conj = Set.univ
/-- WeakerTautologousConclusion (WTC): some, but not all, interpretations are models of Ax, and
all interpretations are models of C. -/
def WTC : Prop := SomeNotAll P.ax ∧ P.conj = Set.univ
/-- WeakerTheorem (WTH): some interpretations are models of Ax, all models of Ax are models of C,
some models of C are not models of Ax, and some interpretations are not models of C. -/
def WTH : Prop :=
  P.ax.Nonempty ∧ P.ax ⊆ P.conj ∧ (∃ i ∈ P.conj, i ∉ P.ax) ∧ ∃ i, i ∉ P.conj
/-- CounterUnsatisfiabilityPreserving (CUP): if Ax is unsatisfiable then ~C is unsatisfiable. -/
def CUP : Prop := P.ax = ∅ → P.conjᶜ = ∅
/-- CounterSatisfiabilityPreserving (CSP): if Ax is satisfiable then ~C is satisfiable. -/
def CSP : Prop := P.ax.Nonempty → P.conjᶜ.Nonempty
/-- CounterTautologyPreserving (CTP): if Ax is a tautology then ~C is a tautology. -/
def CTP : Prop := P.ax = Set.univ → P.conjᶜ = Set.univ
/-- EquiCounterSatisfiable (ECS): Ax is satisfiable iff ~C is satisfiable. -/
def ECS : Prop := P.ax.Nonempty ↔ P.conjᶜ.Nonempty
/-- EquiCounterTautologous (ECA): Ax is a tautology iff ~C is a tautology. -/
def ECA : Prop := P.ax = Set.univ ↔ P.conjᶜ = Set.univ
/-- CounterSatisfiable (CSA): some interpretations are models of Ax, and some models of Ax are
models of ~C. -/
def CSA : Prop := P.ax.Nonempty ∧ ∃ i ∈ P.ax, i ∉ P.conj
/-- CounterTheorem (CTH): all models of Ax are models of ~C. -/
def CTH : Prop := P.ax ⊆ P.conjᶜ
/-- SatisfiableAxiomsCounterTheorem (SCT): some interpretations are models of Ax, and all models
of Ax are models of ~C. -/
def SCT : Prop := P.ax.Nonempty ∧ P.ax ⊆ P.conjᶜ
/-- CounterEquivalent (CEQ): some interpretations are models of Ax, all models of Ax are models
of ~C, and all models of ~C are models of Ax. -/
def CEQ : Prop := P.ax.Nonempty ∧ P.ax ⊆ P.conjᶜ ∧ P.conjᶜ ⊆ P.ax
/-- UnsatisfiableConclusion (UNC): some interpretations are models of Ax, and all
interpretations are models of ~C. -/
def UNC : Prop := P.ax.Nonempty ∧ P.conj = ∅
/-- WeakerCounterConclusion (WCC): some interpretations are models of Ax, all models of Ax are
models of ~C, and some models of ~C are not models of Ax. -/
def WCC : Prop := P.ax.Nonempty ∧ P.ax ⊆ P.conjᶜ ∧ ∃ i ∉ P.conj, i ∉ P.ax
/-- EquivalentCounterTheorem (ECT): some, but not all, interpretations are models of Ax, all
models of Ax are models of ~C, and all models of ~C are models of Ax. -/
def ECT : Prop := SomeNotAll P.ax ∧ P.ax ⊆ P.conjᶜ ∧ P.conjᶜ ⊆ P.ax
/-- Unsatisfiable (UNS): all interpretations are models of Ax, and all interpretations are
models of ~C. -/
def UNS : Prop := P.ax = Set.univ ∧ P.conj = ∅
/-- WeakerUnsatisfiableConclusion (WUC): some, but not all, interpretations are models of Ax,
and all interpretations are models of ~C. -/
def WUC : Prop := SomeNotAll P.ax ∧ P.conj = ∅
/-- WeakerCounterTheorem (WCT): some interpretations are models of Ax, all models of Ax are
models of ~C, some models of ~C are not models of Ax, and some interpretations are models of C. -/
def WCT : Prop :=
  P.ax.Nonempty ∧ P.ax ⊆ P.conjᶜ ∧ (∃ i ∉ P.conj, i ∉ P.ax) ∧ P.conj.Nonempty
/-- ContradictoryAxioms (CAX): no interpretations are models of Ax. -/
def CAX : Prop := P.ax = ∅
/-- SatisfiableConclusionContradictoryAxioms (SCA): no interpretations are models of Ax, and
some interpretations are models of C. -/
def SCA : Prop := P.ax = ∅ ∧ P.conj.Nonempty
/-- SatisfiableCounterConclusionContradictoryAxioms (SCC): no interpretations are models of Ax,
and some interpretations are models of ~C. -/
def SCC : Prop := P.ax = ∅ ∧ P.conjᶜ.Nonempty
/-- TautologousConclusionContradictoryAxioms (TCA): no interpretations are models of Ax, and all
interpretations are models of C. -/
def TCA : Prop := P.ax = ∅ ∧ P.conj = Set.univ
/-- WeakerConclusionContradictoryAxioms (WCA): no interpretations are models of Ax, and some,
but not all, interpretations are models of C. -/
def WCA : Prop := P.ax = ∅ ∧ SomeNotAll P.conj
/-- UnsatisfiableConclusionContradictoryAxioms (UCA): no interpretations are models of Ax, and
all interpretations are models of ~C. -/
def UCA : Prop := P.ax = ∅ ∧ P.conj = ∅
/-- NoConsequence (NOC): some interpretations are models of Ax, some models of Ax are models of
C, and some models of Ax are models of ~C. -/
def NOC : Prop := P.ax.Nonempty ∧ (∃ i ∈ P.ax, i ∈ P.conj) ∧ ∃ i ∈ P.ax, i ∉ P.conj

end Current

/-! ## Codes -/

/-- The semantic status values with a three-letter code, in either source. -/
inductive Status where
  | UNP | SAP | TAP | ESA | ETA | SAT | THM | STH | EQV | TAC | WEC | ETH | TAU | WTC | WTH
  | CUP | CSP | CTP | ECS | ECA | CSA | CTH | SCT | CEQ | UNC | WCC | ECT | UNS | WUC | WCT
  | CAX | SCA | SCC | TCA | WCA | UCA | NOC
  deriving DecidableEq, Repr

namespace Status

/-- Every status, in the order above. -/
def all : List Status :=
  [UNP, SAP, TAP, ESA, ETA, SAT, THM, STH, EQV, TAC, WEC, ETH, TAU, WTC, WTH,
   CUP, CSP, CTP, ECS, ECA, CSA, CTH, SCT, CEQ, UNC, WCC, ECT, UNS, WUC, WCT,
   CAX, SCA, SCC, TCA, WCA, UCA, NOC]

/-- The three-letter code. -/
def code : Status → String
  | UNP => "UNP" | SAP => "SAP" | TAP => "TAP" | ESA => "ESA" | ETA => "ETA" | SAT => "SAT"
  | THM => "THM" | STH => "STH" | EQV => "EQV" | TAC => "TAC" | WEC => "WEC" | ETH => "ETH"
  | TAU => "TAU" | WTC => "WTC" | WTH => "WTH" | CUP => "CUP" | CSP => "CSP" | CTP => "CTP"
  | ECS => "ECS" | ECA => "ECA" | CSA => "CSA" | CTH => "CTH" | SCT => "SCT" | CEQ => "CEQ"
  | UNC => "UNC" | WCC => "WCC" | ECT => "ECT" | UNS => "UNS" | WUC => "WUC" | WCT => "WCT"
  | CAX => "CAX" | SCA => "SCA" | SCC => "SCC" | TCA => "TCA" | WCA => "WCA" | UCA => "UCA"
  | NOC => "NOC"

/-- The official one-word name (current ontology). -/
def oneWord : Status → String
  | UNP => "UnsatisfiabilityPreserving" | SAP => "SatisfiabilityPreserving"
  | TAP => "TautologyPreserving" | ESA => "EquiSatisfiable" | ETA => "EquiTautologous"
  | SAT => "Satisfiable" | THM => "Theorem" | STH => "SatisfiableAxiomsTheorem"
  | EQV => "Equivalent" | TAC => "TautologousConclusion" | WEC => "WeakerConclusion"
  | ETH => "EquivalentTheorem" | TAU => "Tautology" | WTC => "WeakerTautologousConclusion"
  | WTH => "WeakerTheorem" | CUP => "CounterUnsatisfiabilityPreserving"
  | CSP => "CounterSatisfiabilityPreserving" | CTP => "CounterTautologyPreserving"
  | ECS => "EquiCounterSatisfiable" | ECA => "EquiCounterTautologous"
  | CSA => "CounterSatisfiable" | CTH => "CounterTheorem"
  | SCT => "SatisfiableAxiomsCounterTheorem" | CEQ => "CounterEquivalent"
  | UNC => "UnsatisfiableConclusion" | WCC => "WeakerCounterConclusion"
  | ECT => "EquivalentCounterTheorem" | UNS => "Unsatisfiable"
  | WUC => "WeakerUnsatisfiableConclusion" | WCT => "WeakerCounterTheorem"
  | CAX => "ContradictoryAxioms" | SCA => "SatisfiableConclusionContradictoryAxioms"
  | SCC => "SatisfiableCounterConclusionContradictoryAxioms"
  | TCA => "TautologousConclusionContradictoryAxioms"
  | WCA => "WeakerConclusionContradictoryAxioms"
  | UCA => "UnsatisfiableConclusionContradictoryAxioms" | NOC => "NoConsequence"

/-- The status with a given three-letter code. -/
def ofCode? (c : String) : Option Status := all.find? (·.code == c)

/-- The status's semantics in the current ontology. -/
def holds {I : Type u} (s : Status) (P : Problem I) : Prop :=
  match s with
  | UNP => Current.UNP P | SAP => Current.SAP P | TAP => Current.TAP P | ESA => Current.ESA P
  | ETA => Current.ETA P | SAT => Current.SAT P | THM => Current.THM P | STH => Current.STH P
  | EQV => Current.EQV P | TAC => Current.TAC P | WEC => Current.WEC P | ETH => Current.ETH P
  | TAU => Current.TAU P | WTC => Current.WTC P | WTH => Current.WTH P | CUP => Current.CUP P
  | CSP => Current.CSP P | CTP => Current.CTP P | ECS => Current.ECS P | ECA => Current.ECA P
  | CSA => Current.CSA P | CTH => Current.CTH P | SCT => Current.SCT P | CEQ => Current.CEQ P
  | UNC => Current.UNC P | WCC => Current.WCC P | ECT => Current.ECT P | UNS => Current.UNS P
  | WUC => Current.WUC P | WCT => Current.WCT P | CAX => Current.CAX P | SCA => Current.SCA P
  | SCC => Current.SCC P | TCA => Current.TCA P | WCA => Current.WCA P | UCA => Current.UCA P
  | NOC => Current.NOC P

/-- The status's semantics in the 2007 text, for the codes that text defines. -/
def holds2007? {I : Type u} (s : Status) (P : Problem I) : Option Prop :=
  match s with
  | SAT => some (V2007.SAT P) | THM => some (V2007.THM P) | EQV => some (V2007.EQV P)
  | WTH => some (V2007.WTH P) | TAC => some (V2007.TAC P) | ETH => some (V2007.ETH P)
  | TAU => some (V2007.TAU P) | CAX => some (V2007.CAX P) | SCA => some (V2007.SCA P)
  | TCA => some (V2007.TCA P) | CSA => some (V2007.CSA P) | CTH => some (V2007.CTH P)
  | CEQ => some (V2007.CEQ P) | WCT => some (V2007.WCT P) | UNC => some (V2007.UNC P)
  | ECT => some (V2007.ECT P) | UNS => some (V2007.UNS P) | SCC => some (V2007.SCC P)
  | UCA => some (V2007.UCA P) | NOC => some (V2007.NOC P)
  | _ => none

end Status

end Silmaril.Logic.Szs

end
