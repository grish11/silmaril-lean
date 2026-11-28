module

public import Silmaril.SSA.SeaOfNodes.Loop.Institution.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-! Native loop sentences and typed CF observations at a fixed word boundary. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Institution

open CategoryTheory Silmaril.Logic.Institution
open Diamond (Val dataPorts)
open RVSDG (Tuple)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.CF.SwitchAssert (Outcome)

/-- Fix the widths of the captured inputs, single latch and single result. -/
structure Profile where
  inputs : List Width
  carried : Width
  result : Width

abbrev concrete : Diamond.Institution.Signature.{0, 0} Width := ⟨CF.Op⟩

/-- Each local primitive has a realization in the fixed CF lowering profile.
Morphisms are typed relabellings that commute with realization. -/
abbrev Signature := Over concrete

def sourceModel (S : Signature) : Diamond.Model.{0, 0, 0} S.left.op :=
  Diamond.Institution.reduct S.hom CF.model

variable {P : Diamond.Institution.Signature.{0, 0} Width}

def Admits (B : Profile) : Loop.Institution.Sentence P → Prop
  | .equation e =>
    e.inputs = inputSorts B.inputs ∧ e.out = .data B.result ∧
      e.lhs.carried = [.data B.carried] ∧ e.rhs.carried = [.data B.carried]
  | .terminates (inputs := inputs) (out := out) g =>
    inputs = inputSorts B.inputs ∧ out = .data B.result ∧ g.carried = [.data B.carried]

abbrev SourceSentence (B : Profile) (P : Diamond.Institution.Signature.{0, 0} Width) :=
  { s : Loop.Institution.Sentence P // Admits B s }

variable {B : Profile} {Q : Diamond.Institution.Signature.{0, 0} Width}

/-- Relabelling changes only producer symbols. The native sentence's
entry, latch and result widths stay fixed. -/
def SourceSentence.map (h : P ⟶ Q) (s : SourceSentence B P) : SourceSentence B Q :=
  ⟨s.val.map h, by
    obtain ⟨s, admitted⟩ := s
    cases s <;> exact admitted⟩

abbrev TargetProgram (B : Profile) :=
  Cfg TargetOp (Label B.carried B.result) B.inputs [B.result]

/-- The target sentences contain typed CFGs with the common interface. -/
inductive TargetSentence (B : Profile) where
  | equation (lhs rhs : TargetProgram B)
  | terminates (g : TargetProgram B)

/-- The checked Basic embedding observes returns independently of the
internal block labels and their argument profiles. -/
noncomputable def observeCfg {Γ : List Width} {result : Width} {Label : List Width → Type}
    (g : Cfg TargetOp Label Γ [result]) (input : Env Γ) : Part (Outcome [result]) :=
  (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed g).denotePart evalOp input

noncomputable def observe (g : TargetProgram B) (input : Env B.inputs) : Part (Outcome [B.result]) :=
  observeCfg g input

/-- Both undefined observations agree in a partial equation. Universal
termination instead requires every observation to be defined. -/
def TargetSentence.Holds : TargetSentence B → Prop
  | .equation lhs rhs => ∀ input, observe lhs input = observe rhs input
  | .terminates g => ∀ input, (observe g input).Dom

/-- Encode a native input tuple as a target environment in the same order. -/
def encodeInput : {Γ : List Width} → Tuple (Val Word) (dataPorts (inputSorts Γ)) → Env Γ
  | [], .nil => .nil
  | _ :: _, .cons value tail => .cons value (encodeInput tail)

/-- Pack a native word as the target's returned singleton, preserving its width. -/
def encodeResult {w : Width} (value : Word w) : Outcome [w] :=
  .returned (.cons value .nil)

def lowerProgram (g : Loop.Institution.Program concrete (inputSorts B.inputs) (.data B.result))
    (oneLatch : g.carried = [.data B.carried]) : TargetProgram B := by
  rcases g with ⟨carried, entrySigs, headerSigs, g⟩
  cases oneLatch
  exact lower g

def translateProgram (S : Signature)
    (g : Loop.Institution.Program S.left (inputSorts B.inputs) (.data B.result))
    (oneLatch : g.carried = [.data B.carried]) : TargetProgram B :=
  lowerProgram (g.map S.hom) oneLatch

/-- Translate a concrete native sentence by lowering each of its loops. -/
def lowerSentence (s : SourceSentence B concrete) : TargetSentence B := by
  obtain ⟨s, admitted⟩ := s
  cases s with
  | equation e =>
    rcases e with ⟨inputs, out, lhs, rhs⟩
    obtain ⟨sameInputs, sameResult, leftLatch, rightLatch⟩ := admitted
    change inputs = inputSorts B.inputs at sameInputs
    change out = .data B.result at sameResult
    subst inputs
    subst out
    exact .equation (lowerProgram lhs leftLatch) (lowerProgram rhs rightLatch)
  | terminates g =>
    obtain ⟨sameInputs, sameResult, latch⟩ := admitted
    cases sameInputs
    cases sameResult
    exact .terminates (lowerProgram g latch)

/-- Realize the source symbols, then use the concrete CFG lowering. -/
def translate (S : Signature) (s : SourceSentence B S.left) : TargetSentence B :=
  lowerSentence (s.map S.hom)

/-- Each realized signature has one matched model, the reduct of the
concrete bit-vector model. -/
def sourceRoom (B : Profile) (S : Signature) : Room.{0, 0, 0} where
  Sen := SourceSentence B S.left
  Mod := Cat.of (Discrete Unit)
  Sat _ s := s.val.Holds (sourceModel S)

/-- The target has one matched evaluator, the concrete CFG interpreter. -/
def targetRoom (B : Profile) : Room.{0, 0, 0} where
  Sen := TargetSentence B
  Mod := Cat.of (Discrete Unit)
  Sat _ s := s.Holds

end Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Institution
