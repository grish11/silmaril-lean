module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Signature.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Categorical.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.FiniteExit.Institution.Thms
public import Silmaril.SSA.LambdaRTL.Quotient.Defs

/-! # Exact equations of captured tables and witnessed LetCase terms -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Institution (Room)
open Morphism (SignatureMap)
open LambdaSSA.Acyclic.Positional.Capture
open LambdaSSA.Acyclic.Positional.Capture.Reverse
open LambdaSSA.Semantics.Categorical (ctxObj labelObj denoteRegion)

variable {τ υ ε δ : Type} [TypeFormers τ] [TypeFormers υ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ}
  {d : Nat} {β : BoundCtx τ d} {L : List τ}

/-- A ranked captured table pointed at any of its local positions, with an
entry operand in the shared ambient context. -/
structure RankedEntry (Φ : Type) [HasTy Φ τ] (β : BoundCtx τ d) (L : List τ) where
  size : Nat
  table : Table Φ β L size
  checked : table.check = true
  index : Fin (size + 1)
  entry : LambdaSSA.Acyclic.Operand Φ β (table.types index)

def RankedEntry.toFiniteExit (p : RankedEntry P.Instr β L) :=
  p.table.toFiniteExit p.checked p.index p.entry

def RankedEntry.toGrammar (p : RankedEntry P.Instr β L) : Program P.Instr β L :=
  (tableGrammar p.table p.checked p.index p.entry).val

/-- Reuse the reverse compiler on the witness of the actual rendered term. -/
def ofGrammar (p : Program P.Instr β L) : RankedEntry P.Instr β L :=
  let rebuilt := (show ResultGrammar p.toLetCase from ⟨p, rfl⟩).toTable
  ⟨rebuilt.size, rebuilt.table, rebuilt.checked, 0, rebuilt.entry⟩

def RankedEntry.mapSignature (g : SignatureMap P.Instr Q.Instr τ υ ε δ)
    [g.PreservesProducts] [g.PreservesSums] (p : RankedEntry P.Instr β L) :
    RankedEntry Q.Instr (β.mapTypes g.ty) (L.map g.ty) :=
  ⟨p.size, p.table.mapSignature g, (p.table.check_mapSignature g).trans p.checked,
    p.index, p.entry.mapSignature g⟩

abbrev RankedEquation (P : InstrSig τ ε) :=
  Σ i : FiniteExitIndex τ, RankedEntry P.Instr i.bound i.exits × RankedEntry P.Instr i.bound i.exits

/-- A pair of grammar witnesses with a common ordered exit interface. Each
program carries exactly its rendered LetCase term via `⟨p, rfl⟩`. -/
abbrev GrammarEquation (P : InstrSig τ ε) :=
  Σ i : FiniteExitIndex τ, Program P.Instr i.bound i.exits × Program P.Instr i.bound i.exits

def readGrammar (e : RankedEquation P) : GrammarEquation P :=
  ⟨e.1, e.2.1.toGrammar, e.2.2.toGrammar⟩

def numberGrammar (e : GrammarEquation P) : RankedEquation P :=
  ⟨e.1, ofGrammar e.2.1, ofGrammar e.2.2⟩

def rankedFiniteExit (e : RankedEquation P) : FiniteExitEquation P :=
  ⟨e.1, e.2.1.toFiniteExit, e.2.2.toFiniteExit⟩

def grammarFiniteExit (e : GrammarEquation P) : FiniteExitEquation P :=
  ⟨e.1, e.2.1.toFiniteExit, e.2.2.toFiniteExit⟩

/-- The actual packed LetCase equation, including both exact derivations. -/
def grammarCase (e : GrammarEquation P) : CaseEquation P :=
  compileFiniteExit (grammarFiniteExit e)

variable (g : SignatureMap P.Instr Q.Instr τ υ ε δ) [g.PreservesProducts] [g.PreservesSums]

def mapRanked (e : RankedEquation P) : RankedEquation Q :=
  ⟨⟨e.1.depth, e.1.bound.mapTypes g.ty, e.1.exits.map g.ty⟩,
    e.2.1.mapSignature g, e.2.2.mapSignature g⟩

def mapGrammar (e : GrammarEquation P) : GrammarEquation Q :=
  ⟨⟨e.1.depth, e.1.bound.mapTypes g.ty, e.1.exits.map g.ty⟩,
    e.2.1.mapSignature g, e.2.2.mapSignature g⟩

variable {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]

/-- The arrow of the actual native CFG, with its original ordered exits. -/
noncomputable def denoteRanked (K : CoherentRegionModel J P) (p : RankedEntry P.Instr β L) :
    J.obj (ctxObj K.types β.toList) ⟶ J.obj (labelObj K.types L) :=
  letI := K.instructions
  denoteRegion J K.types (p.table.toSSA_hasType p.index p.entry)

noncomputable def rankedRoom (P : InstrSig τ ε) : Room.{0, 0, 1} where
  Sen := RankedEquation P
  Mod := (finiteExitRoom J P).Mod
  Sat K e := denoteRanked J K.fromShrinkHoms.as e.2.1 = denoteRanked J K.fromShrinkHoms.as e.2.2

/-- Evaluate the witnessed equations in the existing validated LetCase
models. The grammar witness restricts which sentences can be used. -/
noncomputable def grammarRoom (P : InstrSig τ ε) : Room.{0, 0, 1} where
  Sen := GrammarEquation P
  Mod := (validatedRoom J P).Mod
  Sat A e := (validatedRoom J P).Sat A (grammarCase e)

end Silmaril.Isotope.Institution.Acyclic.Captured
