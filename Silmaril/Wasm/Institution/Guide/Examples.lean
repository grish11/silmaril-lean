module

public import Silmaril.Wasm.Institution.Generic.Defs
public import Silmaril.Wasm.Unified.Inst.Thms
public import Silmaril.Logic.Institution.Examples.Comorphisms
public import Silmaril.Logic.Institution.Hets.LogicGraph

@[expose] public section

/-!
# Worked examples for the institutions guide

The compiled companion of `docs/projects/wasm-institutions-guide.md`. Every step of the guide is a definition,
a theorem or an `example` here, written against `Silmaril.Logic.Institution` and the `ObsSemantics` builder
(`Silmaril.Wasm.Institution.Generic`). The companion `Silmaril.Wasm.Institution.Guide.Facade` expresses these examples through
the current `Silmaril.Inst` facade. This file keeps the direct public-core presentation.

1. *Define a logic* from an observational semantics (`natOut`, `intOut`), and read validity of
   a concrete refinement off the denotations (`natOut_one_le`).
2. *Define a comorphism* from a translation (`natToInt`), with its model-expansiveness, and
   *borrow* validity along it (`intOut_valid_one_le`); read the same translation as an
   institution morphism (`natToIntHom`).
3. *Define a comorphism directly* (`dn`, double negation on propositional logic), *transfer
   satisfaction* along it, *compose* it with silmaril's `plToFol` and borrow entailment along
   the composite.
4. *Register logics in a logic graph* (`graph`, three nodes, three comorphism edges and one
   morphism edge), prove every path model-expansive and borrow along a path.
5. *Use the unified Wasm institution*: its satisfaction condition is the generic one, and a
   sentence over a smaller feature set transfers along an inclusion.

Nothing here is assumed: there is no `sorry`, axiom or native evaluation.
-/

namespace Silmaril.Wasm.Institution.Guide

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Wasm.Institution (ObsSemantics Sig)

/-! ## 1. A logic from an observational semantics -/

/-- Outputs over `ℕ` at a single interface: a program is a finite list of possible outputs,
refinement is inclusion, and the one operator lets a program also output `0`. -/
abbrev natOut : ObsSemantics (Discrete Unit) where
  Sem _ := Set ℕ
  restrict _ s := s
  restrict_id _ := rfl
  restrict_comp _ _ _ := rfl
  Prog := List ℕ
  den _ p := {n | n ∈ p}
  Op := Unit
  op _ _ s := s ∪ {0}
  Le _ s t := s ⊆ t

/-- The same over `ℤ`, where refinement only looks at the natural outputs. -/
abbrev intOut : ObsSemantics (Discrete Unit) where
  Sem _ := Set ℤ
  restrict _ s := s
  restrict_id _ := rfl
  restrict_comp _ _ _ := rfl
  Prog := List ℤ
  den _ p := {n | n ∈ p}
  Op := Unit
  op _ _ s := s ∪ {0}
  Le _ s t := ∀ n : ℕ, (n : ℤ) ∈ s → (n : ℤ) ∈ t

/-- The only interface. -/
abbrev pt : Discrete Unit := ⟨()⟩

/-- Validity of the closed sentence `[1] ⊑ [1, 2]` is inclusion of denotations. -/
theorem natOut_one_le : natOut.Valid (natOut.leSen pt [1] [1, 2]) := by
  rw [ObsSemantics.valid_leSen_iff]
  intro n (h : n ∈ [1])
  show n ∈ [1, 2]
  simp_all

/-- The institution of an observational semantics: signatures are pairs of program variables
and an interface. Note the explicit universe list of the result type. -/
example : Inst.{1, 0, 0, 0, 0} := natOut.inst

/-! ## 2. A comorphism from a translation -/

/-- `ℕ`-outputs embed into `ℤ`-outputs: programs map forwards along the cast, semantic objects
map backwards by taking the natural outputs. -/
def natToInt : ObsSemantics.Translation (𝟭 (Discrete Unit)) natOut intOut where
  sem _ s := {n : ℕ | (n : ℤ) ∈ s}
  sem_restrict _ _ := rfl
  prog p := p.map (Nat.cast : ℕ → ℤ)
  sem_den _ p := by
    ext n
    show (n : ℤ) ∈ p.map (Nat.cast : ℕ → ℤ) ↔ n ∈ p
    simp [Int.natCast_inj]
  op := id
  sem_op _ _ s := by
    ext n
    show (n : ℤ) ∈ s ∪ {0} ↔ n ∈ {m : ℕ | (m : ℤ) ∈ s} ∪ {0}
    simp
  atom t u := .le t u
  atom_mapVars _ _ _ := rfl
  atom_holds _ _ _ _ _ := Iff.rfl

/-- Every set of natural outputs is the natural part of a set of integer outputs, so the
comorphism of `natToInt` is model-expansive. -/
theorem natToInt_surjective (X : Discrete Unit) : Function.Surjective (natToInt.sem X) :=
  fun s => ⟨(Nat.cast : ℕ → ℤ) '' s, by ext n; simp [natToInt, Int.natCast_inj]⟩

/-- The comorphism `natOut → intOut`. -/
noncomputable def natToIntCo : Inst.CoHom natOut.inst intOut.inst := natToInt.coHom

theorem natToIntCo_modelExpansive : natToIntCo.ModelExpansive :=
  natToInt.coHom_modelExpansive natToInt_surjective

/-- Borrowing: validity in `natOut` is validity of the translated sentence in `intOut`. -/
theorem intOut_valid_one_le : intOut.Valid (natToInt.sen (natOut.leSen pt [1] [1, 2])) :=
  (natToInt.valid_iff natToInt_surjective _).1 natOut_one_le

/-- The same corridors, read as an institution morphism `intOut → natOut` (a projection). -/
noncomputable def natToIntHom : Inst.Hom intOut.inst natOut.inst := natToInt.toHom

theorem natToIntHom_sound : natToIntHom.Sound := natToInt.toHom_sound natToInt_surjective

/-! ## 3. A comorphism defined directly: double negation on propositional logic -/

open Silmaril.Logic.Institution.Examples

/-- Double negation of a propositional formula. -/
def dneg {P : Type} (φ : PL.Formula P) : PL.Formula P := .imp (.imp φ .bot) .bot

/-- The corridor of double negation at a signature: sentences are double-negated, models are
unchanged. Its satisfaction condition is `¬¬a ↔ a`. -/
def dnCorridor (P : Type) : PL.institution.obj P ⟶ (𝟭 Type ⋙ PL.institution).obj P :=
  ⟨dneg, 𝟭 _, fun _ _ => not_not⟩

/-- **Double negation as an institution comorphism** `PL → PL`. -/
def dn : Inst.CoHom PL.inst PL.inst where
  Φ := 𝟭 _
  ρ :=
    { app := dnCorridor
      naturality := fun _ _ _ => Room.hom_ext rfl rfl }

theorem dn_modelExpansive : dn.ModelExpansive := fun _ M => ⟨M, rfl⟩

/-- Transferring satisfaction along `dn`, in the generic form of silmaril. -/
example (P : Type) (v : (PL.inst.I.obj P).Mod) (φ : (PL.inst.I.obj P).Sen) :
    (PL.inst.I.obj (dn.Φ.obj P)).Sat v ((dn.ρ.app P).sen φ) ↔
      (PL.inst.I.obj P).Sat ((dn.ρ.app P).mod.obj v) φ :=
  dn.satisfaction P v φ

/-- The sentence map of `dn` computes. -/
example (P : Type) (φ : PL.Formula P) : (dn.ρ.app P).sen φ = dneg φ := rfl

/-- Composition with silmaril's `plToFol`: a comorphism `PL → FOL`. -/
def dnFol : Inst.CoHom PL.inst FOL.inst := dn.comp plToFol

/-- The composite translates a formula by double negation, then into first-order logic. -/
example (P : Type) (φ : PL.Formula P) : (dnFol.ρ.app P).sen φ = PLtoFOL.sen (dneg φ) := rfl

theorem dnFol_modelExpansive : dnFol.ModelExpansive :=
  dn_modelExpansive.comp plToFol_modelExpansive

/-- Borrowing along the composite: propositional consequence is first-order consequence of the
double-negated translations. -/
theorem pl_entails_iff_dnFol (P : Type) (Γ : Set (PL.Formula P)) (φ : PL.Formula P) :
    (PL.institution.obj P).Entails Γ φ ↔
      (FOL.institution.obj (PLtoFOL.sig P)).Entails
        ((fun ψ => PLtoFOL.sen (dneg ψ)) '' Γ) (PLtoFOL.sen (dneg φ)) :=
  dnFol.entails_iff dnFol_modelExpansive P Γ φ

/-! ## 4. A logic graph -/

/-- The logics of the example graph. -/
inductive Node where
  | pl
  | eq
  | fol

/-- The institution of each logic (all `Inst.{1, 0, 0, 0, 1}`). -/
def Node.inst : Node → Inst.{1, 0, 0, 0, 1}
  | .pl => PL.inst
  | .eq => EQ.inst
  | .fol => FOL.inst

/-- Comorphism edges. -/
inductive Edge : Node → Node → Type where
  | dnEdge : Edge .pl .pl
  | plFol : Edge .pl .fol
  | eqFol : Edge .eq .fol

/-- Morphism edges. -/
inductive Proj : Node → Node → Type where
  | folEq : Proj .fol .eq

/-- The comorphism of each edge. -/
def Edge.coHom : {a b : Node} → Edge a b → Inst.CoHom a.inst b.inst
  | _, _, .dnEdge => dn
  | _, _, .plFol => plToFol
  | _, _, .eqFol => eqToFol

/-- The morphism of each projection edge. -/
def Proj.hom : {a b : Node} → Proj a b → Inst.Hom a.inst b.inst
  | _, _, .folEq => folToEq

/-- **The example logic graph.** -/
def graph : LogicGraph.{0, 0, 1, 0, 0, 0, 1} where
  Logics := Node
  inst := Node.inst
  Comor := Edge
  comor := Edge.coHom
  Mor := Proj
  mor := Proj.hom

theorem edge_modelExpansive : ∀ {a b : Node} (e : Edge a b), e.coHom.ModelExpansive
  | _, _, .dnEdge => dn_modelExpansive
  | _, _, .plFol => plToFol_modelExpansive
  | _, _, .eqFol => eqToFol_modelExpansive

theorem proj_sound : ∀ {a b : Node} (e : Proj a b), e.hom.Sound
  | _, _, .folEq => folToEq_sound

/-- Every path of the graph is model-expansive. -/
theorem pathModelExpansive : ∀ {a b : graph.Idx} (p : Quiver.Path a b),
    graph.PathModelExpansive p
  | _, _, .nil => trivial
  | _, _, .cons p e => ⟨pathModelExpansive p, edge_modelExpansive e⟩

/-- An edge as an arrow of the comorphism quiver of `graph`. -/
def arrow {a b : Node} (e : Edge a b) : @Quiver.Hom graph.Idx _ a b := e

/-- The path `pl --dn--> pl --plFol--> fol`. -/
def dnThenFol : @Quiver.Path graph.Idx _ Node.pl Node.fol :=
  (Quiver.Path.nil.cons (arrow .dnEdge)).cons (arrow .plFol)

/-- Heterogeneous borrowing along `dnThenFol`, in the Grothendieck institution of the graph.
The statement is the (long) one of `LogicGraph.entails_lift_path_iff`; it is elaborated, not
written out. -/
example (S : (IndexedCoInst.inst graph.indexed (graph.pt .pl)).Sign) :=
  graph.entails_lift_path_iff dnThenFol (pathModelExpansive _) S

/-! ## 5. The unified Wasm institution -/

section Unified

open Silmaril.Wasm.Unified

variable {In B : Type}

/-- The satisfaction condition of the unified institution, read through silmaril's room API,
is `Unified.sat_map_iff`. -/
example {S S' : FSig} (σ : S ⟶ S') (M : Model In B S') (φ : Sen In B S) :
    ((Unified.inst In B).I.obj S').Sat M (((Unified.inst In B).I.map σ).sen φ) ↔
      ((Unified.inst In B).I.obj S).Sat (((Unified.inst In B).I.map σ).mod.obj M) φ :=
  sat_map_iff σ M φ

/-- A sentence about a smaller feature set holds of a model of a larger one exactly when it
holds of the reduct. -/
example {S S' : FSig} (h : FSig.Sub S S') (M : Model In B S') (φ : Sen In B S) :
    Unified.Sat M (φ.map (FSig.incl h)) ↔ Unified.Sat (M.reduct (FSig.incl h)) φ :=
  sat_incl_iff h M φ

/-- The unified institution lives at `Inst.{0, 0, 0, 0, 1}`: its signatures are in `Type`, so
it cannot be a node of `graph` (signatures in `Type 1`) without lifting. -/
example : Inst.{0, 0, 0, 0, 1} := Unified.inst In B

end Unified

/-! ## Axiom checks

The guide's main borrowing statements use only the standard axioms. -/

/--
info: 'Silmaril.Wasm.Institution.Guide.intOut_valid_one_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms intOut_valid_one_le

/--
info: 'Silmaril.Wasm.Institution.Guide.pl_entails_iff_dnFol' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms pl_entails_iff_dnFol

/--
info: 'Silmaril.Wasm.Institution.Guide.pathModelExpansive' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms pathModelExpansive

end Silmaril.Wasm.Institution.Guide
