module

public import Silmaril.Wasm.Institution.Guide.Examples
public import Silmaril.Logic.Inst.Graph.Defs
public import Silmaril.Logic.Inst.Builders.Defs
public import Silmaril.Wasm.InstObs.Defs
public import Silmaril.Wasm.Institution.Api.Defs
public import Silmaril.Wasm.Unified.Api.Defs
public import Silmaril.Games.InstGraph.Defs
public import Silmaril.Games.InstFacade.Defs
public import Silmaril.Games.Examples.Counter.Examples
public import Silmaril.Wasm.SpecTec.GrammarInst.Facade.Defs
public import Silmaril.Wasm.Spec.InstFacade.Defs
public import Silmaril.Wasm.Atlas.Defs

@[expose] public section

/-!
# Worked examples for the institutions guide, through the facade

The compiled companion of the *facade* blocks of `docs/projects/wasm-institutions-guide.md`. Sections 1–5
restate the examples of `Silmaril.Wasm.Institution.Guide.Examples` (written against silmaril's
`Inst` directly) under the facade namespace `Silmaril.Inst` (`Silmaril.Logic.Inst`); sections 6–10
add examples for the other institution families of Silmaril.

1. *A logic*: `natOut.inst : Institution₁`, validity in the facade (`natOut_one_le'`).
2. *A comorphism from a translation*: `Comorphism.ofObs`, borrowing validity.
3. *A comorphism defined directly*: `dn` at the facade type, transfer by `simp`, `≫ᶜ`, `𝟙ᶜ`,
   borrowing along a composite.
4. *A logic graph*: `GraphSpec` with edge lists; every path model-expansive; borrowing along a
   path written out (through `Silmaril.Wasm.Institution.LogicGraph.AllExpansive`).
5. *The unified Wasm institution* through the facade.
6. *The Wasm API layer*: its graphs are `LogicGraph₁`s, `ExpTranslation` gives a facade
   comorphism with borrowing and no side condition.
7. *Games*: `GInst` as an `Institution₁`, transfer with `⊨[GInst]`, a game reading as a
   facade comorphism, the game graph as a `GraphSpec`.
8. *SpecTec grammar institutions*: `fullCoHom` as a facade comorphism, borrowing.
9. *`Spec.Format`*: `Spec.inst L S : Institution₀`, logic maps compose with `≫ᶜ`.
10. *Atlas*: a chart as a one-signature facade institution, and a transition with a section of
    its point map as a semi-comorphism.

Nothing here is assumed: there is no `sorry`, axiom or native evaluation. The axiom checks at the
end are `#guard_msgs` tests.
-/

namespace Silmaril.Wasm.Institution.Guide.Facade

open CategoryTheory Silmaril.Logic.Institution Silmaril.Inst
open Silmaril.Wasm.Institution (ObsSemantics Sig)
open Silmaril.Wasm.Institution.Guide

/-! ## 1. A logic -/

/-- The observational logic of section 1 has the facade type `Institution₁`; no universe list. -/
example : Institution₁ := natOut.inst

/-- The facade builder is the same institution. -/
example : Institution.ofObs natOut = natOut.inst := rfl

/-- Validity in the facade is the generic validity. -/
theorem natOut_one_le' : (Institution.ofObs natOut).Valid (natOut.leSen pt [1] [1, 2]) :=
  (valid_ofObs_iff natOut _).2 natOut_one_le

/-! ## 2. A comorphism from a translation -/

/-- `natToInt` as a facade comorphism. -/
noncomputable def natToIntC : Comorphism (Institution.ofObs natOut) (Institution.ofObs intOut) :=
  Comorphism.ofObs natToInt

theorem natToIntC_modelExpansive : natToIntC.ModelExpansive :=
  Comorphism.ofObs_modelExpansive natToInt natToInt_surjective

/-- Borrowing validity, with dot notation on the facade-typed comorphism. -/
theorem intOut_valid_one_le' :
    (Institution.ofObs intOut).Valid (natToIntC.sen _ (natOut.leSen pt [1] [1, 2])) :=
  (natToIntC.valid_iff natToIntC_modelExpansive _).1 natOut_one_le'

/-- The facade sentence translation is the translation's own. -/
example : natToIntC.sen _ (natOut.leSen pt [1] [1, 2]) = natToInt.sen (natOut.leSen pt [1] [1, 2]) :=
  rfl

/-! ## 3. A comorphism defined directly -/

open Silmaril.Logic.Institution.Examples

/-- Propositional logic at a facade type, so that dot notation (`PLf.Mod`) works. -/
abbrev PLf : Institution.{1, 0, 0, 0, 1} := PL.inst

/-- First-order logic at a facade type. -/
abbrev FOLf : Institution.{1, 0, 0, 0, 1} := FOL.inst

/-- `dn` ascribed the facade type. -/
def dnC : Comorphism PLf PLf := dn

/-- Transfer of satisfaction: a `simp` lemma (`Comorphism.sat_sen_iff`). -/
example (P : PLf.Sign) (v : PLf.Mod (dnC.sig P)) (φ : PLf.Sen P) :
    v ⊨[PLf] dnC.sen P φ ↔ dnC.mod P v ⊨[PLf] φ := by
  simp

/-- Composition with `≫ᶜ`; the identity law holds by `rfl`. -/
def dnFolC : Comorphism PLf FOLf := dnC ≫ᶜ plToFol

example : 𝟙ᶜ PLf ≫ᶜ dnC = dnC := Comorphism.id_comp dnC

/-- The composite translation computes. -/
example (P : Type) (φ : PL.Formula P) : dnFolC.sen P φ = PLtoFOL.sen (dneg φ) := rfl

/-- Borrowing along the composite, stated with facade projections. -/
theorem pl_entails_iff_dnFol' (P : Type) (Γ : Set (PLf.Sen P)) (φ : PLf.Sen P) :
    PLf.Entails Γ φ ↔ FOLf.Entails (dnFolC.sen P '' Γ) (dnFolC.sen P φ) :=
  dnFolC.entails_iff (Comorphism.ModelExpansive.comp dn_modelExpansive plToFol_modelExpansive)
    P Γ φ

/-- The facade statement is the silmaril one (`pl_entails_iff_dnFol`), word for word. -/
example (P : Type) (Γ : Set (PL.Formula P)) (φ : PL.Formula P) :
    pl_entails_iff_dnFol' P Γ φ = pl_entails_iff_dnFol P Γ φ := rfl

/-! ## 4. A logic graph with `GraphSpec` -/

/-- The graph of section 4 as edge lists: no edge inductive types, no `match`. -/
def spec : GraphSpec Node.inst where
  comors := [⟨.pl, .pl, dn⟩, ⟨.pl, .fol, plToFol⟩, ⟨.eq, .fol, eqToFol⟩]
  mors := [⟨.fol, .eq, folToEq⟩]

/-- One fact per listed edge. -/
theorem spec_allModelExpansive : spec.AllModelExpansive :=
  spec.allModelExpansive_of_forall fun i => by
    match i with
    | ⟨0, _⟩ => exact dn_modelExpansive
    | ⟨1, _⟩ => exact plToFol_modelExpansive
    | ⟨2, _⟩ => exact eqToFol_modelExpansive

/-- Every path is model-expansive. -/
theorem spec_pathModelExpansive {a b : Node} (p : Quiver.Path (V := spec.toLogicGraph.Idx) a b) :
    spec.toLogicGraph.PathModelExpansive p :=
  spec.pathModelExpansive spec_allModelExpansive p

/-- The same fact in the form of the Wasm API (`LogicGraph.AllExpansive`), which carries the
short borrowing lemma. -/
theorem spec_allExpansive : Silmaril.Wasm.Institution.LogicGraph.AllExpansive spec.toLogicGraph :=
  ⟨fun e => spec.comor_modelExpansive spec_allModelExpansive e⟩

/-- The path `pl --dn--> pl --plFol--> fol`, from list indices. -/
def dnThenFolS : Quiver.Path (V := spec.toLogicGraph.Idx) Node.pl Node.fol :=
  (Quiver.Path.nil.cons (spec.coEdge ⟨0, by decide⟩)).cons (spec.coEdge ⟨1, by decide⟩)

section Borrow

open Silmaril.Wasm.Institution.LogicGraph (Sign FlatRoom pathSig pathSen)

/-- **Borrowing along a path**, written out with the named parts `FlatRoom`, `pathSig` and
`pathSen` (silmaril's `LogicGraph.entails_lift_path_iff` can only be elaborated, not written
briefly). -/
theorem spec_borrow (S : Sign spec.toLogicGraph Node.pl)
    (Γ : Set (FlatRoom spec.toLogicGraph Node.pl S).Sen)
    (φ : (FlatRoom spec.toLogicGraph Node.pl S).Sen) :
    (FlatRoom spec.toLogicGraph Node.pl S).Entails Γ φ ↔
      (FlatRoom spec.toLogicGraph Node.fol (pathSig _ dnThenFolS S)).Entails
        (pathSen _ dnThenFolS S '' Γ) (pathSen _ dnThenFolS S φ) :=
  spec_allExpansive.entails_path_iff dnThenFolS S Γ φ

end Borrow

/-! ## 5. The unified Wasm institution -/

section Unified

open Silmaril.Wasm.Unified

variable {In B : Type}

/-- The unified institution at a facade type (`Institution.{0, 0, 0, 0, 1}`). -/
abbrev Uf (In B : Type) : Institution.{0, 0, 0, 0, 1} := Unified.inst In B

/-- The Wasm API's universe-free name is the same type. -/
example : Unified.UInst = Institution.{0, 0, 0, 0, 1} := rfl

/-- The satisfaction condition, through the facade: `simp`. -/
example {S S' : (Uf In B).Sign} (σ : S ⟶ S') (M : (Uf In B).Mod S') (φ : (Uf In B).Sen S) :
    M ⊨[Uf In B] (Uf In B).map σ φ ↔ (Uf In B).reduct σ M ⊨[Uf In B] φ := by
  simp

/-- The facade notions unfold to the unified ones by `rfl`. -/
example {S S' : FSig} (h : FSig.Sub S S') (M : Model In B S') (φ : Sen In B S) :
    M ⊨[Uf In B] (Uf In B).map (FSig.incl h) φ ↔ Unified.Sat (M.reduct (FSig.incl h)) φ :=
  sat_incl_iff h M φ

end Unified

/-! ## 6. The Wasm API layer -/

section WasmApi

open Silmaril.Wasm.Institution

/-- The Wasm logic graphs are the facade's `LogicGraph₁`: the logic-graph shape of
`GraphSpec`s over `Institution₁` with nodes and edges in `Type`. -/
example : Silmaril.Inst.LogicGraph₁ = Silmaril.Logic.Institution.LogicGraph.{0, 0, 1, 0, 0, 0, 0} :=
  rfl

variable {I J : Type} [Category.{0} I] [Category.{0} J] {F : I ⥤ J} {A : ObsSemantics I}
  {B : ObsSemantics J}

/-- An `ExpTranslation` (a translation bundled with surjective semantic maps) is a facade
comorphism with borrowing and no side condition. -/
example (T : ObsSemantics.ExpTranslation F A B) {K : Sig I} (s : ObsSemantics.Sen A K) :
    (Institution.ofObs A).Valid s ↔ (Institution.ofObs B).Valid (T.sen s) :=
  Comorphism.valid_iff (Comorphism.ofObs T.toTranslation) T.modelExpansive s

end WasmApi

/-! ## 7. Games -/

section Games

open Silmaril.Games Silmaril.Games.Examples.Counter

/-- The game institution has the facade type `Institution₁`. -/
example : Institution₁ := GInst

/-- Satisfaction of a translated sentence, with the facade's notation: `simpa` with the game
unfolding lemmas. -/
example (n : ℕ) :
    (show Institution.Mod GInst cellGame from counter n) ⊨[GInst] Institution.map GInst ι (GSen.box (ConstAns n)) := by
  simpa using reduct_counter_const n

/-- The facade transfer lemma at `GInst` is the classic one, `GInst.sat_iff`. -/
example (n : ℕ) :
    (show Institution.Mod GInst cellGame from counter n) ⊨[GInst] Institution.map GInst ι (GSen.box (ConstAns n)) ↔
      Institution.reduct GInst ι (counter n) ⊨[GInst] GSen.box (ConstAns n) :=
  Institution.sat_map_iff (A := GInst) ι (counter n) _

/-- The identity reading of `GInstRef`, as a facade comorphism. -/
def refReading : GInst.Reading GInstRef where
  game := 𝟭 _
  mod _ σ := σ
  mod_reduct _ _ := rfl

def refC : Comorphism GInstRef GInst := refReading.coHom

example : refC = GInstRef.toGInst := rfl

/-- Borrowing along a surjective reading, with the facade's `entails_iff`. -/
example (G : Game.{0}) (Γ : Set (Institution.Sen GInstRef G)) (φ : Institution.Sen GInstRef G) :
    Institution.Entails GInstRef Γ φ ↔
      Institution.Entails GInst (refC.sen G '' Γ) (refC.sen G φ) :=
  refC.entails_iff (refReading.modelExpansive fun _ => Function.surjective_id) G Γ φ

/-- The game logic graph `GInstRef → GInst → DGInst` as a `GraphSpec`. -/
def gameSpec : GraphSpec InstGraph.inst where
  comors := [⟨.ref, .plain, GInstRef.toGInst⟩, ⟨.plain, .div, GInst.toDGInst⟩]

theorem gameSpec_allModelExpansive : gameSpec.AllModelExpansive :=
  gameSpec.allModelExpansive_of_forall fun i => by
    match i with
    | ⟨0, _⟩ => exact GInstRef.toGInst_modelExpansive
    | ⟨1, _⟩ => exact GInst.toDGInst_modelExpansive

theorem gameSpec_pathModelExpansive {a b : InstGraph.Node}
    (p : Quiver.Path (V := gameSpec.toLogicGraph.Idx) a b) :
    gameSpec.toLogicGraph.PathModelExpansive p :=
  gameSpec.pathModelExpansive gameSpec_allModelExpansive p

end Games

/-! ## 8. SpecTec grammar institutions -/

section Grammar

open Silmaril.Wasm.SpecTec.GrammarInst
open Silmaril.SpecTec.Grammar (Attr)

variable {α β : Type} {A : Attr α} {B : Attr β}

/-- Grammar institutions have the facade type `Institution₁`. -/
example (D : Type) : Institution₁ := inst A D

/-- The full comorphism along an attribute homomorphism, at the facade type. -/
def fullC (f : AttrHom A B) (D : Type) : Comorphism (inst A D) (instIn B f.toFun D) :=
  fullCoHom f D

/-- Transfer of satisfaction is the facade's `sat_sen_iff`. -/
example (f : AttrHom A B) (D : Type) (S : Silmaril.Wasm.SpecTec.GrammarInst.Sig D)
    (M : Institution.Mod (instIn B f.toFun D) S)
    (φ : Institution.Sen (inst A D) S) :
    M ⊨[instIn B f.toFun D] (fullC f D).sen S φ ↔ (fullC f D).mod S M ⊨[inst A D] φ :=
  Comorphism.sat_sen_iff (fullC f D) S M φ

/-- Borrowing along `fullCoHom`, through the facade. -/
example (f : AttrHom A B) (D : Type) (S : Silmaril.Wasm.SpecTec.GrammarInst.Sig D)
    (Γ : Set (Institution.Sen (inst A D) S))
    (φ : Institution.Sen (inst A D) S) :
    Institution.Entails (inst A D) Γ φ ↔
      Institution.Entails (instIn B f.toFun D) ((fullC f D).sen S '' Γ) ((fullC f D).sen S φ) :=
  (fullC f D).entails_iff (fullCoHom_modelExpansive f D) S Γ φ

end Grammar

/-! ## 9. `Spec.Format` -/

section SpecFormat

open Silmaril.Wasm.Spec

variable {Ty A R : Type} (L L' L'' : Logic Ty A R) (S : Semantics Ty A R)

/-- The trace-specification institution has the facade type `Institution₀`. -/
example : Institution₀ := inst L S

/-- Logic maps compose as facade comorphisms (`LogicMap.coHom_comp`, `rfl`). -/
example (f : LogicMap L L') (g : LogicMap L' L'') :
    (f.comp g).coHom S = (f.coHom S : Comorphism _ _) ≫ᶜ g.coHom S := rfl

/-- … and the identity logic map gives `𝟙ᶜ`. -/
example : (LogicMap.id L).coHom S = 𝟙ᶜ (inst L S) := rfl

/-- Transfer of satisfaction along a logic map: models are unchanged. -/
example (f : LogicMap L L') {X : Iface Ty} (M : Model S X) (s : Sen L X) :
    M ⊨[inst L' S] Comorphism.sen (f.coHom S) X s ↔ M ⊨[inst L S] s :=
  Comorphism.sat_sen_iff (f.coHom S) X M s

end SpecFormat

/-! ## 10. Atlas charts -/

section Atlas

open Silmaril.Wasm.Atlas

/-- A chart as a one-signature facade institution: models are the points of its domain. -/
def chartPlain (C : Chart.{0, 0}) : Plain (Discrete Unit) where
  Sen _ := C.Sen
  map _ φ := φ
  map_id _ _ := rfl
  map_comp _ _ _ := rfl
  Mod _ := {p : C.Pt // C.dom p}
  reduct _ M := M
  reduct_id _ _ := rfl
  reduct_comp _ _ _ := rfl
  Sat M φ := C.Sat M.1 φ
  sat_map _ _ _ := Iff.rfl

/-- The institution of a chart. -/
abbrev chartInst (C : Chart.{0, 0}) : Institution.{0, 0, 0, 0, 0} := (chartPlain C).toInst

/-- **A transition with a section of its point map is a semi-comorphism.** Transitions map
points forwards, comorphisms map models backwards; given `back`, a source point over every
target point of the domain, the transition's direction and class become the semi-comorphism's.
-/
def transitionSemi {C D : Chart.{0, 0}} (T : Transition C D)
    (back : {q : D.Pt // D.dom q} → {p : C.Pt // C.dom p}) (hback : ∀ q, T.pt (back q).1 = q.1) :
    SemiComorphism (chartInst C) (chartInst D) where
  sig S := S
  sen _ φ := T.sen φ
  mod _ q := back q
  cls _ φ := T.cls φ
  Fwd := T.dir.fwd = true
  Bwd := T.dir.bwd = true
  sat_fwd hf _ q φ hc h := by
    have e : T.pt (back q).1 = q.1 := hback q
    have := (T.sat (back q).1 φ (back q).2 hc).1 hf h
    rwa [e] at this
  sat_bwd hb _ q φ hc h := by
    have e : T.pt (back q).1 = q.1 := hback q
    have h' : D.Sat (T.pt (back q).1) (T.sen φ) := by rwa [e]
    exact (T.sat (back q).1 φ (back q).2 hc).2 hb h'

/-- For an `equal` transition, satisfaction transfers both ways on the class. -/
example {C D : Chart.{0, 0}} (T : Transition C D) (hT : T.dir = .equal)
    (back : {q : D.Pt // D.dom q} → {p : C.Pt // C.dom p}) (hback : ∀ q, T.pt (back q).1 = q.1)
    (q : (chartInst D).Mod (Discrete.mk ())) (φ : C.Sen) (hc : T.cls φ) :
    q ⊨[chartInst D] (transitionSemi T back hback).sen _ φ ↔
      (transitionSemi T back hback).mod _ q ⊨[chartInst C] φ :=
  SemiComorphism.sat_sen_iff (transitionSemi T back hback)
    (show T.dir.fwd = true by rw [hT]; rfl) (show T.dir.bwd = true by rw [hT]; rfl)
    (S := Discrete.mk ()) hc q

end Atlas

/-! ## Axiom checks -/

/--
info: 'Silmaril.Wasm.Institution.Guide.Facade.intOut_valid_one_le'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms intOut_valid_one_le'

/--
info: 'Silmaril.Wasm.Institution.Guide.Facade.pl_entails_iff_dnFol'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms pl_entails_iff_dnFol'

/--
info: 'Silmaril.Wasm.Institution.Guide.Facade.spec_borrow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms spec_borrow

/--
info: 'Silmaril.Wasm.Institution.Guide.Facade.gameSpec_pathModelExpansive' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms gameSpec_pathModelExpansive

/--
info: 'Silmaril.Wasm.Institution.Guide.Facade.transitionSemi' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms transitionSemi

end Silmaril.Wasm.Institution.Guide.Facade
