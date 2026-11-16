module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Indexed.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.Object.FiniteTag

@[expose] public section

/-! # Finite mutual families as an admissible indexed-W presentation

The source has finitely many tags, a local index type for each tag, and
constructor positions whose recursive targets may name any of those tags.
The simultaneous motive and method quantify over the whole tagged family.
This is a derived-rule presentation over existing W terms, not an independent
primitive mutual term grammar.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Mutual

open W WEncoding.Terms

namespace Tags
abbrev Tag {k : ℕ} (count : ℕ) : Tm k := Encoding.Object.FiniteTag.Tag count
abbrev canonical {k count : ℕ} (tag : Fin count) : Tm k := Encoding.Object.FiniteTag.canonical tag
end Tags

/-- Source mutual data. Binder order is newest first: local index/tag,
shape/index/tag, and position/shape/index/tag, respectively. -/
structure Description (count : ℕ) where
  localIndex : Tm 1
  shape : Tm 2
  position : Tm 3
  targetTag : Tm 4
  targetIndex : Tm 4

namespace Description

/-- Replace the tagged index by its tag and local-index projections. -/
def flatten {count : ℕ} (M : Description count) : WEncoding.Terms.Description where
  index := .sigma (Tags.Tag count) M.localIndex
  shape := M.shape.bsubst (fun i => Fin.cases (.snd (.bv 0)) (fun _ => .fst (.bv 0)) i)
  position := M.position.bsubst (fun i => Fin.cases (.bv 0)
    (fun j => Fin.cases (.snd (.bv 1)) (fun _ => .fst (.bv 1)) j) i)
  next := .pair
    (M.targetTag.bsubst (fun i => Fin.cases (.bv 0)
      (fun j => Fin.cases (.bv 1)
        (fun k => Fin.cases (.snd (.bv 2)) (fun _ => .fst (.bv 2)) k) j) i))
    (M.targetIndex.bsubst (fun i => Fin.cases (.bv 0)
      (fun j => Fin.cases (.bv 1)
        (fun k => Fin.cases (.snd (.bv 2)) (fun _ => .fst (.bv 2)) k) j) i))

def taggedIndex {count : ℕ} (_M : Description count) (tag : Fin count) (i : Tm 0) : Tm 0 :=
  .pair (Tags.canonical tag) i

def localType {count : ℕ} (M : Description count) (tag : Fin count) : Tm 0 :=
  M.localIndex.lst (Tags.canonical tag)

def universeBound {count : ℕ} (M : Description count) : ℕ :=
  max M.localIndex.universeBound (max M.shape.universeBound
    (max M.position.universeBound (max M.targetTag.universeBound M.targetIndex.universeBound)))

end Description

/-- Checked source local-index formation together with the actual flattened
shape, position and recursive-target formation derivations. These are formation
premises, not certificates of a requested constructor or elimination result. -/
structure FormationData {count : ℕ} (M : Description count) (levels : RuleBudget) (n : ℕ) (Γ : Ctx)
    extends IndexedFormationData M.flatten levels n Γ where
  localIndex : ∀ x ∉ names, (Γ.cons x (Tags.Tag count)).JEqB levels ∅ (.univ n)
    (M.localIndex.open x) (M.localIndex.open x)

def FormationData.includeLevels {count : ℕ} {levels more : RuleBudget} {n : ℕ} {M : Description count} {Γ : Ctx}
    (D : FormationData M levels n Γ) (h : levels ≤ more) : FormationData M more n Γ where
  toIndexedFormationData := D.toIndexedFormationData.includeLevels h
  localIndex x hx := (D.localIndex x hx).include h

/-- Source judgments name one member of an actual finite mutual family. -/
inductive Judgment where
  | ordinary (j : W.Jdg)
  | family {count : ℕ} (M : Description count) (n : ℕ) (Γ : Ctx) (tag : Fin count) (i : Tm 0)
  | node {count : ℕ} (M : Description count) (n : ℕ) (Γ : Ctx) (tag : Fin count) (i a children : Tm 0)
  | eliminate {count : ℕ} (M : Description count) (n m : ℕ) (Γ : Ctx)
      (C step : Tm 0) (tag : Fin count) (i value : Tm 0)
  | compute {count : ℕ} (M : Description count) (n m : ℕ) (Γ : Ctx)
      (C step : Tm 0) (tag : Fin count) (i a children : Tm 0)

def Judgment.toIndexed : Judgment → Indexed.Judgment
  | .ordinary j => .ordinary j
  | .family M n Γ tag i => .family M.flatten n Γ (M.taggedIndex tag i)
  | .node M n Γ tag i a f => .node M.flatten n Γ (M.taggedIndex tag i) a f
  | .eliminate M n m Γ C s tag i t => .eliminate M.flatten n m Γ C s (M.taggedIndex tag i) t
  | .compute M n m Γ C s tag i a f => .compute M.flatten n m Γ C s (M.taggedIndex tag i) a f

def Judgment.encode (j : Judgment) : W.Jdg := j.toIndexed.encode

def Judgment.annotationBound : Judgment → ℕ
  | .ordinary _ => 0
  | .family M n _ _ _ | .node M n _ _ _ _ _ => max M.universeBound (n + 1)
  | .eliminate M n m _ _ _ _ _ _ | .compute M n m _ _ _ _ _ _ _ =>
      max M.universeBound (max (n + 1) (m + 1))

def Judgment.universeBound (j : Judgment) : ℕ :=
  max j.toIndexed.universeBound j.annotationBound

def Judgment.UsesBelow (j : Judgment) (levels : ℕ) : Prop := j.universeBound ≤ levels

/-- All mutual rules consume source derivations. The same simultaneous motive
and method cover every finite tag and every cross-family recursive position. -/
inductive Derivation (levels : ℕ) : Judgment → Prop where
  | ordinary {j : W.Jdg} (d : Ctx.JEqB levels ∅ j.Γ j.A j.a j.b) :
      Derivation levels (.ordinary j)
  | expose {j : Judgment} (d : Derivation levels j) :
      Derivation levels (.ordinary j.encode)
  | family {count n : ℕ} {M : Description count} {Γ : Ctx} {tag : Fin count} {i : Tm 0}
      (D : FormationData M levels n Γ)
      (hi : Derivation levels (.ordinary ⟨Γ, M.localType tag, i, i⟩)) :
      Derivation levels (.family M n Γ tag i)
  | node {count n : ℕ} {M : Description count} {Γ : Ctx} {tag : Fin count} {i a f : Tm 0}
      (D : FormationData M levels n Γ)
      (hi : Derivation levels (.ordinary ⟨Γ, M.localType tag, i, i⟩))
      (ha : Derivation levels (.ordinary ⟨Γ, M.flatten.shape.lst (M.taggedIndex tag i), a, a⟩))
      (hf : Derivation levels (.ordinary ⟨Γ,
        .pi (M.flatten.positionAt (M.taggedIndex tag i) a)
          (M.flatten.childFibres n (.pair (M.taggedIndex tag i) a)), f, f⟩)) :
      Derivation levels (.node M n Γ tag i a f)
  | eliminate {count n m : ℕ} {M : Description count} {Γ : Ctx}
      {C s : Tm 0} {tag : Fin count} {i t : Tm 0}
      (D : FormationData M levels n Γ) (hm : m + 1 < levels)
      (hC : Derivation levels (.ordinary ⟨Γ, M.flatten.motiveType n m, C, C⟩))
      (hs : Derivation levels (.ordinary ⟨Γ, M.flatten.indexedStepType n C, s, s⟩))
      (hi : Derivation levels (.ordinary ⟨Γ, M.localType tag, i, i⟩))
      (ht : Derivation levels (.ordinary ⟨Γ, M.flatten.fibre n (M.taggedIndex tag i), t, t⟩)) :
      Derivation levels (.eliminate M n m Γ C s tag i t)
  | compute {count n m : ℕ} {M : Description count} {Γ : Ctx}
      {C s : Tm 0} {tag : Fin count} {i a f : Tm 0}
      (D : FormationData M levels n Γ) (hm : m + 1 < levels)
      (hC : Derivation levels (.ordinary ⟨Γ, M.flatten.motiveType n m, C, C⟩))
      (hs : Derivation levels (.ordinary ⟨Γ, M.flatten.indexedStepType n C, s, s⟩))
      (hi : Derivation levels (.ordinary ⟨Γ, M.localType tag, i, i⟩))
      (ha : Derivation levels (.ordinary ⟨Γ, M.flatten.shape.lst (M.taggedIndex tag i), a, a⟩))
      (hf : Derivation levels (.ordinary ⟨Γ,
        .pi (M.flatten.positionAt (M.taggedIndex tag i) a)
          (M.flatten.fibreAt n ((M.flatten.next.lst (M.taggedIndex tag i)).lst a)), f, f⟩)) :
      Derivation levels (.compute M n m Γ C s tag i a f)

inductive Consequence (levels : ℕ) (H : Set Judgment) : Judgment → Prop where
  | hyp {j} (hj : j ∈ H) : Consequence levels H j
  | ordinary {j : W.Jdg} (d : Ctx.JEqB levels (Judgment.encode '' H) j.Γ j.A j.a j.b) :
      Consequence levels H (.ordinary j)
  | derived {j} (d : Derivation levels j) : Consequence levels H j

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Mutual
