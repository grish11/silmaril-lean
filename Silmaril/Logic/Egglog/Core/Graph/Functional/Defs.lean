module

public import Silmaril.Logic.Egglog.Core.Graph.Thms
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

@[expose] public section
namespace Silmaril.Logic.Egglog.Core.Graph.Functional
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- At most one output per input; no existence or nonempty-carrier premise. -/
def FD (S : Signature) : ObjectProperty (FOL.Structure (signature S)) := fun M =>
  ∀ {n : Nat} {w : Fin (n+1) → S.S}
    (f : S.Function n (w ∘ Fin.succ) (w 0))
    (args : ∀ i : Fin n, M.carrier (w i.succ)) (x y : M.carrier (w 0)),
    M.rel (.row (w := w) f) (Fin.cases x args) →
    M.rel (.row (w := w) f) (Fin.cases y args) → x = y

/-- These are actual public FOL structures, with every public FOL hom between them. -/
abbrev IndependentModel (S : Signature) := (FD S).FullSubcategory

/-- Keep the original FOL carriers and constructor operations, and select the tags. -/
def reconstruct {S : Signature} (M : IndependentModel S) : Core.Model S where
  carrier := M.obj.carrier
  op := M.obj.op
  rel p := M.obj.rel (.predicate p)
  row := fun {n w s} f args x => M.obj.rel (.row (w := Fin.cases s w) f) (Fin.cases x args)
  functional := by
    intro n w s f
    have h := @M.property n (Fin.cases s w)
    simp only [Function.comp_def, Fin.cases_zero, Fin.cases_succ] at h
    exact h f

/-- The old graph interpretation, now an actual public FOL functor. -/
def graphs (S : Signature) : Core.Model S ⥤ FOL.Structure (signature S) where
  obj := model
  map h :=
    { map := h.map
      map_op := h.map_op
      map_rel := fun r args hr => by
        cases r with
        | predicate p => exact h.map_rel p args hr
        | row f => exact h.row f (fun i => args i.succ) (args 0) hr }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Graphs satisfy FD by the existing, independently stated table functionality. -/
theorem graph_fd {S : Signature} (M : Core.Model S) : FD S (model M) := by
  intro n w f args x y hx hy
  exact M.functional f args x y hx hy

/-- Lift into the full subcategory without discarding any model arrows. -/
def embed (S : Signature) : Core.Model S ⥤ IndependentModel S :=
  (FD S).lift (graphs S) graph_fd

/-- Every actual FOL hom preserves the reconstructed rows as well as predicates. -/
def models (S : Signature) : IndependentModel S ⥤ Core.Model S where
  obj := reconstruct
  map {X Y} h :=
    { map := h.hom.map
      map_op := h.hom.map_op
      map_rel := fun p args hp => h.hom.map_rel (.predicate p) args hp
      row := by
        intro n w s f args x hx
        change X.obj.rel (.row (w := Fin.cases s w) f) (Fin.cases x args) at hx
        have hh := h.hom.map_rel (.row (w := Fin.cases s w) f) (Fin.cases x args) hx
        change Y.obj.rel (.row (w := Fin.cases s w) f)
          (Fin.cases (h.hom.map s x) (fun i => h.hom.map (w i) (args i)))
        convert hh using 1
        funext i
        exact Fin.cases rfl (fun _ => rfl) i }
  map_id _ := Core.Model.Hom.ext _ _ rfl
  map_comp _ _ := Core.Model.Hom.ext _ _ rfl

/-- Functionality is stable under arbitrary original signature maps. -/
theorem fd_reduct {S T : Signature} (f : S ⟶ T)
    (M : IndependentModel T) : FD S ((FOL.Structure.reduct (signatureMap f)).obj M.obj) := by
  intro n w t args x y hx hy
  exact M.property (w := f.sorts ∘ w) (f.functions t) args x y hx hy

def reduct {S T : Signature} (f : S ⟶ T) : IndependentModel T ⥤ IndependentModel S :=
  (FD S).lift ((FD T).ι ⋙ FOL.Structure.reduct (signatureMap f)) (fd_reduct f)

/-- Full FOL sentences interpreted in independently supplied FD structures. -/
def room (S : Signature) : Room.{0,0,1} :=
  ⟨FOL.Sentence (signature S), Cat.of (IndependentModel S), fun M p => p.Holds M.obj⟩

def reindex {S T : Signature} (f : S ⟶ T) : room S ⟶ room T :=
  ⟨FOL.Sentence.map (signatureMap f), reduct f,
    fun M p => FOL.Sentence.holds_map (signatureMap f) M.obj p⟩

/-- Two output variables followed by the shared input variables. This also covers
nullary tables and contexts whose sorts have empty carriers. -/
def fdContext {S : Signature} {n : Nat} (w : Fin n → S.S) (s : S.S) :
    Fin (n+2) → S.S := Fin.cases s (Fin.cases s w)

def fdFormula {S : Signature} {n w s} (f : S.Function n w s) :
    FOL.Formula (signature S) (fdContext w s) :=
  let args : ∀ i : Fin n, EQ.Term S.toSignature (fdContext w s) (w i) :=
    fun i => .var i.succ.succ
  let first : FOL.Formula (signature S) (fdContext w s) := .rel (Relation.row (w := Fin.cases s w) f)
    (Fin.cases (.var 0) args)
  let second : FOL.Formula (signature S) (fdContext w s) := .rel (Relation.row (w := Fin.cases s w) f)
    (Fin.cases (.var 1) args)
  .not (.and (.and first second) (.not (.eq (.var 0) (.var 1))))

def fdSentence {S : Signature} {n w s} (f : S.Function n w s) :
    FOL.Sentence (signature S) := EQtoFOL.closeAll (fdContext w s) (fdFormula f)

/-- The full set of table FD axioms, not an externally supplied truth oracle. -/
def fdTheory (S : Signature) : Set (FOL.Sentence (signature S)) :=
  {p | ∃ (n : Nat) (w : Fin n → S.S) (s : S.S) (f : S.Function n w s), p = fdSentence f}

end Silmaril.Logic.Egglog.Core.Graph.Functional
