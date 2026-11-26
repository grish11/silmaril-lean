module

public import Silmaril.Logic.ACL2.Books.Defs
import Silmaril.Proofs.Logic.ACL2.Books

@[expose] public section

namespace Silmaril.Logic.ACL2

open CategoryTheory Institution.Metatheory

variable {P Q : Presentation} {W V U : World} {name : Name} {n : Nat}

theorem definitionEquation_map {S T : Signature} (σ : S ⟶ T) {k : Nat}
    (f : S.Symbol k) (t : Term S k) :
    (definitionEquation f t).map σ = definitionEquation (σ.symbol f) (t.map σ) := rfl

theorem Presentation.equations_map (f : P ⟶ Q) :
    Set.MapsTo (Sentence.map f.signature) P.equations Q.equations :=
  Proofs.Logic.ACL2.Books.equations_map f

theorem Presentation.define_body_new (P : Presentation) (fresh : P.signature.arity name = none)
    (t : Term P.signature n) :
    (P.define fresh t).body (P.signature.addSymbol name n) =
      some (t.map (Signature.addInclusion fresh n)) :=
  Proofs.Logic.ACL2.Books.define_body_new P fresh t

theorem Presentation.map_derives (f : P ⟶ Q) {Γ : Set (Sentence P.signature)}
    {p : Sentence P.signature} (h : P.Derives Γ p) :
    Q.Derives (Sentence.map f.signature '' Γ) (p.map f.signature) :=
  Proofs.Logic.ACL2.Books.presentation_map_derives f h

/-- The syntactic π-institution. A declaration with a body contributes its defining equation to
the hypotheses of every derivation at that signature. -/
def Presentation.entailment : Presentation ⥤ ER where
  obj P :=
    { Sen := Sentence P.signature
      Derives := P.Derives
      refl p := .hyp (Or.inr (Set.mem_singleton p))
      mono sub h := h.weaken (Set.union_subset_union_right _ sub)
      trans cut h := h.bind fun p hp => hp.elim
        (fun hd => .hyp (Or.inl hd)) (fun h => h.elim (fun hg => .hyp (Or.inr hg)) (cut p)) }
  map f := ⟨Sentence.map f.signature, fun h => Presentation.map_derives f h⟩
  map_id _ := ER.hom_ext (funext Sentence.map_id)
  map_comp f g := ER.hom_ext (funext (Sentence.map_comp f.signature g.signature))

def pi : Institution.PiCoIns.{0, 0, 0} := ⟨Presentation, Presentation.entailment⟩

/-- The same π-institution in the category with backward sentence morphisms. -/
abbrev piIns : Institution.PiIns.{0, 0, 0} := pi

/-- Interpret definition bodies as equations in the existing presentation construction. -/
def Presentation.toPresentation : Presentation ⥤ Institution.Presentation institution where
  obj P := ⟨P.signature, P.equations⟩
  map f := ⟨f.signature, Presentation.equations_map f⟩

/-- The ordinary institution on the π-signatures, with models satisfying the named definitions. -/
def presentedInst : Institution.Inst.{0, 0, 0, 0, 1} :=
  ⟨Presentation, Presentation.toPresentation ⋙ Institution.Theory.ofPresentation institution ⋙
    Institution.Theory.institution institution⟩

/-- Forget defining equations on models. Sentence translation is the identity at each underlying
signature. The arrow points from the presented institution to the one with bare declarations. -/
def forgetDefinitions : Institution.Inst.Hom presentedInst inst where
  Φ := Presentation.toPresentation ⋙ Institution.Presentation.forget institution
  η :=
    { app := fun _ => ⟨id, CategoryTheory.ObjectProperty.ι _, fun _ _ => Iff.rfl⟩
      naturality := fun _ _ _ => Institution.Room.hom_ext rfl rfl }

/-- Syntactic consequence implies semantic consequence on the definition-aware signatures. -/
def piSound : Institution.Diagram.CoHom pi (Institution.semanticPi presentedInst) where
  Φ := 𝟭 _
  ρ :=
    { app := fun P => ⟨id, fun {_ _} h M hΓ => Derives.sound h M.obj fun p hp =>
        hp.elim (fun hd => M.property p ((room P.signature).subset_closure P.equations hd))
          (fun hg => hΓ p ⟨p, hg, rfl⟩)⟩
      naturality := fun _ _ _ => ER.hom_ext rfl }

theorem World.Extension.theory_map (e : W.Extension V) :
    Set.MapsTo (Sentence.map e.presentation.signature) W.theory V.theory :=
  Proofs.Logic.ACL2.Books.theory_map e

theorem World.Extension.models_reduct (e : W.Extension V) {M : Model V.signature} (hM : V.Models M) :
    W.Models (M.reduct e.presentation.signature) :=
  Proofs.Logic.ACL2.Books.models_reduct e hM

theorem World.Extension.provable_map (e : W.Extension V) {p : Sentence W.signature}
    (h : W.Provable p) : V.Provable (p.map e.presentation.signature) :=
  Proofs.Logic.ACL2.Books.world_provable_map e h

/-- Including a checked book preserves every previously derivable statement. -/
theorem Book.provable_include (b : Book W V) {p : Sentence W.signature}
    (h : W.Provable p) : V.Provable (p.map b.extension.presentation.signature) :=
  b.extension.provable_map h

theorem World.checked_bare (S : Signature) : (World.bare S).Checked :=
  fun _ ⟨_, h⟩ => by cases h

/-- A checked book derives its named theorems from its defining equations,
provided the input world's theorem table already has that property. -/
theorem Book.checked (b : Book W V) (hW : W.Checked) : V.Checked :=
  Proofs.Logic.ACL2.Books.book_checked b hW

theorem World.Checked.pi_derives (h : W.Checked) {p : Sentence W.signature} (proof : W.Provable p) :
    W.presentation.Derives ∅ p :=
  (h.discharge proof).weaken Set.subset_union_left

theorem World.valid_bare (S : Signature) : (World.bare S).Valid :=
  Proofs.Logic.ACL2.Books.valid_bare S

/-- With a valid input world, the new theorem table is semantically entailed by the new
definition table. Definition events preserve this invariant by model reduction. -/
theorem Book.valid (b : Book W V) (hW : W.Valid) : V.Valid :=
  Proofs.Logic.ACL2.Books.book_valid b hW

/-- Every model of the input world expands to a model of the output world of a checked book.
A new function is interpreted by evaluating its body in the old model. -/
theorem Book.expand (b : Book W V) (M : Model W.signature) (hM : W.Models M) :
    ∃ N : Model V.signature, V.Models N ∧ N.reduct b.extension.presentation.signature = M :=
  Proofs.Logic.ACL2.Books.book_expand b M hM

/-- A checked book is semantically conservative for sentences over the input signature. -/
theorem Book.entails_iff (b : Book W V) (p : Sentence W.signature) :
    V.Entails (p.map b.extension.presentation.signature) ↔ W.Entails p :=
  Proofs.Logic.ACL2.Books.book_entails_iff b p

end Silmaril.Logic.ACL2
