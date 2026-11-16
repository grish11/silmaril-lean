module

public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeEncoding.Defs
import Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeEncoding

@[expose] public section
namespace Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeEncoding
open CategoryTheory

/-- A source-typed interpretation becomes an actual native term-valued encoding.
Declaration-image typings are derived from source proofs, not assumed. -/
def encoding {S T : Institution.Signature} (F : S ⟶ T) :
    Encoding (presentation S) (presentation T) where
  toConstantAssignment := assignment F
  declared := by exact Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeEncoding.declared F
  rules := by exact Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeEncoding.rules F

/-- Native compilation commutes with source substitution on every source term,
including the shared constructors represented by the fixed non-LF placeholder. -/
theorem term_map {S T : Institution.Signature} (F : S ⟶ T)
    (t : IntensionalMLTT.Term S.scope) :
    (encoding F).term (NativeConversion.term (NativeSignature.globals (names S.scope)) t) =
      NativeConversion.term (NativeSignature.globals (names T.scope)) (t.subst F.terms) :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeEncoding.term_map F t

/-- Independently formed source LF signatures and actual typed substitutions
map functorially to native typed presentations and term-valued encodings.
Functor laws hold on all native constant names, including undeclared ones. -/
def functor : Institution.Signature ⥤ TypedPresentation where
  obj := presentation
  map := encoding
  map_id S := by
    apply Encoding.ext
    funext c
    exact Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeEncoding.image_identity S c
  map_comp F G := by
    apply Encoding.ext
    funext c
    exact Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeEncoding.image_comp F G c

/-- Native closed-theory institutions connected by the compiled source maps.
These reuse native entailment semantics, rather than source substitution models. -/
noncomputable def institutions : Institution.Signature ⥤ Silmaril.Logic.Institution.CoIns.{0, 0, 0, 0, 0} :=
  functor ⋙ encodingInstitutions

/-- The compiled source maps give Hets comorphism edges between native institutions. -/
noncomputable def hets : Silmaril.Logic.Institution.LogicGraph.{0, 0, 0, 0, 0, 0, 0} :=
  Silmaril.Logic.Institution.IndexedCoInst.toLogicGraph institutions

end Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeEncoding
