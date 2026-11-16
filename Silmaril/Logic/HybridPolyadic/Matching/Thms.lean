module

public import Silmaril.Logic.HybridPolyadic.Matching.Defs
import Silmaril.Proofs.Logic.HybridPolyadic.Matching.Semantics
import Silmaril.Proofs.Logic.HybridPolyadic.Matching.Syntax

@[expose] public section
noncomputable section
namespace Silmaril.Logic.HybridPolyadic.Matching
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Matching

theorem nominal_denote {S : Signature} (M : Model S) {n : ℕ} (a : S.Nominal)
    (env : Fin n → M.base.carrier ()) (w : M.base.carrier ()) :
    w ∈ M.base.denote env (nominalPattern a) ↔ w = M.name a :=
  Silmaril.Proofs.Logic.HybridPolyadic.Matching.nominal_denote M a env w

theorem definedPattern_denote {S : Signature} (M : Model S) {n : ℕ} (p : Pattern S n)
    (env : Fin n → M.base.carrier ()) (w : M.base.carrier ()) :
    w ∈ M.base.denote env (definedPattern p) ↔ ∃ v, v ∈ M.base.denote env p :=
  Silmaril.Proofs.Logic.HybridPolyadic.Matching.defined_denote M p env w

theorem nominal_not_empty {S : Signature} (M : Model S) (a : S.Nominal) :
    M.base.operation (.nominal a) (fun i => i.elim0) ≠ ∅ := by
  intro h
  have hm : M.name a ∈ M.base.operation (.nominal a) (fun i => i.elim0) := by rw [M.nominal]; rfl
  rw [h] at hm
  exact hm

theorem nominal_members_equal {S : Signature} (M : Model S) (a : S.Nominal)
    (x y : M.base.carrier ())
    (hx : x ∈ M.base.operation (.nominal a) (fun i => i.elim0))
    (hy : y ∈ M.base.operation (.nominal a) (fun i => i.elim0)) : x = y := by
  have hx' : x = M.name a := by rw [M.nominal] at hx; exact hx
  have hy' : y = M.name a := by rw [M.nominal] at hy; exact hy
  exact hx'.trans hy'.symm

/-- The proved raw denotation law holds at every world/environment of every admitted model. -/
theorem translate_denote {S : Signature} (M : Model S) {n : ℕ}
    (p : Formula S n) (env : Fin n → M.base.carrier ()) (w : M.base.carrier ()) :
    w ∈ M.base.denote env (translate p) ↔ p.Holds (decode M) env w :=
  Silmaril.Proofs.Logic.HybridPolyadic.Matching.translate_denote M p env w

theorem translate_satisfaction {S : Signature} (M : Model S) (p : Formula S 0) :
    Sat M (translateFixedPoint p) ↔ HybridPolyadic.Sat (decode M) p :=
  translate_denote M p Fin.elim0 M.point

/-- Arrow invariance is asserted only for the proved hybrid translation image. -/
theorem translate_hom {S : Signature} {M N : Model S} (h : M ⟶ N) {n : ℕ}
    (p : Formula S n) (env : Fin n → M.base.carrier ()) (w : M.base.carrier ()) :
    w ∈ M.base.denote env (translate p) ↔
      h.map w ∈ N.base.denote (h.map ∘ env) (translate p) :=
  (translate_denote M p env w).trans
    ((p.holds_hom h env w).trans ((translate_denote N p (h.map ∘ env) (h.map w)).symm))

/-- Every admitted target arrow is a genuine sorted raw operation-graph homomorphism. -/
def forgetHom {S : Signature} {M N : Model S} (h : M ⟶ N) : FirstOrder.Model.Hom M.base N.base where
  map s := by cases s; exact h.map
  operation := by
    intro n inputs output op args result hr
    cases op with
    | atom a =>
      have he : args = (fun i => i.elim0) := funext (fun i => Fin.elim0 i)
      have hn : (fun i => h.map (args i)) = (fun i : Fin 0 => i.elim0) :=
        funext (fun i => Fin.elim0 i)
      change h.map result ∈ N.base.operation (.atom a) _
      rw [hn]
      exact (h.atoms a result).mp (by simpa only [he] using hr)
    | nominal a =>
      have hm : result = M.name a := by
        change result ∈ ({M.name a} : Set _)
        rw [← M.nominal a args]
        exact hr
      rw [N.nominal]
      exact (congrArg h.map hm).trans (h.names a)
    | action a => exact h.forth _ a result args hr
    | defined => rw [N.definedness]; trivial

def forgetFirstOrder (S : Signature) : Model S ⥤ FirstOrder.Pointed.Model () (matchingSignature S) where
  obj M := ⟨M.base, M.point⟩
  map h := ⟨forgetHom h, h.point⟩
  map_id _ := FirstOrder.Pointed.Model.Hom.ext _ _ (FirstOrder.Model.Hom.ext _ _ rfl)
  map_comp _ _ := FirstOrder.Pointed.Model.Hom.ext _ _ (FirstOrder.Model.Hom.ext _ _ rfl)

/-- Syntactic naturality holds for arbitrary symbol maps, including aliases. -/
theorem translate_map {S T : Signature} (f : S ⟶ T) {n : ℕ} (p : Formula S n) :
    FirstOrder.Pattern.map (matchingSignatureMap f) (translate p) = translate (p.map f) :=
  Silmaril.Proofs.Logic.HybridPolyadic.Matching.translate_map f p

theorem translateFixedPoint_map {S T : Signature} (f : S ⟶ T) (p : Formula S 0) :
    (translateFixedPoint p).map (matchingSignatureMap f) = translateFixedPoint (p.map f) :=
  congrArg FixedPoint.Pattern.base (translate_map f p)

private theorem model_ext {S : Signature} {M N : Model S} (hb : M.base = N.base)
    (hp : HEq M.point N.point) (hn : HEq M.name N.name) : M = N := by
  cases M; cases N; cases hb; cases hp; cases hn; rfl

private theorem hom_ext {S : Signature} {M N : Model S} (f g : M ⟶ N)
    (h : f.map = g.map) : f = g := by
  cases f; cases g; cases h; rfl

private theorem hom_hext {S : Signature} {M M' N N' : Model S} (hM : M = M') (hN : N = N')
    (f : M ⟶ N) (g : M' ⟶ N') (h : HEq f.map g.map) : HEq f g := by
  cases hM; cases hN
  exact heq_of_eq (hom_ext _ _ (eq_of_heq h))

theorem reduct_id {S : Signature} (M : Model S) : reduct (𝟙 S) M = M := by
  apply model_ext (M := reduct (𝟙 S) M) (N := M) _ HEq.rfl HEq.rfl
  change FirstOrder.SignatureMap.reduct (matchingSignatures.map (𝟙 S)) M.base = M.base
  rw [matchingSignatures.map_id]
  exact FirstOrder.SignatureMap.reduct_id M.base

theorem reduct_comp {S T U : Signature} (f : S ⟶ T) (g : T ⟶ U) (M : Model U) :
    reduct (f ≫ g) M = reduct f (reduct g M) := by
  apply model_ext (M := reduct (f ≫ g) M) (N := reduct f (reduct g M)) _ HEq.rfl HEq.rfl
  change FirstOrder.SignatureMap.reduct (matchingSignatures.map (f ≫ g)) M.base = _
  rw [matchingSignatures.map_comp]
  rfl

theorem reductFunctor_id {S : Signature} : reductFunctor (𝟙 S) = 𝟭 (Model S) := by
  apply Functor.hext reduct_id
  intro M N h
  exact hom_hext (reduct_id M) (reduct_id N) _ _ HEq.rfl

theorem reductFunctor_comp {S T U : Signature} (f : S ⟶ T) (g : T ⟶ U) :
    reductFunctor (f ≫ g) = reductFunctor g ⋙ reductFunctor f := by
  apply Functor.hext (reduct_comp f g)
  intro M N h
  exact hom_hext (reduct_comp f g M) (reduct_comp f g N) _ _ HEq.rfl

theorem sentence_map_id (S : Signature) (p : Sentence S) :
    p.map (matchingSignatureMap (𝟙 S)) = p := by
  have hsig : matchingSignatureMap (𝟙 S) = 𝟙 (matchingSignature S) := matchingSignatures.map_id S
  rw [hsig]
  exact FixedPoint.Pattern.map_id p

theorem sentence_map_comp {S T U : Signature} (f : S ⟶ T) (g : T ⟶ U) (p : Sentence S) :
    p.map (matchingSignatureMap (f ≫ g)) = (p.map (matchingSignatureMap f)).map (matchingSignatureMap g) := by
  have hsig : matchingSignatureMap (f ≫ g) = matchingSignatureMap f ≫ matchingSignatureMap g :=
    matchingSignatures.map_comp f g
  rw [hsig]
  exact FixedPoint.Pattern.map_comp (matchingSignatureMap f) (matchingSignatureMap g) p

/-- Full closed 2019 syntax over the explicitly constrained marked models.
The model-arrow policy is bounded/injective, not the unrestricted pointed
2019 institution's equality-only category. -/
def institution : Signature ⥤ Room where
  obj S := ⟨Sentence S, Cat.of (Model S), Sat⟩
  map f := ⟨FixedPoint.Pattern.map (matchingSignatureMap f), reductFunctor f, by
    intro M p
    change M.point ∈ (p.map (matchingSignatureMap f)).denote M.base _ _ ↔ _
    rw [FixedPoint.Pattern.denote_map]
    rfl⟩
  map_id S := Room.hom_ext (funext (sentence_map_id S)) reductFunctor_id
  map_comp f g := Room.hom_ext (funext (sentence_map_comp f g)) (reductFunctor_comp f g)

def inst : Inst := ⟨Signature, institution⟩

def hybridCorridor (S : Signature) : HybridPolyadic.institution.obj S ⟶ institution.obj S :=
  ⟨translateFixedPoint, decodeFunctor S, translate_satisfaction⟩

def hybridNatural : HybridPolyadic.institution ⟶ (𝟭 Signature) ⋙ institution where
  app := hybridCorridor
  naturality := by
    intro S T f
    exact Room.hom_ext (funext (fun p => (translateFixedPoint_map f p).symm)) rfl

/-- Model decoding commutes with every hybrid signature reduct. -/
theorem decode_reduct {S T : Signature} (f : S ⟶ T) (M : Model T) :
    decode (reduct f M) = (HybridPolyadic.reduct f).obj (decode M) := rfl

theorem decodeFunctor_naturality {S T : Signature} (f : S ⟶ T) :
    reductFunctor f ⋙ decodeFunctor S = decodeFunctor T ⋙ HybridPolyadic.reduct f := rfl

/-- Genuine comorphism to constrained full-syntax matching, not unrestricted matching. -/
def hybridToConstrainedMatching : Inst.CoHom HybridPolyadic.inst inst :=
  ⟨𝟭 Signature, hybridNatural⟩

@[simp] theorem decode_expand {S : Signature} (M : HybridPolyadic.Model S) : decode (expand M) = M := by
  cases M
  rfl

theorem expanded_satisfaction {S : Signature} (M : HybridPolyadic.Model S) (p : Formula S 0) :
    Sat (expand M) (translateFixedPoint p) ↔ HybridPolyadic.Sat M p := by
  rw [translate_satisfaction, decode_expand]


theorem hybridCorridor_modelExpansive (S : Signature) : Corridor.ModelExpansive (hybridCorridor S) :=
  fun M => ⟨expand M, decode_expand M⟩

theorem hybridToConstrainedMatching_modelExpansive :
    ∀ S, Corridor.ModelExpansive (hybridToConstrainedMatching.ρ.app S) :=
  hybridCorridor_modelExpansive

/-- SAT is preserved and reflected by the actual same-carrier model expansions. -/
theorem hybrid_sat_iff {S : Signature} (p : Formula S 0) :
    (∃ M : HybridPolyadic.Model S, HybridPolyadic.Sat M p) ↔
      ∃ M : Model S, Sat M (translateFixedPoint p) := by
  constructor
  · rintro ⟨M, h⟩
    exact ⟨expand M, (expanded_satisfaction M p).mpr h⟩
  · rintro ⟨M, h⟩
    exact ⟨decode M, (translate_satisfaction M p).mp h⟩

theorem hybrid_unsat_iff {S : Signature} (p : Formula S 0) :
    (¬ ∃ M : HybridPolyadic.Model S, HybridPolyadic.Sat M p) ↔
      ¬ ∃ M : Model S, Sat M (translateFixedPoint p) :=
  not_congr (hybrid_sat_iff p)

/-- Public corridor borrowing gives semantic consequence in both directions. -/
theorem hybrid_entails_iff (S : Signature) (Γ : Set (Formula S 0)) (p : Formula S 0) :
    (HybridPolyadic.institution.obj S).Entails Γ p ↔
      (institution.obj S).Entails (translateFixedPoint '' Γ) (translateFixedPoint p) :=
  (hybridCorridor S).entails_map_iff (hybridCorridor_modelExpansive S) Γ p

end Silmaril.Logic.HybridPolyadic.Matching
