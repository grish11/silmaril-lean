module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Categorical.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Dispatcher
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Categorical.Realization.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.FiniteExit.Categorical.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.Renaming.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (fst snd)
open LambdaSSA.Semantics.Categorical
open LambdaSSA.Semantics.Categorical.SingletonDispatcher (labelInject_payload)
open LetIter.Semantics.Categorical (TypeModel InstructionModel extend_postmap bind_pre_map case_pre_map
  bind_retainEnvironment)
open LetIter.ProofRelevant.Semantics.Categorical (extend caseWithContext)
open Morphism.CaseSSA (erase erase_hasType erase_rename up_ren_related)

local notation "bindArrow" => LetIter.ProofRelevant.Semantics.Categorical.bind

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v x y h k

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type x} {C : Type y} [Category.{h} V] [Category.{k} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]
  {d : Nat} {β : BoundCtx τ d} {L : LCtx τ} {n : Nat}
  {m : Nat} {γ : BoundCtx τ m}

local notation "E" => ctxObj M β.toList
local notation "G" => ctxObj M γ.toList

omit [TypeFormers τ] in
private theorem Scope.ren : {m : Nat} → {γ : BoundCtx τ m} → (s : Scope β γ) →
    Ren β.toList γ.toList s.indices
  | _, _, .base => Ren.id _
  | _, _, .skip s A => s.ren.comp (Ren.wk _ A)

omit [TypeFormers τ] in
private theorem Scope.related (s : Scope β γ) (i : Fin d) :
    (s.renaming.toFun i).val = s.indices i.val := by
  induction s with
  | base => rfl
  | skip s A ih =>
    change (s.renaming.toFun i).val.succ = (s.indices i.val).succ
    exact congrArg Nat.succ ih

omit [StrongElgotFreydCategory J] [ElgotCategory C] [Iteration C] [DistributivePremonoidalCategory C]
  [DistributiveTensor V] [HasFiniteCoproducts C] [SymmetricPremonoidalCategory C]
  [PremonoidalCategory C] [SymmetricCategory V] in
private theorem Scope.lookup_projection (s : Scope β γ) {i : Nat} {A : τ} (hi : At β.toList i A) :
    s.projection M ≫ lookup M i hi = lookup M (s.indices i) (s.ren hi) := by
  induction s with
  | base => simp [Scope.projection, Scope.indices]
  | skip s B ih =>
    change (fst _ (M.obj B) ≫ s.projection M) ≫ lookup M i hi =
      fst _ (M.obj B) ≫ lookup M (s.indices i) (s.ren hi)
    rw [Category.assoc, ih]

omit [StrongElgotFreydCategory J] [ElgotCategory C] [Iteration C] [DistributivePremonoidalCategory C]
  [DistributiveTensor V] [HasFiniteCoproducts C] [SymmetricPremonoidalCategory C]
  [PremonoidalCategory C] [SymmetricCategory V] in
private theorem Scope.lookup_packet (s : Scope β γ) (A : τ)
    {i : Nat} {B : τ} (hi : At (A :: β.toList) i B) :
    (s.projection M ▷ M.obj A) ≫ lookup M i hi =
      lookup M (Silmaril.DeBruijn.lift s.indices i) ((s.ren.lift A) hi) := by
  cases i with
  | zero =>
    cases Option.some.inj hi
    simp [lookup, Silmaril.DeBruijn.lift]
  | succ i =>
    change (s.projection M ▷ M.obj A) ≫ (fst E (M.obj A) ≫ lookup M i hi) =
      fst G (M.obj A) ≫ lookup M (s.indices i) (s.ren hi)
    rw [CartesianMonoidalCategory.whiskerRight_fst_assoc, s.lookup_projection M hi]

private theorem Scope.operand_denotes (s : Scope β γ) {A B : τ} (a : Operand Φ (β.snoc A) B) :
    Denotes J M (erase_hasType (s.operand a).2.toHasType)
      (J.map (s.projection M ▷ M.obj A) ≫ denoteOperand J M a) := by
  have orig := denote_spec J M (erase_hasType a.2.toHasType)
  have mapped := orig.rename J M (s.ren.lift A) (fun _ _ hi => s.lookup_packet M A hi)
  have same : erase (s.operand a).1 = LambdaSSA.Tm.rename (Silmaril.DeBruijn.lift s.indices) (erase a.1) :=
    erase_rename (s.renaming.up A).toFun _ (up_ren_related s.related) a.1
  have transport {t t' : LambdaSSA.Tm Φ} {Γ : VCtx τ} (eq : t = t')
      {ht : LambdaSSA.Tm.HasType Γ t B} {ht' : LambdaSSA.Tm.HasType Γ t' B} {f} :
      Denotes J M ht' f → Denotes J M ht f := by
    cases eq
    exact id
  exact transport same mapped

variable [FreydCategory.CentralUnit J] [RegionTypingCoherent (Φ := Φ) J M]

private theorem join_operand {A : τ} (a : Operand Φ γ A) (b : FiniteExit Φ L (γ.snoc A))
    {f : J.obj G ⟶ J.obj (M.obj A)} (da : Denotes J M (erase_hasType a.2.toHasType) f) :
    denoteRegion J M (FiniteExit.join (.br a) b).toSSA_hasType =
      bindArrow J f (denoteRegion J M b.toSSA_hasType) := by
  let ha := (Code.br a).toSSA_hasType (L := [A]) (exit := 0) rfl
  rw [FiniteExit.denote_linkSingleton J M ha b.toSSA_hasType _,
    ← (RegionDenotes.br (h := (rfl : At [A] 0 A)) da).eq_denote J M]
  change extend J (f ≫ J.map (labelInject M 0 (L := [A]) rfl)) ≫
    J.map (G ◁ singletonLabelPayload M A) ≫ denoteRegion J M b.toSSA_hasType = _
  rw [extend_postmap, Category.assoc, ← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp,
    labelInject_payload, MonoidalCategory.whiskerLeft_id, J.map_id, Category.id_comp]
  rfl

private abbrev Continues (p : Table Φ β L n) {targets : List (Fin (n + 1))}
    (next : LocalContinuations β p.types L Φ targets) : Prop :=
  ∀ j (edge : j ∈ targets) {m : Nat} {γ : BoundCtx τ m} (s : Scope β γ),
    denoteRegion J M (next j edge s).toSSA_hasType =
      J.map (s.projection M ▷ M.obj (p.types j)) ≫ p.resultAt J M j

omit [FreydCategory.CentralUnit J] in
private theorem target_compile (p : Table Φ β L n) {A : τ} (t : Target p.types L A)
    {targets : List (Fin (n + 1))} (edge : ∀ j ∈ t.locals, j ∈ targets) (s : Scope β γ)
    (next : LocalContinuations β p.types L Φ targets) (ih : Continues J M p next) :
    denoteRegion J M (t.compile edge s next).toSSA_hasType =
      J.map (s.projection M ▷ M.obj A) ≫ t.route J M p := by
  cases t with
  | «local» j => exact ih j (edge j (by simp [Target.locals])) s
  | exit h =>
    rw [Target.route, ← J.map_comp, CartesianMonoidalCategory.whiskerRight_snd_assoc]
    exact ((RegionDenotes.br (h := h) (Denotes.var (J := J) (M := M) (i := 0) rfl)).eq_denote).symm.trans
      (by rw [← J.map_comp]; rfl)

omit [FreydCategory.CentralUnit J] [RegionTypingCoherent (Φ := Φ) J M]
  [StrongElgotFreydCategory J] [ElgotCategory C] [Iteration C] [DistributivePremonoidalCategory C]
  [DistributiveTensor V] [HasFiniteCoproducts C] [SymmetricPremonoidalCategory C]
  [PremonoidalCategory C] [SymmetricCategory V] in
private theorem projection_step (s : Scope β γ) {A B D : V}
    (k : J.obj (E ⊗ B) ⟶ J.obj D) :
    J.map ((fst G A ≫ s.projection M) ▷ B) ≫ k =
      J.map ((s.projection M ▷ A) ▷ B) ≫ J.map (fst E A ▷ B) ≫ k := by
  rw [← J.map_comp_assoc, ← MonoidalCategory.comp_whiskerRight,
    CartesianMonoidalCategory.whiskerRight_fst]

private theorem block_compile (p : Table Φ β L n) {A : τ} (b : Block Φ β p.types L A)
    (s : Scope β γ) (next : LocalContinuations β p.types L Φ b.locals) (ih : Continues J M p next) :
    denoteRegion J M (b.compile s next).toSSA_hasType =
      J.map (s.projection M ▷ M.obj A) ≫ b.continued J M p := by
  cases b with
  | jump a t =>
    let body := t.compile (fun _ h => h) (.skip s A) next
    change denoteRegion J M (FiniteExit.join (.br (s.operand a)) body).toSSA_hasType = _
    rw [join_operand J M _ body (s.operand_denotes J M a), target_compile J M p t _ _ next ih]
    simp only [Scope.projection, projection_step J M s]
    rw [bind_pre_map J, Block.continued, bind_retainEnvironment J]
  | @case B D a l r =>
    let left := l.compile (fun _ h => List.mem_append_left _ h) (.skip s A) next
    let right := r.compile (fun _ h => List.mem_append_right _ h) (.skip s A) next
    have den := RegionDenotes.case (s.operand_denotes J M a)
      (denoteRegion_spec J M left.toSSA_hasType) (denoteRegion_spec J M right.toSSA_hasType)
    change denoteRegion J M (FiniteExit.case (s.operand a) left right).toSSA_hasType = _
    rw [← den.eq_denote, target_compile J M p l _ _ next ih, target_compile J M p r _ _ next ih]
    simp only [Scope.projection, projection_step J M s, Category.assoc, case_pre_map, Block.continued]

theorem compileAt_denote_proof (p : Table Φ β L n) (ok : p.check = true) (i : Fin (n + 1))
    {m' : Nat} {γ' : BoundCtx τ m'} (s : Scope β γ') :
    denoteRegion J M (p.compileAt ok i s).toSSA_hasType =
      J.map (s.projection M ▷ M.obj (p.types i)) ≫ p.resultAt J M i := by
  rw [Table.compileAt, resultAt_step_proof J M p i]
  apply block_compile J M
  intro j edge _ _ t
  exact compileAt_denote_proof p ok j t
termination_by p.rank i
decreasing_by exact p.decreases ok edge

theorem toFiniteExit_denote_proof (p : Table Φ β L n) (ok : p.check = true) (i : Fin (n + 1))
    (a : Operand Φ β (p.types i)) :
    denoteRegion J M (p.toFiniteExit ok i a).toSSA_hasType = denoteRegion J M (p.toSSA_hasType i a) := by
  rw [Table.toFiniteExit, join_operand J M _ _ (denote_spec J M _),
    compileAt_denote_proof J M p ok i .base, toSSA_denote_proof J M p i a]
  simp [Scope.projection, denoteOperand]

theorem toLetCase_denote_proof (p : Table Φ β L n) (ok : p.check = true) (i : Fin (n + 1))
    (a : Operand Φ β (p.types i)) :
    denoteRegion J M (p.toSSA_hasType i a) =
      J.map (contextMap M β) ≫ LetCase.Semantics.Categorical.denote J M (p.toLetCase ok i a).2 ≫
        J.map (labelInject M (L := [Region.packedExitType L]) 0 rfl ≫ unpackLabelExit M L) := by
  let c := p.toFiniteExit ok i a
  rw [← toFiniteExit_denote_proof J M p ok i a, ← FiniteExit.denote_decode_encode J M c,
    FiniteExit.denote_decode, Code.denote_toSSA J M c.encode (L := [_]) (exit := 0) rfl]
  simp only [Table.toLetCase, Category.assoc, ← J.map_comp, c]

theorem toLetCase?_denote_proof (p : Table Φ β L n) (i : Fin (n + 1))
    (a : Operand Φ β (p.types i)) {term : Operand Φ β (Region.packedExitType L)}
    (compiled : p.toLetCase? i a = some term) :
    denoteRegion J M (p.toSSA_hasType i a) =
      J.map (contextMap M β) ≫ LetCase.Semantics.Categorical.denote J M term.2 ≫
        J.map (labelInject M (L := [Region.packedExitType L]) 0 rfl ≫ unpackLabelExit M L) := by
  unfold Table.toLetCase? at compiled
  split at compiled
  · rename_i ok
    obtain rfl := Option.some.inj compiled
    exact toLetCase_denote_proof J M p ok i a
  · contradiction

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture
