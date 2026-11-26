module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Categorical.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Categorical.Realization.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.FiniteExit.Categorical.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Categorical.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Labels.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional

open CategoryTheory CategoryTheory.Limits PremonoidalCategory
open CategoryTheory.CartesianMonoidalCategory (snd)
open scoped MonoidalCategory
open Silmaril.SSA.RVSDG.LambdaSSA
open LinearChain (Site localSite)
open LinearChain.Categorical (siteArrow decodeLabels decode_local cfgStepOf cfgStepOf_at
  call choice case_project call_denotes payload_cfg_denotes)
open LambdaSSA.Semantics.Categorical
open LetIter.Semantics.Categorical (TypeModel InstructionModel)
open LetIter.ProofRelevant.Semantics.Categorical
  (caseWithContext duplicate extend splitMapCoprod)
local notation "bindArrow" => LetIter.ProofRelevant.Semantics.Categorical.bind
open Morphism.CaseSSA (erase_hasType)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w h k

variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
  {V : Type v} {C : Type w} [Category.{h} V] [Category.{k} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]
  {n : Nat} {L : LCtx τ}

omit [TypeFormers τ] in
private theorem site_eq {K : LCtx τ} {A : τ} {s t : Site K A} (e : s.index = t.index) : s = t := by
  cases s
  cases t
  cases e
  rfl

omit [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J] [InstructionModel J M Φ] in
private theorem route_exit [DistributiveFreydCategory J] (p : Table Φ L n)
    {A : τ} {j : Nat} (ht : At L j A) (hj : At (List.ofFn p.types ++ L) (n + j) A) :
    J.map (siteArrow M ⟨n + j, hj⟩) ≫ decodeLabels J M p.types L =
      J.map (labelInject M j ht) ≫ coprod.inl := by
  unfold siteArrow decodeLabels
  rw [← J.map_comp_assoc, labelAppendSplit_exit M p.types L ht hj, J.map_comp, Category.assoc]
  congr 1
  exact map_inl_inv_coprodComparison J

private theorem destination_result (p : Table Φ L n)
    {A : τ} (s : Site (List.ofFn p.types ++ L) A) :
    (p.destination s).result J M =
      J.map (siteArrow M s) ≫ decodeLabels J M p.types L ≫
        coprod.desc (𝟙 _) (iterate (p.step J M)) := by
  have hi := p.destination_index s
  generalize p.destination s = target at hi ⊢
  cases target with
  | «local» i ty =>
    cases ty
    have eq : s = localSite p.types L i := site_eq hi.symm
    rw [eq, ← Category.assoc, decode_local J M, Category.assoc, coprod.inr_desc]
    rfl
  | exit j ty =>
    change n + j = s.index at hi
    have hs : At (List.ofFn p.types ++ L) (n + j) A := hi.symm ▸ s.typing
    have eq : s = ⟨n + j, hs⟩ := site_eq hi.symm
    rw [eq, ← Category.assoc, route_exit J M p ty hs, Category.assoc, coprod.inl_desc, Category.comp_id]
    rfl

theorem resultAt_step_proof (p : Table Φ L n) (i : Fin n) :
    p.resultAt J M i =
      Acyclic.Categorical.blockArrow J M (fun _ s => (p.destination s).result J M) (p.block i) := by
  dsimp only [Table.resultAt]
  rw [ElgotCategory.fixpoint (p.step J M), ← Category.assoc]
  change (J.map _ ≫ cfgStepOf J M p.types L (p.blockArrows J M)) ≫ _ = _
  rw [cfgStepOf_at, Category.assoc, Table.blockArrows, Acyclic.Categorical.blockArrow_post]
  congr 1
  funext A s
  exact (destination_result J M p s).symm

variable [FreydCategory.CentralUnit J] [RegionTypingCoherent (Φ := Φ) J M]

omit [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]
  [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M] [TypeFormers τ] in
private theorem bind_payload [DistributiveFreydCategory J] [FreydCategory.CentralUnit J] {E A T : V}
    (f : J.obj E ⟶ J.obj A) (g : J.obj A ⟶ J.obj T) :
    bindArrow J f (J.map (snd E A) ≫ g) = f ≫ g := by
  have drop : extend J f ≫ J.map (snd E A) = f := by
    simp only [extend, PremonoidalCategory.leftTensor, PremonoidalCategory.id_whiskerRight,
      Category.id_comp, Category.assoc]
    rw [FreydCategory.whiskerLeft_snd J, ← J.map_comp_assoc]
    simp [duplicate]
  change extend J f ≫ (J.map (snd E A) ≫ g) = _
  rw [← Category.assoc, drop]

private theorem join_payload {d : Nat} {β : BoundCtx τ d} {A : τ}
    (a : Operand Φ β A) (b : FiniteExit Φ L (β.snoc A))
    {f : J.obj (ctxObj M β.toList) ⟶ J.obj (M.obj A)}
    (da : Denotes J M (erase_hasType a.2.toHasType) f)
    (g : J.obj (M.obj A) ⟶ J.obj (labelObj M L))
    (body : denoteRegion J M b.toSSA_hasType = J.map (snd (ctxObj M β.toList) (M.obj A)) ≫ g) :
    denoteRegion J M (FiniteExit.join (.br a) b).toSSA_hasType = f ≫ g := by
  let ha := (Code.br a).toSSA_hasType (L := [A]) (exit := 0) rfl
  rw [FiniteExit.denote_linkSingleton J M ha b.toSSA_hasType _, body]
  rw [← (RegionDenotes.br (h := (rfl : At [A] 0 A)) da).eq_denote J M,
    ← J.map_comp_assoc, CartesianMonoidalCategory.whiskerLeft_snd,
    J.map_comp, Category.assoc, bind_payload, Category.assoc, ← J.map_comp_assoc,
    SingletonDispatcher.labelInject_payload, J.map_id, Category.id_comp]

omit [FreydCategory.CentralUnit J] [RegionTypingCoherent (Φ := Φ) J M] in
private theorem operand_denotes {d : Nat} {β : BoundCtx τ d} {A B : τ}
    (op : TwoBlock.Instruction Φ A B) :
    Denotes J M (erase_hasType (operand (β := β) op).2.toHasType)
      (J.map (snd (ctxObj M β.toList) (M.obj A)) ≫ call J M op) := by
  obtain ⟨op, rfl, rfl⟩ := op
  exact call_denotes J M ⟨op, rfl, rfl⟩

private abbrev LocalContinuationsCorrect (p : Table Φ L n) (targets : List Nat)
    (next : LocalContinuations p targets) : Prop :=
  ∀ j (edge : j.val ∈ targets) {d : Nat} (β : BoundCtx τ d),
    denoteRegion J M (next j edge β).toSSA_hasType =
      J.map (snd (ctxObj M β.toList) (M.obj (p.types j))) ≫ p.resultAt J M j

omit [FreydCategory.CentralUnit J] in
private theorem compileDestination_denote (p : Table Φ L n) {A : τ} {targets : List Nat}
    (t : Destination p A) (edge : t.index ∈ targets) {d : Nat} (β : BoundCtx τ d)
    (next : LocalContinuations p targets) (ih : LocalContinuationsCorrect J M p targets next) :
    denoteRegion J M (p.compileDestination t edge β next).toSSA_hasType =
      J.map (snd (ctxObj M β.toList) (M.obj A)) ≫ t.result J M := by
  cases t with
  | «local» j ty =>
    cases ty
    exact ih j edge β
  | exit j ty =>
    exact (RegionDenotes.br (h := ty) (Denotes.var (J := J) (M := M) (i := 0) rfl)).eq_denote.symm

private theorem compileBlock_denote (p : Table Φ L n) (i : Fin n)
    (b : Acyclic.Block Φ (List.ofFn p.types ++ L) (p.types i)) {d : Nat} (β : BoundCtx τ d)
    (next : LocalContinuations p b.targets) (ih : LocalContinuationsCorrect J M p b.targets next) :
    denoteRegion J M (p.compileBlock i b β next).toSSA_hasType =
      J.map (snd (ctxObj M β.toList) (M.obj (p.types i))) ≫
        Acyclic.Categorical.blockArrow J M (fun _ s => (p.destination s).result J M) b := by
  cases b with
  | jump op s =>
    simp only [Table.compileBlock, Acyclic.Categorical.blockArrow]
    rw [← Category.assoc]
    exact join_payload J M _ _ (operand_denotes J M op) _
      (compileDestination_denote J M p _ _ _ next ih)
  | branch op l r =>
    have hl : l.index ∈ (Acyclic.Block.branch op l r).targets := by simp [Acyclic.Block.targets]
    have hr : r.index ∈ (Acyclic.Block.branch op l r).targets := by simp [Acyclic.Block.targets]
    let γ := β.snoc (p.types i)
    let left := p.compileTarget l hl γ next
    let right := p.compileTarget r hr γ next
    have dl := compileDestination_denote J M p (p.destination l)
      ((p.destination_index l).symm ▸ hl) γ next ih
    have dr := compileDestination_denote J M p (p.destination r)
      ((p.destination_index r).symm ▸ hr) γ next ih
    change denoteRegion J M left.toSSA_hasType = _ at dl
    change denoteRegion J M right.toSSA_hasType = _ at dr
    have den := RegionDenotes.case (operand_denotes J M (β := β) op)
      (denoteRegion_spec J M left.toSSA_hasType) (denoteRegion_spec J M right.toSSA_hasType)
    rw [dl, dr, case_project] at den
    simpa only [Table.compileBlock, Acyclic.Categorical.blockArrow, choice, Category.assoc] using
      den.eq_denote.symm

theorem compileRankedAt_denote_proof (p : Table Φ L n) (ranking : Ranking p) (i : Fin n)
    {d : Nat} (β : BoundCtx τ d) :
    denoteRegion J M (p.compileRankedAt ranking i β).toSSA_hasType =
      J.map (snd (ctxObj M β.toList) (M.obj (p.types i))) ≫ p.resultAt J M i := by
  rw [Table.compileRankedAt, resultAt_step_proof J M p i]
  apply compileBlock_denote J M
  intro j edge _ γ
  exact compileRankedAt_denote_proof p ranking j γ
termination_by ranking.rank i
decreasing_by exact ranking.decreases i j ((p.mem_localTargets i j).mpr edge)

theorem toSSA_denote_proof (p : Table Φ L n) {d : Nat} {β : BoundCtx τ d}
    (i : Fin n) (a : Operand Φ β (p.types i)) :
    denoteRegion J M (p.toSSA_hasType i a) =
      denote J M (erase_hasType a.2.toHasType) ≫ p.resultAt J M i := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    let da := denote_spec J M (erase_hasType a.2.toHasType)
    have native := payload_cfg_denotes J M p.types i
      (.br (localSite p.types L i).typing (erase_hasType a.2.toHasType))
      (fun j => (p.block j).typing β.toList) _ (RegionDenotes.br da)
      (p.blockArrows J M) (fun j => Acyclic.Categorical.block_denotes J M (p.block j) β.toList)
    exact native.eq_denote.symm

theorem toFiniteExitRanked_denote_proof (p : Table Φ L n) (ranking : Ranking p)
    {d : Nat} {β : BoundCtx τ d} (i : Fin n) (a : Operand Φ β (p.types i)) :
    denoteRegion J M (p.toFiniteExitRanked ranking i a).toSSA_hasType =
      denoteRegion J M (p.toSSA_hasType i a) := by
  rw [toSSA_denote_proof J M]
  exact join_payload J M a (p.compileRankedAt ranking i β) (denote_spec J M _) _
    (compileRankedAt_denote_proof J M p ranking i β)

theorem toLetCaseRanked_denote_proof (p : Table Φ L n) (ranking : Ranking p)
    {d : Nat} {β : BoundCtx τ d} (i : Fin n) (a : Operand Φ β (p.types i)) :
    denoteRegion J M (p.toSSA_hasType i a) =
      J.map (contextMap M β) ≫ LetCase.Semantics.Categorical.denote J M (p.toLetCaseRanked ranking i a).2 ≫
        J.map (labelInject M (L := [Region.packedExitType L]) 0 rfl ≫ unpackLabelExit M L) := by
  let c := p.toFiniteExitRanked ranking i a
  rw [← toFiniteExitRanked_denote_proof J M p ranking i a, ← FiniteExit.denote_decode_encode J M c,
    FiniteExit.denote_decode, Code.denote_toSSA J M c.encode (L := [_]) (exit := 0) rfl]
  simp only [Table.toLetCaseRanked, Category.assoc, ← J.map_comp, c]

theorem toLetCase?_denote_proof (p : Table Φ L n) {d : Nat} {β : BoundCtx τ d}
    (i : Fin n) (a : Operand Φ β (p.types i)) {term : Operand Φ β (Region.packedExitType L)}
    (compiled : p.toLetCase? i a = some term) :
    denoteRegion J M (p.toSSA_hasType i a) =
      J.map (contextMap M β) ≫ LetCase.Semantics.Categorical.denote J M term.2 ≫
        J.map (labelInject M (L := [Region.packedExitType L]) 0 rfl ≫ unpackLabelExit M L) := by
  unfold Table.toLetCase? at compiled
  split at compiled
  · rename_i ok
    obtain rfl := Option.some.inj compiled
    exact toLetCaseRanked_denote_proof J M p (p.acyclicRanking ok) i a
  · contradiction

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional
