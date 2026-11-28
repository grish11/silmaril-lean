module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Roundtrip.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Generators.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.FiniteExit.Thms

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture

open Region (HasType ValueBranches)
open Region.Paper
open Region (cfgEntryContinuations)
open Silmaril.DeBruijn (lift)
open Morphism.CaseSSA (erase erase_hasType erase_rename up_ren_related)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {d m n : Nat} {β : BoundCtx τ d} {γ : BoundCtx τ m} {L : LCtx τ}

omit [TypeFormers τ] in
private theorem scope_ren : {m : Nat} → {γ : BoundCtx τ m} → (s : Scope β γ) →
    Ren β.toList γ.toList s.indices
  | _, _, .base => Ren.id _
  | _, _, .skip s A => (scope_ren s).comp (Ren.wk _ A)

omit [TypeFormers τ] in
private theorem scope_related (s : Scope β γ) (i : Fin d) :
    (s.renaming.toFun i).val = s.indices i.val := by
  induction s with
  | base => rfl
  | skip s A ih => exact congrArg Nat.succ ih

private theorem operand_erase (s : Scope β γ) {A B : τ} (a : Operand Φ (β.snoc A) B) :
    erase (s.operand a).1 = (erase a.1).rename (lift s.indices) :=
  erase_rename (s.renaming.up A).toFun _ (up_ren_related (scope_related s)) a.1

private def rows (p : Table Φ β L n) (s : Scope β γ) : Fin (n + 1) → Region Φ :=
  fun j => (p.block j).toSSA.renameVars (lift s.indices)

private theorem rows_typed (p : Table Φ β L n) (s : Scope β γ) (j : Fin (n + 1)) :
    HasType (p.types j :: γ.toList) (rows p s j) (List.ofFn p.types ++ L) :=
  (p.block j).toSSA_hasType.renameVars ((scope_ren s).lift (p.types j))

private theorem rows_skip (p : Table Φ β L n) (s : Scope β γ) (A : τ) :
    (fun j => (rows p s j).renameVars (lift Nat.succ)) = rows p (.skip s A) := by
  funext j
  rw [rows, Region.renameVars_comp]
  congr 1
  funext i
  cases i <;> rfl

private theorem rows_base (p : Table Φ β L n) :
    rows p (.base : Scope β β) = fun j => (p.block j).toSSA := by
  funext j
  unfold rows
  rw [show lift (Scope.base : Scope β β).indices = id by funext i; cases i <;> rfl, Region.renameVars_id]

private theorem drop_fresh (r : Region Φ) :
    (r.renameVars (lift Nat.succ)).substVars (Tm.singleSubst (.var 0)) = r := by
  rw [Region.substVars_renameVars]
  have h : Tm.singleSubst (.var 0 : Tm Φ) ∘ lift Nat.succ = Tm.var := by funext i; cases i <;> rfl
  rw [h, Region.substVars_var]

private theorem head_local {k : Nat} {Γ : VCtx τ} (R : Fin (k + 1) → τ) {blocks : Fin (k + 1) → Region Φ}
    (hb : ∀ j, HasType (R j :: Γ) (blocks j) (List.ofFn R ++ L)) (i : Fin (k + 1)) :
    Region.Paper.Eqv (R i :: Γ) (cfgEntryContinuations blocks i)
      (.cfg (blocks i) (k + 1) (fun j => (blocks j).renameVars (lift Nat.succ))) L := by
  let shifted := fun j => (blocks j).renameVars (lift Nat.succ)
  have ht (j : Fin (k + 1)) := (hb j).renameVars ((Ren.wk Γ (R i)).lift (R j))
  have step : Region.SubstitutionEquiv (R i :: Γ) (cfgEntryContinuations blocks i)
      (.cfg (.let₁ (.var 0) (shifted i)) (k + 1) shifted) L :=
    .base (.entry (.cfgBrLocal R i (.var (i := 0) rfl) ht))
  have beta := Region.SubstitutionEquiv.letValue (.var (i := 0) (rfl : At (R i :: Γ) 0 (R i))) (ht i)
  rw [drop_fresh] at beta
  exact .cfgEta (.native (step.trans (.cfg R beta (fun j => .base (.refl (ht j))))))

private theorem entry_operand {k : Nat} {Γ : VCtx τ} (R : Fin k → τ) {blocks : Fin k → Region Φ}
    {i : Nat} {A : τ} {a : Tm Φ} (out : At (List.ofFn R ++ L) i A) (ha : Tm.HasType Γ a A)
    (hb : ∀ j, HasType (R j :: Γ) (blocks j) (List.ofFn R ++ L)) :
    WithBoundEntryEta.Eqv Γ (.cfg (.br i a) k blocks) (.let₁ a (cfgEntryContinuations blocks i)) L := by
  have step := WithBoundEntryEta.reentry R (.br out ha) hb
  rw [Region.lsubst_bindBranchArguments_br] at step
  exact step

private theorem target_replay (p : Table Φ β L n) {A : τ} (t : Target p.types L A)
    {targets : List (Fin (n+1))} (edge : ∀ j ∈ t.locals, j ∈ targets) (s : Scope β γ)
    (next : LocalContinuations β p.types L Φ targets)
    (ih : ∀ j (h : j ∈ targets) {m : Nat} {γ : BoundCtx τ m} (s : Scope β γ),
      WithBoundEntryEta.Eqv (γ.snoc (p.types j)).toList (cfgEntryContinuations (rows p s) j)
        (next j h s).toSSA L) :
    WithBoundEntryEta.Eqv (γ.snoc A).toList (cfgEntryContinuations (rows p s) t.index)
      (t.compile edge s next).toSSA L := by
  cases t with
  | «local» j => exact ih j (edge j (by simp [Target.locals])) s
  | exit h =>
    exact .paper (.cfgEta (.native (.base (.entry (.cfgBrExit p.types h (.var (i := 0) rfl)
      (fun j => (rows_typed p s j).renameVars ((Ren.wk γ.toList A).lift (p.types j))))))))

private theorem join_operand {A : τ} (a : Operand Φ γ A) (b : FiniteExit Φ L (γ.snoc A)) :
    WithBoundEntryEta.Eqv γ.toList (FiniteExit.join (.br a) b).toSSA (.let₁ (erase a.1) b.toSSA) L := by
  let R : Fin 1 → τ := fun _ => A
  let block := b.toSSA.renameLabels Nat.succ
  have hb (j : Fin 1) : HasType (R j :: γ.toList) block (List.ofFn R ++ L) := by
    simpa [R, List.ofFn_succ, block, BoundCtx.toList] using b.toSSA_hasType.renameLabels (Ren.wk L A)
  have out : At (List.ofFn R ++ L) 0 A := rfl
  have ha := erase_hasType a.2.toHasType
  have enter := entry_operand R out ha hb
  have next := head_local R hb 0
  have drop : Region.SubstitutionEquiv (A :: γ.toList)
      (.cfg block 1 (fun _ => block.renameVars (lift Nat.succ))) b.toSSA L := by
    simpa only [Nat.zero_add, Nat.one_add, block, BoundCtx.toList] using
      (Region.SubstitutionEquiv.cfgOutward R b.toSSA_hasType
        (fun j => (hb j).renameVars ((Ren.wk γ.toList A).lift A)))
  simpa only [FiniteExit.toSSA, Code.toSSA, Region.linkExits, List.length_cons, List.length_nil, Nat.zero_add, Nat.one_add, block]
    using enter.trans (.let₁ ha (.paper (next.trans (.cfgEta (.native drop)))))

private theorem block_replay (p : Table Φ β L n) {A : τ} (b : Block Φ β p.types L A)
    (s : Scope β γ) (next : LocalContinuations β p.types L Φ b.locals)
    (ih : ∀ j (h : j ∈ b.locals) {m : Nat} {γ : BoundCtx τ m} (s : Scope β γ),
      WithBoundEntryEta.Eqv (γ.snoc (p.types j)).toList (cfgEntryContinuations (rows p s) j)
        (next j h s).toSSA L) :
    WithBoundEntryEta.Eqv (γ.snoc A).toList
      (.cfg (b.toSSA.renameVars (lift s.indices)) (n + 1) (rows p (.skip s A)))
      (b.compile s next).toSSA L := by
  cases b with
  | jump a t =>
    let body := t.compile (fun _ h => h) (.skip s A) next
    have ha := erase_hasType (s.operand a).2.toHasType
    have enter := entry_operand p.types t.typing ha (rows_typed p (.skip s A))
    have move := target_replay p t (fun _ h => h) (.skip s A) next ih
    exact (by simpa only [Block.toSSA, Region.renameVars, operand_erase] using enter :
      WithBoundEntryEta.Eqv _ _ _ _).trans ((Extension.Eqv.let₁ ha move).trans (join_operand (s.operand a) body).symm)
  | @case B D a l r =>
    have ha := erase_hasType (s.operand a).2.toHasType
    have enter := WithBoundEntryEta.Generators.caseEntry p.types ha
      (.br l.typing (.var (i := 0) rfl)) (.br r.typing (.var (i := 0) rfl)) (rows_typed p (.skip s A))
    have left := target_replay p l (fun _ h => List.mem_append_left _ h) (.skip s A) next ih
    have right := target_replay p r (fun _ h => List.mem_append_right _ h) (.skip s A) next ih
    have step := enter.trans (.case ha left right)
    simpa only [Block.toSSA, Block.compile, FiniteExit.toSSA, Region.renameVars, operand_erase, Tm.rename, lift] using step

private theorem compileAt_replay_proof (p : Table Φ β L n) (ok : p.check = true)
    (i : Fin (n + 1)) {m : Nat} {γ : BoundCtx τ m} (s : Scope β γ) :
    WithBoundEntryEta.Eqv (γ.snoc (p.types i)).toList (cfgEntryContinuations (rows p s) i)
      (p.compileAt ok i s).toSSA L := by
  rw [Table.compileAt]
  have enter := head_local p.types (rows_typed p s) i
  rw [rows_skip p s (p.types i)] at enter
  apply (Region.Paper.Extension.Eqv.paper enter).trans
  apply block_replay p (p.block i) s
  intro j edge _ _ t
  exact compileAt_replay_proof p ok j t
termination_by p.rank i
decreasing_by exact p.decreases ok edge

theorem toFiniteExit_replay_proof (p : Table Φ β L n) (ok : p.check = true)
    (i : Fin (n + 1)) (a : Operand Φ β (p.types i)) :
    WithBoundEntryEta.Eqv β.toList (p.toSSA i a) (p.toFiniteExit ok i a).toSSA L := by
  have enter := entry_operand p.types (Target.local (L := L) i).typing
    (erase_hasType a.2.toHasType) (fun j => (p.block j).toSSA_hasType)
  have body := compileAt_replay_proof p ok i (.base : Scope β β)
  rw [rows_base] at body
  exact enter.trans ((Extension.Eqv.let₁ (erase_hasType a.2.toHasType) body).trans (join_operand a (p.compileAt ok i .base)).symm)

private theorem bind_branches {Γ : VCtx τ} {r : Region Φ} (h : HasType Γ r L) :
    WithBoundEntryEta.Eqv Γ r r.bindBranchArguments L := by
  induction h with
  | br hi ha => exact WithBoundEntryEta.bindBranch hi ha
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ ihl ihr => exact .case ha ihl ihr
  | cfg R _ _ ihe ihb => exact .cfg R ihe ihb

theorem native_roundTrip_proof (p : Table Φ β L n) (ok : p.check = true)
    (i : Fin (n + 1)) (a : Operand Φ β (p.types i)) :
    WithBoundEntryEta.Eqv β.toList (p.toSSA i a) (Reverse.tableGrammar p ok i a).toTable.toSSA L := by
  let g := Reverse.tableGrammar p ok i a
  have rebuilt := toFiniteExit_replay_proof g.toTable.table g.toTable.checked 0 g.toTable.entry
  change WithBoundEntryEta.Eqv β.toList g.toTable.toSSA
    ((Reverse.tableProgram p ok i a).toTable.toFiniteExit
      (Reverse.tableProgram p ok i a).toTable_checked 0 (Reverse.tableProgram p ok i a).entry).toSSA L at rebuilt
  rw [Reverse.Program.toTable_render, Reverse.tableProgram_render] at rebuilt
  exact (toFiniteExit_replay_proof p ok i a).trans rebuilt.symm

theorem bind_pack_eq_proof {Γ : VCtx τ} {r q : Region Φ}
    (h : WithBoundEntryEta.Eqv Γ r q L) :
    WithBoundEntryEta.Eqv Γ r.bindBranchArguments.packExits q.bindBranchArguments.packExits
      [Region.packedExitType L] := by
  have guarded := (bind_branches h.typed.1).symm.trans (h.trans (bind_branches h.typed.2))
  exact guarded.lsubstPost h.typed.1.bindBranchArguments h.typed.2.bindBranchArguments
    (fun _ _ hit => (Region.packExits_valueFamily Γ L hit).hasType)

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture
