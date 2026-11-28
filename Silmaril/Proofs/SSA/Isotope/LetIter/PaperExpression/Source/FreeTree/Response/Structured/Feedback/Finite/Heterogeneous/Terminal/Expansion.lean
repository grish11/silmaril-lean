module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Terminal.Expansion.Transfer.Defs
public import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Terminal.Normalize
import Silmaril.SSA.Isotope.LetIter.AbortSequence.Normalization.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Equations.Thms

@[expose] public section

open Silmaril.Isotope Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.PaperExpression

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.TerminalProofs

private theorem decode_encode (S : Code) (p : S.Value → Code) (v : S.Value) (x : (p v).Value) :
    Code.decode S p (Code.encode S p v x) = ⟨v, x⟩ := by
  induction S with
  | unit => cases v; rfl
  | sum l r il ir =>
    cases v with
    | inl v =>
      simp only [Code.encode, Code.decode]
      rw [il (fun v => p (.inl v)) v x]
    | inr v =>
      simp only [Code.encode, Code.decode]
      rw [ir (fun v => p (.inr v)) v x]

variable {n : Nat} {F : Family n} {S T B : Code}

local notation "Ops" => Opcode F
local notation "Free" => (Ctx.nil : Ctx Empty (Ty Unit))
local notation "H" => HasType Ops Free

def nativePlan (p : Plan F S B) (m : Nat) : Tm Empty Ops m :=
  match p with
  | .one r => nativeRow r m
  | .two f x k =>
    .let₁ (.op f (nativeValue Ops f.argCode x)) (dispatch f.replyCode (fun m r => nativeRow (k r) m) (.bv 0))

theorem plan_lowers (p : Plan F S B) (m : Nat) :
    p.source.toLetIter m = some (nativePlan p m) := by
  cases p with
  | one r => exact row_lowers r m
  | two f x k =>
    simp only [Plan.source, nativePlan, Expr.toLetIter, value_lowers]
    rw [dispatch_lowers f.replyCode (fun m r => row_lowers (k r) m) (a := .var 0) (arg := .bv 0) rfl]
    rfl

theorem plan_typed (p : Plan F S B) {m : Nat} (β : BoundCtx (Ty Unit) m) :
    H β (nativePlan p m) (Code.sum B S).ty := by
  cases p with
  | one r => exact row_typed r β
  | two f x k => exact .let₁ (.op (value_typed f.argCode x β)) (dispatch_typed f.replyCode
      (fun β r => row_typed (k r) β) .bv)

theorem plan_subst (p : Plan F S B) {j m : Nat} (σ : Fin j → Tm Empty Ops m) :
    (nativePlan p j).bsubst σ = nativePlan p m := by
  cases p with
  | one r => exact row_subst r σ
  | two f x k =>
    simp only [nativePlan, Tm.bsubst, value_bsubst, dispatch_subst f.replyCode (fun σ r => row_subst (k r) σ)]
    rfl

private def nativeTransferPlan (p : TransferPlan F S B) (m : Nat) : Tm Empty Ops m :=
  match p with
  | .ordinary plan => nativePlan plan m
  | .transfer target => nativeValue Ops (Code.sum B S) (.inr target)

private theorem transferPlan_lowers (p : TransferPlan F S B) (m : Nat) :
    p.source.toLetIter m = some (nativeTransferPlan p m) := by
  cases p with
  | ordinary p => exact plan_lowers p m
  | transfer target => exact value_lowers (.sum B S) (.inr target) m

private theorem transferPlan_typed (p : TransferPlan F S B) {m : Nat} (β : BoundCtx (Ty Unit) m) :
    H β (nativeTransferPlan p m) (Code.sum B S).ty := by
  cases p with
  | ordinary p => exact plan_typed p β
  | transfer target => exact value_typed (.sum B S) (.inr target) β

private theorem transferPlan_subst (p : TransferPlan F S B) {j m : Nat} (σ : Fin j → Tm Empty Ops m) :
    (nativeTransferPlan p j).bsubst σ = nativeTransferPlan p m := by
  cases p with
  | ordinary p => exact plan_subst p σ
  | transfer target => exact value_bsubst σ (.sum B S) (.inr target)

private def nativePlans (M : TransferPlans F S B) : Tm Empty Ops 1 :=
  dispatch S (fun m s => nativeTransferPlan (M s) m) (.bv 0)

private theorem plans_lowers (M : TransferPlans F S B) : M.source.toLetIter 1 = some (nativePlans M) :=
  dispatch_lowers S (fun m s => transferPlan_lowers (M s) m) (a := .var 0) (arg := .bv 0) rfl

private theorem plans_typed (M : TransferPlans F S B) :
    H (.snoc .nil S.ty) (nativePlans M) (Code.sum B S).ty :=
  dispatch_typed S (fun β s => transferPlan_typed (M s) β) .bv

private def rowPlan : TransferRow F S B → TransferPlan F S B
  | .ordinary row => .ordinary (.one row)
  | .transfer target => .transfer target

private theorem expanded_lowers (M : TransferTable F S B) :
    M.source.toLetIter 1 = some (nativePlans (fun s => rowPlan (M s))) :=
  dispatch_lowers S (src := fun s => (M s).source) (rows := fun m s => nativeTransferPlan (rowPlan (M s)) m) (fun m s => by
    cases M s with
    | ordinary row => exact row_lowers row m
    | transfer target => exact value_lowers (.sum B S) (.inr target) m) (a := .var 0) (arg := .bv 0) rfl

variable {ε : Type} [HasEff (Opcode F) ε] {pe : ε}

local notation "E" => AbortEquiv (Φ := Ops) pe Free

private theorem plans_beta (M : TransferPlans F S B) (s : S.Value) :
    E .nil (plug (nativePlans M) (nativeValue Ops S s)) (nativeTransferPlan (M s) 0) (Code.sum B S).ty := by
  rw [plug, nativePlans, dispatch_subst S (fun σ s => transferPlan_subst (M s) σ)]
  exact dispatch_beta S (fun β s => transferPlan_typed (M s) β)
    (fun σ s => transferPlan_subst (M s) σ) .nil s

private def embedControl (Φ : Type) : Tm Empty Φ 1 :=
  .case (.bv 0) (.inl (.bv 0)) (.inr (.inl (.bv 0)))

omit [HasEff (Opcode F) ε] in
private theorem embed_typed : H (.snoc .nil (Code.sum B S).ty)
    (embedControl Ops) (Code.sum B (Code.sum S T)).ty :=
  .case .bv (.inl .bv) (.inr (.inl .bv))

private theorem embed_value (v : (Code.sum B S).Value) :
    E .nil (plug (embedControl Ops) (nativeValue Ops (Code.sum B S) v))
      (nativeValue Ops (Code.sum B (Code.sum S T)) (Sum.map id Sum.inl v))
      (Code.sum B (Code.sum S T)).ty := by
  cases v with
  | inl b =>
    exact handler_left (l := .inl (.bv 0)) (r := .inr (.inl (.bv 0))) rfl (.inl .bv) (.inr (.inl .bv)) b
  | inr s =>
    exact handler_right (l := .inl (.bv 0)) (r := .inr (.inl (.bv 0))) rfl (.inl .bv) (.inr (.inl .bv)) s

private theorem embed_row (r : Row F S B) :
    E .nil (.let₁ (nativeRow r 0) (embedControl Ops))
      (nativeRow (r.map (T := Code.sum S T) Sum.inl) 0) (Code.sum B (Code.sum S T)).ty := by
  cases r with
  | ret b =>
    exact (bind_value embed_typed (.inl b)).trans (embed_value (.inl b))
  | call f x k =>
    exact bind_call (B := B) (C := B) (T := Code.sum S T) x k
      (fun r => Sum.map id Sum.inl (k r)) embed_typed (fun r => embed_value (T := T) (k r))

private def embedPlan (p : Plan F S B) (T : Code) : Plan F (Code.sum S T) B :=
  match p with
  | .one r => .one (r.map Sum.inl)
  | .two f x k => .two f x (fun r => (k r).map Sum.inl)

private theorem embed_plan (p : Plan F S B) :
    E .nil (.let₁ (nativePlan p 0) (embedControl Ops)) (nativePlan (embedPlan p T) 0)
      (Code.sum B (Code.sum S T)).ty := by
  cases p with
  | one r => exact embed_row r
  | two f x k =>
    exact bind_dispatch x (fun m r => nativeRow (k r) m) (fun m r => nativeRow ((k r).map (T := Code.sum S T) Sum.inl) m)
      (fun β r => row_typed (k r) β) (fun β r => row_typed ((k r).map (T := Code.sum S T) Sum.inl) β)
      (fun σ r => row_subst (k r) σ) (fun σ r => row_subst ((k r).map (T := Code.sum S T) Sum.inl) σ)
      embed_typed (fun r => embed_row (k r))

private def embedTransfer (p : TransferPlan F S B) (T : Code) : TransferPlan F (.sum S T) B :=
  match p with
  | .ordinary p => .ordinary (embedPlan p T)
  | .transfer target => .transfer (.inl target)

private theorem embed_transfer (p : TransferPlan F S B) :
    E .nil (.let₁ (nativeTransferPlan p 0) (embedControl Ops))
      (nativeTransferPlan (embedTransfer p T) 0) (Code.sum B (.sum S T)).ty := by
  cases p with
  | ordinary p => exact embed_plan p
  | transfer target =>
    exact (bind_value embed_typed (.inr target)).trans (embed_value (.inr target))

private def staged (M : TransferPlans F S B) : Table F M.stateCode (Code.sum B M.stateCode) := fun u =>
  match M.expand u with
  | .ordinary row => stageRow (fun v => u.isLeft && !v.isLeft) row
  | .transfer target => .ret (.inr target)

private theorem flatten_expanded (M : TransferPlans F S B) :
    E (.snoc .nil M.stateCode.ty) (.case (nativeBody (staged M)) (.bv 0) (.inr (.bv 0)))
      (nativePlans (fun u => rowPlan (M.expand u))) (Code.sum B M.stateCode).ty := by
  refine flatten_dispatch (staged M) _ (plans_typed _) (fun u => ?_)
  refine Refinement.trans ?_ (plans_beta (fun v => rowPlan (M.expand v)) u).symm
  cases h : M.expand u with
  | ordinary row =>
    rw [staged, h]
    exact flatten_stage_row row (fun v => u.isLeft && !v.isLeft)
  | transfer target =>
    rw [staged, h]
    exact flatten_stage_transfer target

private def asOuter (T : Code) (r : Row F S B) : Row F (Code.sum S T) (Code.sum B (Code.sum S T)) :=
  match r with
  | .ret b => .ret (.inl b)
  | .call f x k => .call f x (fun r => .inl (Sum.map id Sum.inl (k r)))

private theorem staged_outer (M : TransferPlans F S B) (u : M.stateCode.Value) (r : Row F S B)
    (atRow : M.expand u = .ordinary (r.map (T := M.stateCode) Sum.inl)) : staged M u = asOuter M.pending r := by
  cases r with
  | ret b => simp only [staged, stageRow, atRow, Row.map, asOuter]
  | call f x k =>
    simp only [staged, stageRow, atRow, Row.map, asOuter]
    apply congrArg (Row.call f x)
    funext v
    cases rv : k v with
    | inl b => rfl
    | inr t =>
      change stageReply (S := Code.sum S M.pending) (B := B)
        (fun v : (Code.sum S M.pending).Value =>
          (show (Code.sum S M.pending).Value from u).isLeft && !v.isLeft)
        (.inr (.inl t)) = .inl (.inr (.inl t))
      simp [stageReply, Sum.isLeft]

private theorem inner_outer (M : TransferPlans F S B) (u : M.stateCode.Value) (r : Row F S B)
    (atRow : M.expand u = .ordinary (r.map (T := M.stateCode) Sum.inl)) :
    E .nil (.iter (nativeValue Ops M.stateCode u) (nativeBody (staged M)))
      (nativeRow (r.map (T := M.stateCode) Sum.inl) 0) (Code.sum B M.stateCode).ty := by
  let body := body_typed (staged M)
  have first := body_beta (pe := pe) (staged M) u
  rw [staged_outer M u r atRow] at first
  let handle := loopHandler_typed body
  refine (unfold_closed body u).trans ((Refinement.let₁ first (.refl handle)).trans ?_)
  cases r with
  | ret b =>
    exact (bind_value handle (.inl (.inl b))).trans (loopHandler_left body (.inl b))
  | call f x k =>
    exact bind_call (S := M.stateCode) (T := M.stateCode) (B := Code.sum B M.stateCode) (C := B) x
      (fun v => .inl (Sum.map id Sum.inl (k v))) (fun v => Sum.map id Sum.inl (k v))
      handle (fun v => loopHandler_left body _)

private def pending (M : TransferPlans F S B) (s : S.Value) (v : (M s).replyCode.Value) : M.stateCode.Value :=
  .inr (Code.encode S (fun s => (M s).replyCode) s v)

private theorem pending_row (M : TransferPlans F S B) (s : S.Value) (v : (M s).replyCode.Value) :
    M.expand (pending M s v) = ((M s).second v).map (T := M.stateCode) Sum.inl := by
  simp only [pending, TransferPlans.expand]
  rw [decode_encode S (fun s => (M s).replyCode) s v]

private theorem second_of_two {p : TransferPlan F S B} {f : Ops} {x : f.argCode.Value}
    {k : f.replyCode.Value → Row F S B} (row : p = .ordinary (.two f x k)) (v : f.replyCode.Value) :
    p.second (row.symm ▸ v) = .ordinary (k v) := by subst p; rfl

private theorem first_of_one {p : TransferPlan F S B} (r : Row F S B) (eq : p = .ordinary (.one r))
    (encode : p.replyCode.Value → T.Value) : p.expandFirst T encode = .ordinary (r.map Sum.inl) := by
  subst p
  rfl

private theorem first_of_two {p : TransferPlan F S B} {f : Ops} {x : f.argCode.Value}
    {k : f.replyCode.Value → Row F S B} (eq : p = .ordinary (.two f x k))
    (encode : p.replyCode.Value → T.Value) :
    p.expandFirst T encode = .ordinary (.call f x (fun v => .inr (.inr (encode (eq.symm ▸ v))))) := by
  subst p
  rfl

private theorem first_of_transfer {p : TransferPlan F S B} (target : S.Value)
    (eq : p = .transfer target) (encode : p.replyCode.Value → T.Value) :
    p.expandFirst T encode = .transfer (.inl target) := by
  subst p
  rfl

private theorem inner_two (M : TransferPlans F S B) (s : S.Value) (f : Ops) (x : f.argCode.Value)
    (k : f.replyCode.Value → Row F S B) (row : M s = .ordinary (.two f x k)) :
    E .nil (.iter (nativeValue Ops M.stateCode (.inl s)) (nativeBody (staged M)))
      (nativePlan (S := M.stateCode) (.two f x (fun r => (k r).map (T := M.stateCode) Sum.inl)) 0) (Code.sum B M.stateCode).ty := by
  let next (v : f.replyCode.Value) : M.stateCode.Value := pending M s (row.symm ▸ v)
  have step : staged M (.inl s) = .call f x (fun v => .inr (next v)) := by
    have head : M.expand (.inl s) = .ordinary (.call f x (fun v => .inr (next v))) :=
      first_of_two row (Code.encode S (fun s => (M s).replyCode) s)
    unfold staged
    rw [head]
    rfl
  let body := body_typed (staged M)
  let handle := loopHandler_typed body
  have first := body_beta (pe := pe) (staged M) (.inl s)
  rw [step] at first
  refine (unfold_closed body (.inl s)).trans ((Refinement.let₁ first (.refl handle)).trans ?_)
  refine bind_dispatch x
    (fun _ v => nativeValue Ops (Code.sum (Code.sum B M.stateCode) M.stateCode) (.inr (next v)))
    (fun m v => nativeRow ((k v).map (T := M.stateCode) Sum.inl) m)
    (fun β v => value_typed (Code.sum (Code.sum B M.stateCode) M.stateCode) (.inr (next v)) β)
    (fun β v => row_typed ((k v).map (T := M.stateCode) Sum.inl) β)
    (fun σ v => value_bsubst σ (Code.sum (Code.sum B M.stateCode) M.stateCode) (.inr (next v)))
    (fun σ v => row_subst ((k v).map (T := M.stateCode) Sum.inl) σ) handle (fun v => ?_)
  have chosen : M.expand (next v) = .ordinary ((k v).map (T := M.stateCode) Sum.inl) := by
    rw [show next v = pending M s (row.symm ▸ v) from rfl, pending_row, second_of_two row v]
    rfl
  exact (bind_value handle (.inr (next v))).trans
    ((loopHandler_right body (next v)).trans (inner_outer M (next v) (k v) chosen))

private theorem inner_at (M : TransferPlans F S B) (s : S.Value) :
    E .nil (.iter (nativeValue Ops M.stateCode (.inl s)) (nativeBody (staged M)))
      (nativeTransferPlan (embedTransfer (M s) M.pending) 0) (Code.sum B M.stateCode).ty := by
  cases row : M s with
  | ordinary p =>
    cases p with
    | one r =>
      exact inner_outer M (.inl s) r
        (first_of_one r row (Code.encode S (fun s => (M s).replyCode) s))
    | two f x k => exact inner_two M s f x k row
  | transfer target =>
    have head : M.expand (.inl s) = .transfer (.inl target) :=
      first_of_transfer target row (Code.encode S (fun s => (M s).replyCode) s)
    exact loop_return (staged M) (.inl s) (v := .inr (.inl target)) (by simp only [staged, head])

private def innerBody (M : TransferPlans F S B) : Tm Empty Ops 1 :=
  .iter (.bv 0) (nativeBody (staged M)).underBinder

private theorem inner_typed (M : TransferPlans F S B) :
    H (.snoc .nil M.stateCode.ty) (innerBody M) (Code.sum B M.stateCode).ty :=
  .iter .bv (body_typed (staged M)).underBinder

private theorem specialize_inner (M : TransferPlans F S B) (v : M.stateCode.Value) :
    plug (innerBody M) (nativeValue Ops M.stateCode v) = .iter (nativeValue Ops M.stateCode v) (nativeBody (staged M)) := by
  unfold innerBody
  have eq : (nativeBody (staged M)).underBinder = widen (nativeBody (staged M)) 1 := by
    conv_lhs => rw [← widen_zero (nativeBody (staged M)), widen_under]
  rw [eq]
  exact loopArm_plug _ _

private theorem expansion_square (M : TransferPlans F S B) :
    E (.snoc .nil S.ty) (.case (nativePlans M) (.inl (.bv 0)) (.inr (.inl (.bv 0))))
      ((innerBody M).underBinder.instantiate (.inl (.bv 0))) (Code.sum B M.stateCode).ty := by
  have h := plans_typed M
  have bind := Equiv.bindCase (pureEff := pe) h
    (show H (.snoc (.snoc .nil S.ty) B.ty) (.inl (.bv 0)) (Code.sum B M.stateCode).ty from .inl .bv)
    (show H (.snoc (.snoc .nil S.ty) S.ty) (.inr (.inl (.bv 0))) (Code.sum B M.stateCode).ty from .inr (.inl .bv))
  change LocallyNameless.Equiv pe Free _ _ (.let₁ (nativePlans M) (embedControl Ops).underBinder) _ at bind
  rw [instantiate_under]
  refine (Refinement.equiv bind).trans (by_values S (.let₁ h embed_typed.underBinder)
    (plug_typed (inner_typed M) (.inl .bv)) (fun s => ?_))
  rw [plug_bind]
  have rhs : plug (plug (innerBody M) (.inl (.bv 0))) (nativeValue Ops S s (n := 0)) =
      plug (innerBody M) (nativeValue Ops M.stateCode (show (Code.sum S M.pending).Value from .inl s)) := by
    simp only [plug, Tm.bsubst_comp, Tm.bsubst]
    rfl
  refine Eq.mpr (congrArg (fun t => E .nil _ t (Code.sum B M.stateCode).ty) rhs) ?_
  rw [specialize_inner]
  exact (Refinement.let₁ (plans_beta M s) (.refl embed_typed)).trans
    ((embed_transfer (M s)).trans (inner_at M s).symm)

private theorem expand_native (M : TransferPlans F S B) (s : S.Value) :
    E .nil (.iter (nativeValue Ops S s) (nativePlans M))
      (.iter (nativeValue Ops M.stateCode (.inl s)) (nativePlans (fun u => rowPlan (M.expand u)))) B.ty := by
  have init := value_typed S s .nil (Φ := Ops)
  have map : H (.snoc .nil S.ty) (.inl (.bv 0)) M.stateCode.ty := .inl .bv
  have uniform := AbortNormalization.repaired_uniformity (pe := pe) init map (.inl .bv)
    (plans_typed M) (inner_typed M) (expansion_square M)
  have beta := Equiv.letBeta (pureEff := pe) (value_pure S s 0) init map
  have diagonal := Equiv.codiagonal (pureEff := pe) (value_typed M.stateCode (.inl s) .nil (Φ := Ops))
    (body_typed (staged M))
  exact uniform.trans ((Refinement.iter (.equiv beta) (.refl (inner_typed M))).trans
    ((Refinement.equiv diagonal).trans (.iter (.refl (value_typed M.stateCode (.inl s) .nil))
      (flatten_expanded M))))

theorem transfer_expand_eq (M : TransferPlans F S B) (s : S.Value) {a a' : Tm Empty Ops 0} {b b' : Tm Empty Ops 1}
    (ha : (S.literal s).toLetIter 0 = some a) (hb : M.source.toLetIter 1 = some b)
    (ha' : (M.stateCode.literal (.inl s)).toLetIter 0 = some a')
    (hb' : M.expand.source.toLetIter 1 = some b') :
    E .nil (.iter a b) (.iter a' b') B.ty := by
  have sameA := Option.some.inj (ha.symm.trans (value_lowers S s 0))
  have sameB := Option.some.inj (hb.symm.trans (plans_lowers M))
  have sameA' := Option.some.inj (ha'.symm.trans (value_lowers M.stateCode (.inl s) 0))
  have sameB' := Option.some.inj (hb'.symm.trans (expanded_lowers M.expand))
  subst a b a' b'
  exact expand_native M s

theorem expand_eq (M : Plans F S B) (s : S.Value) {a a' : Tm Empty Ops 0} {b b' : Tm Empty Ops 1}
    (ha : (S.literal s).toLetIter 0 = some a) (hb : M.source.toLetIter 1 = some b)
    (ha' : (M.stateCode.literal (.inl s)).toLetIter 0 = some a')
    (hb' : M.expand.source.toLetIter 1 = some b') :
    E .nil (.iter a b) (.iter a' b') B.ty :=
  transfer_expand_eq M.withTransfers s ha hb ha'
    (by rw [M.withTransfers_expanded_source]; exact hb')

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.TerminalProofs
