module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Terminal.Expansion.Defs
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

def nativePlans (M : Plans F S B) : Tm Empty Ops 1 :=
  dispatch S (fun m s => nativePlan (M s) m) (.bv 0)

theorem plans_lowers (M : Plans F S B) : M.source.toLetIter 1 = some (nativePlans M) :=
  dispatch_lowers S (fun m s => plan_lowers (M s) m) (a := .var 0) (arg := .bv 0) rfl

private theorem plans_typed (M : Plans F S B) :
    H (.snoc .nil S.ty) (nativePlans M) (Code.sum B S).ty :=
  dispatch_typed S (fun β s => plan_typed (M s) β) .bv

variable {ε : Type} [HasEff (Opcode F) ε] {pe : ε}

local notation "E" => AbortEquiv (Φ := Ops) pe Free

private theorem plans_beta (M : Plans F S B) (s : S.Value) :
    E .nil (plug (nativePlans M) (nativeValue Ops S s)) (nativePlan (M s) 0) (Code.sum B S).ty := by
  rw [plug, nativePlans, dispatch_subst S (fun σ s => plan_subst (M s) σ)]
  exact dispatch_beta S (fun β s => plan_typed (M s) β) (fun σ s => plan_subst (M s) σ) .nil s

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

private def staged (M : Plans F S B) : Table F M.stateCode (Code.sum B M.stateCode) :=
  stageWith M.expand (fun u v => u.isLeft && !v.isLeft)

private def asOuter (T : Code) (r : Row F S B) : Row F (Code.sum S T) (Code.sum B (Code.sum S T)) :=
  match r with
  | .ret b => .ret (.inl b)
  | .call f x k => .call f x (fun r => .inl (Sum.map id Sum.inl (k r)))

private theorem staged_outer (M : Plans F S B) (u : M.stateCode.Value) (r : Row F S B)
    (atRow : M.expand u = r.map (T := M.stateCode) Sum.inl) : staged M u = asOuter M.pending r := by
  cases r with
  | ret b => simp only [staged, stageWith, atRow, Row.map, asOuter]
  | call f x k =>
    simp only [staged, stageWith, atRow, Row.map, asOuter]
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

private theorem inner_outer (M : Plans F S B) (u : M.stateCode.Value) (r : Row F S B)
    (atRow : M.expand u = r.map (T := M.stateCode) Sum.inl) :
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

private def pending (M : Plans F S B) (s : S.Value) (v : (M s).replyCode.Value) : M.stateCode.Value :=
  .inr (Code.encode S (fun s => (M s).replyCode) s v)

private theorem pending_row (M : Plans F S B) (s : S.Value) (v : (M s).replyCode.Value) :
    M.expand (pending M s v) = ((M s).second v).map (T := M.stateCode) Sum.inl := by
  simp only [pending, Plans.expand]
  rw [decode_encode S (fun s => (M s).replyCode) s v]

private theorem second_of_two {p : Plan F S B} {f : Ops} {x : f.argCode.Value}
    {k : f.replyCode.Value → Row F S B} (row : p = .two f x k) (v : f.replyCode.Value) :
    p.second (row.symm ▸ v) = k v := by subst p; rfl

private theorem first_of_one {p : Plan F S B} (r : Row F S B) (eq : p = .one r)
    (encode : p.replyCode.Value → T.Value) :
    p.expandFirst T encode = r.map Sum.inl := by subst p; rfl

private theorem first_of_two {p : Plan F S B} {f : Ops} {x : f.argCode.Value}
    {k : f.replyCode.Value → Row F S B} (eq : p = .two f x k)
    (encode : p.replyCode.Value → T.Value) :
    p.expandFirst T encode = .call f x (fun v => .inr (.inr (encode (eq.symm ▸ v)))) := by
  subst p
  rfl

private theorem inner_at (M : Plans F S B) (s : S.Value) :
    E .nil (.iter (nativeValue Ops M.stateCode (.inl s)) (nativeBody (staged M)))
      (nativePlan (embedPlan (M s) M.pending) 0) (Code.sum B M.stateCode).ty := by
  cases row : M s with
  | one r =>
    exact inner_outer M (.inl s) r
      (first_of_one r row (Code.encode S (fun s => (M s).replyCode) s))
  | two f x k =>
    let next (v : f.replyCode.Value) : M.stateCode.Value := pending M s (row.symm ▸ v)
    have step : staged M (.inl s) = .call f x (fun v => .inr (next v)) := by
      have head : M.expand (.inl s) = .call f x (fun v => .inr (next v)) :=
        first_of_two row (Code.encode S (fun s => (M s).replyCode) s)
      unfold staged stageWith
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
    have chosen : M.expand (next v) = (k v).map (T := M.stateCode) Sum.inl := by
      rw [show next v = pending M s (row.symm ▸ v) from rfl, pending_row, second_of_two row v]
    exact (bind_value handle (.inr (next v))).trans
      ((loopHandler_right body (next v)).trans (inner_outer M (next v) (k v) chosen))

private def innerBody (M : Plans F S B) : Tm Empty Ops 1 :=
  .iter (.bv 0) (nativeBody (staged M)).underBinder

private theorem inner_typed (M : Plans F S B) :
    H (.snoc .nil M.stateCode.ty) (innerBody M) (Code.sum B M.stateCode).ty :=
  .iter .bv (body_typed (staged M)).underBinder

private theorem specialize_inner (M : Plans F S B) (v : M.stateCode.Value) :
    plug (innerBody M) (nativeValue Ops M.stateCode v) = .iter (nativeValue Ops M.stateCode v) (nativeBody (staged M)) := by
  unfold innerBody
  have eq : (nativeBody (staged M)).underBinder = widen (nativeBody (staged M)) 1 := by
    conv_lhs => rw [← widen_zero (nativeBody (staged M)), widen_under]
  rw [eq]
  exact loopArm_plug _ _

private theorem expansion_square (M : Plans F S B) :
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
    ((embed_plan (M s)).trans (inner_at M s).symm)

theorem expand_native (M : Plans F S B) (s : S.Value) :
    E .nil (.iter (nativeValue Ops S s) (nativePlans M))
      (.iter (nativeValue Ops M.stateCode (.inl s)) (nativeBody M.expand)) B.ty := by
  have init := value_typed S s .nil (Φ := Ops)
  have map : H (.snoc .nil S.ty) (.inl (.bv 0)) M.stateCode.ty := .inl .bv
  have uniform := AbortNormalization.repaired_uniformity (pe := pe) init map (.inl .bv)
    (plans_typed M) (inner_typed M) (expansion_square M)
  have beta := Equiv.letBeta (pureEff := pe) (value_pure S s 0) init map
  have diagonal := Equiv.codiagonal (pureEff := pe) (value_typed M.stateCode (.inl s) .nil (Φ := Ops))
    (body_typed (staged M))
  exact uniform.trans ((Refinement.iter (.equiv beta) (.refl (inner_typed M))).trans
    ((Refinement.equiv diagonal).trans (.iter (.refl (value_typed M.stateCode (.inl s) .nil))
      (flatten_stage_with M.expand (fun u v => u.isLeft && !v.isLeft)))))

theorem expand_eq (M : Plans F S B) (s : S.Value) {a a' : Tm Empty Ops 0} {b b' : Tm Empty Ops 1}
    (ha : (S.literal s).toLetIter 0 = some a) (hb : M.source.toLetIter 1 = some b)
    (ha' : (M.stateCode.literal (.inl s)).toLetIter 0 = some a')
    (hb' : M.expand.source.toLetIter 1 = some b') :
    E .nil (.iter a b) (.iter a' b') B.ty := by
  have sameA := Option.some.inj (ha.symm.trans (value_lowers S s 0))
  have sameB := Option.some.inj (hb.symm.trans (plans_lowers M))
  have sameA' := Option.some.inj (ha'.symm.trans (value_lowers M.stateCode (.inl s) 0))
  have sameB' := Option.some.inj (hb'.symm.trans (body_lowers M.expand))
  subst a b a' b'
  exact expand_native M s

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.TerminalProofs
