module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Terminal.Defs
public import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Terminal.Constructor
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Equations.Thms
import Silmaril.SSA.Isotope.LetIter.AbortSequence.Thms

@[expose] public section

open Silmaril.Isotope Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.PaperExpression

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.TerminalProofs

variable {Φ ε : Type} [HasTy Φ (Ty Unit)] [HasEff Φ ε] {pe : ε}

local notation "Free" => (Ctx.nil : Ctx Empty (Ty Unit))
local notation "H" => HasType Φ Free
local notation "E" => AbortEquiv (Φ := Φ) pe Free

/-- Native constructor dispatch. The branch family is supplied uniformly in
the ambient scope. -/
def dispatch (c : Code) (rows : ∀ n, c.Value → Tm Empty Φ n) {n : Nat} (arg : Tm Empty Φ n) :
    Tm Empty Φ n :=
  match c with
  | .unit => rows n PUnit.unit
  | .sum l r => .case arg
      (dispatch l (fun m v => rows m (.inl v)) (.bv 0))
      (dispatch r (fun m v => rows m (.inr v)) (.bv 0))

omit [HasTy Φ (Ty Unit)] [HasEff Φ ε] in
theorem dispatch_lowers (c : Code) {rows : ∀ n, c.Value → Tm Empty Φ n} {src : c.Value → Expr Φ}
    (lower : ∀ n v, (src v).toLetIter n = some (rows n v))
    {n : Nat} {a : Expr Φ} {arg : Tm Empty Φ n} (ha : a.toLetIter n = some arg) :
    (c.dispatch src a).toLetIter n = some (dispatch c rows arg) := by
  induction c generalizing n a with
  | unit => exact lower _ _
  | sum l r il ir =>
    simp only [Code.dispatch, Expr.toLetIter, ha, dispatch]
    rw [il (fun m v => lower m (.inl v)) (a := .var 0) (arg := .bv 0) rfl,
      ir (fun m v => lower m (.inr v)) (a := .var 0) (arg := .bv 0) rfl]
    rfl

omit [HasEff Φ ε] in
theorem dispatch_typed (c : Code) {rows : ∀ n, c.Value → Tm Empty Φ n} {C : Ty Unit}
    (typed : ∀ {m} (δ : BoundCtx (Ty Unit) m) v, H δ (rows m v) C)
    {n : Nat} {β : BoundCtx (Ty Unit) n} {arg : Tm Empty Φ n} (ha : H β arg c.ty) :
    H β (dispatch c rows arg) C := by
  induction c generalizing n with
  | unit => exact typed _ _
  | sum l r il ir =>
    exact .case ha (il (fun δ v => typed δ (.inl v)) .bv)
      (ir (fun δ v => typed δ (.inr v)) .bv)

omit [HasTy Φ (Ty Unit)] [HasEff Φ ε] in
theorem dispatch_subst (c : Code) {rows : ∀ n, c.Value → Tm Empty Φ n}
    (closed : ∀ {n m} (σ : Fin n → Tm Empty Φ m) v, (rows n v).bsubst σ = rows m v)
    {n m : Nat} (σ : Fin n → Tm Empty Φ m) (arg : Tm Empty Φ n) :
    (dispatch c rows arg).bsubst σ = dispatch c rows (arg.bsubst σ) := by
  induction c generalizing n m with
  | unit => exact closed _ _
  | sum l r il ir =>
    simp only [dispatch, Tm.bsubst]
    rw [il (fun s v => closed s (.inl v)), ir (fun s v => closed s (.inr v))]
    rfl

theorem dispatch_beta (c : Code) {rows : ∀ n, c.Value → Tm Empty Φ n} {C : Ty Unit}
    (typed : ∀ {m} (δ : BoundCtx (Ty Unit) m) v, H δ (rows m v) C)
    (closed : ∀ {n m} (σ : Fin n → Tm Empty Φ m) v, (rows n v).bsubst σ = rows m v)
    {n : Nat} (β : BoundCtx (Ty Unit) n) (v : c.Value) :
    E β (dispatch c rows (nativeValue Φ c v)) (rows n v) C := by
  induction c with
  | unit => cases v; exact .equiv (.refl (typed _ _))
  | sum l r il ir =>
    have left := dispatch_typed l (fun δ v => typed δ (.inl v))
      (show H (β.snoc l.ty) (.bv 0) l.ty from .bv)
    have right := dispatch_typed r (fun δ v => typed δ (.inr v))
      (show H (β.snoc r.ty) (.bv 0) r.ty from .bv)
    cases v with
    | inl x =>
      have eq := Equiv.letBeta (pureEff := pe) (value_pure l x n) (value_typed l x β) left
      simp only [Tm.instantiate, dispatch_subst _ (fun σ v => closed σ (.inl v)),
        Tm.bsubst, Fin.cases_zero] at eq
      exact (Refinement.equiv ((Equiv.caseBetaL (value_typed l x β) left right).trans eq)).trans
        (il (fun δ v => typed δ (.inl v)) (fun σ v => closed σ (.inl v)) x)
    | inr x =>
      have eq := Equiv.letBeta (pureEff := pe) (value_pure r x n) (value_typed r x β) right
      simp only [Tm.instantiate, dispatch_subst _ (fun σ v => closed σ (.inr v)),
        Tm.bsubst, Fin.cases_zero] at eq
      exact (Refinement.equiv ((Equiv.caseBetaR (value_typed r x β) left right).trans eq)).trans
        (ir (fun δ v => typed δ (.inr v)) (fun σ v => closed σ (.inr v)) x)

variable {fcount : Nat} {F : Family fcount} {S B : Code}

local notation "Ops" => Opcode F

def nativeReply {f : Ops} (k : f.replyCode.Value → B.Value ⊕ S.Value) {n : Nat} (arg : Tm Empty Ops n) :=
  dispatch f.replyCode (fun _ v => nativeValue Ops (Code.sum B S) (k v)) arg

def nativeRow (row : Row F S B) (n : Nat) : Tm Empty Ops n :=
  match row with
  | .ret b => nativeValue Ops (Code.sum B S) (.inl b)
  | .call f x k => .let₁ (.op f (nativeValue Ops f.argCode x)) (nativeReply k (.bv 0))

theorem row_lowers (row : Row F S B) (n : Nat) :
    row.source.toLetIter n = some (nativeRow row n) := by
  cases row with
  | ret b => exact value_lowers (Code.sum B S) (.inl b) n
  | call f x k =>
    simp only [nativeRow, Row.source, Expr.toLetIter, value_lowers, replySource, nativeReply]
    rw [dispatch_lowers f.replyCode
      (fun m r => value_lowers (Code.sum B S) (k r) m) (a := .var 0) (arg := .bv 0) rfl]
    rfl

theorem reply_typed {f : Ops} (k : f.replyCode.Value → B.Value ⊕ S.Value)
    {n : Nat} {β : BoundCtx (Ty Unit) n} {arg : Tm Empty Ops n} (ha : HasType Ops Free β arg f.replyCode.ty) :
    HasType Ops Free β (nativeReply k arg) (Code.sum B S).ty :=
  dispatch_typed _ (fun β v => value_typed (Code.sum B S) (k v) β) ha

theorem row_typed (row : Row F S B) {n : Nat} (β : BoundCtx (Ty Unit) n) :
    HasType Ops Free β (nativeRow row n) (Code.sum B S).ty := by
  cases row with
  | ret b => exact value_typed (Code.sum B S) (.inl b) β
  | call f x k => exact .let₁ (.op (value_typed _ x β)) (reply_typed k .bv)

@[simp] theorem reply_subst {f : Ops} (k : f.replyCode.Value → B.Value ⊕ S.Value)
    {n m : Nat} (σ : Fin n → Tm Empty Ops m) (a : Tm Empty Ops n) :
    (nativeReply k a).bsubst σ = nativeReply k (a.bsubst σ) :=
  dispatch_subst _ (fun σ v => value_bsubst σ (Code.sum B S) (k v)) σ a

@[simp] theorem row_subst (row : Row F S B) {n m : Nat} (σ : Fin n → Tm Empty Ops m) :
    (nativeRow row n).bsubst σ = nativeRow row m := by
  cases row with
  | ret v => exact value_bsubst σ (Code.sum B S) (.inl v)
  | call f x k => simp [nativeRow, Tm.bsubst, Tm.upSub]

theorem reply_beta [HasEff Ops ε] {f : Ops} (k : f.replyCode.Value → B.Value ⊕ S.Value)
    (r : f.replyCode.Value) :
    AbortEquiv pe Free .nil (nativeReply k (nativeValue Ops f.replyCode r))
      (nativeValue Ops (Code.sum B S) (k r)) (Code.sum B S).ty :=
  dispatch_beta _ (fun β v => value_typed (Code.sum B S) (k v) β) (fun σ v => value_bsubst σ (Code.sum B S) (k v)) .nil r

def nativeBody (M : Table F S B) : Tm Empty Ops 1 :=
  dispatch S (fun m s => nativeRow (M s) m) (.bv 0)

theorem body_lowers (M : Table F S B) : M.source.toLetIter 1 = some (nativeBody M) :=
  dispatch_lowers S (fun m s => row_lowers (M s) m) (a := .var 0) (arg := .bv 0) rfl

theorem body_typed (M : Table F S B) :
    HasType Ops Free (.snoc .nil S.ty) (nativeBody M) (Code.sum B S).ty :=
  dispatch_typed S (fun β s => row_typed (M s) β) .bv

theorem body_beta [HasEff Ops ε] (M : Table F S B) (s : S.Value) :
    AbortEquiv pe Free .nil (plug (nativeBody M) (nativeValue Ops S s)) (nativeRow (M s) 0) (Code.sum B S).ty := by
  rw [plug, nativeBody, dispatch_subst S (fun σ v => row_subst (M v) σ)]
  exact dispatch_beta _ (fun β v => row_typed (M v) β) (fun σ v => row_subst (M v) σ) .nil s

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.TerminalProofs
