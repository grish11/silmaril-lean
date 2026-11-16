module

public import Silmaril.Wasm.Abstract.ExposePStruct.Defs
public import Silmaril.Wasm.Abstract.Body.Thms
public import Silmaril.Wasm.Abstract.BodyTrace.Thms

/-!
Proofs for `Silmaril.Wasm.Abstract.ExposePStruct.Thms`: the exit-aware Kleisli structure of
`denListXP`, its constructor equations and its congruence for `BodyTrace.FullCollapseEquiv`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.ExposePStruct

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Abstract.BodyTrace
open Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
open Silmaril.Wasm.Abstract.ExposeP Silmaril.Wasm.Abstract.ExposePStruct
open Silmaril.Wasm.Abstract.CallXP (POut)

variable {H : Type}

/-! ## Results -/

/-- A body result falls through, or every continuation passes it. -/
theorem resP_cases (r : ResP) :
    (∃ f stk, r = ⟨(f, .flow (.normal stk))⟩) ∨
      ∀ k : Frame → List Val → M (CallSig H) H ResP, thenKP k r = pure r := by
  rcases r with ⟨f, (fl | ⟨a, args, n⟩)⟩
  · cases fl with
    | normal stk => exact .inl ⟨f, stk, rfl⟩
    | _ => exact .inr fun _ => rfl
  · exact .inr fun _ => rfl

theorem thenKP_unit (r : ResP) :
    thenKP (H := H) (fun f stk => pure ⟨(f, .flow (.normal stk))⟩) r = pure r := by
  rcases resP_cases (H := H) r with ⟨f, stk, rfl⟩ | h
  · rfl
  · exact h _

theorem thenKP_assoc (k k' : Frame → List Val → M (CallSig H) H ResP) (r : ResP) :
    (thenKP k r >>= thenKP k') = thenKP (fun f stk => k f stk >>= thenKP k') r := by
  rcases resP_cases (H := H) r with ⟨f, stk, rfl⟩ | h
  · rfl
  · rw [h, h, pure_bind, h]

/-! ## Equations of the denotation -/

theorem denListXP_nil (f : Frame) (stk : List Val) :
    (denListXP (H := H) [] f stk) = pure ⟨(f, .flow (.normal stk))⟩ := by
  rw [denListXP.eq_def]

theorem denListXP_cons (e : BExpr) (es : List BExpr) (f : Frame) (stk : List Val) :
    (denListXP (H := H) (e :: es) f stk) = denXP e f stk >>= thenKP (denListXP es) := by
  rw [denListXP.eq_def]

theorem denListXP_append (es₁ es₂ : List BExpr) (f : Frame) (stk : List Val) :
    (denListXP (H := H) (es₁ ++ es₂) f stk) =
      denListXP es₁ f stk >>= thenKP (denListXP es₂) := by
  induction es₁ generalizing f stk with
  | nil => rw [List.nil_append, denListXP_nil, pure_bind]; rfl
  | cons e es₁ ih =>
    have hk : (denListXP (H := H) (es₁ ++ es₂)) =
        fun f stk => denListXP es₁ f stk >>= thenKP (denListXP es₂) := funext fun f => funext (ih f)
    rw [List.cons_append, denListXP_cons, denListXP_cons, hk, bind_assoc]
    congr 1
    funext r
    rw [thenKP_assoc]

theorem denListXP_singleton (e : BExpr) (f : Frame) (stk : List Val) :
    (denListXP (H := H) [e] f stk) = denXP e f stk := by
  rw [denListXP_cons]
  have : (denListXP (H := H) []) = fun f stk => pure ⟨(f, .flow (.normal stk))⟩ :=
    funext fun f => funext (denListXP_nil f)
  rw [this]
  conv_rhs => rw [← bind_pure (denXP e f stk)]
  congr 1
  funext r
  exact thenKP_unit r

/-! ## The exit-aware Kleisli category -/

theorem denL_nil : (denL (H := H) []) = idP := by
  funext c; exact denListXP_nil _ _

theorem denL_append (es₁ es₂ : List BExpr) :
    (denL (H := H) (es₁ ++ es₂)) = seqP (denL es₁) (denL es₂) := by
  funext c; exact denListXP_append es₁ es₂ _ _

theorem denL_cons (e : BExpr) (es : List BExpr) :
    (denL (H := H) (e :: es)) = seqP (denT e) (denL es) := by
  funext c; exact denListXP_cons e es _ _

theorem denL_singleton (e : BExpr) : (denL (H := H) [e]) = denT e := by
  funext c; exact denListXP_singleton e _ _

theorem seqP_id_left (g : PHom H Cfg ResP) : seqP idP g = g := by
  funext c; simp only [seqP, idP, pure_bind]; rfl

theorem seqP_id_right (g : PHom H Cfg ResP) : seqP g idP = g := by
  funext c
  simp only [seqP, contP, idP]
  conv_rhs => rw [← bind_pure (g c)]
  congr 1
  funext r
  exact thenKP_unit r

theorem seqP_assoc (g₁ g₂ g₃ : PHom H Cfg ResP) :
    seqP (seqP g₁ g₂) g₃ = seqP g₁ (seqP g₂ g₃) := by
  funext c
  simp only [seqP, contP, bind_assoc]
  congr 1
  funext r
  rw [thenKP_assoc]

/-! ## Constructors -/

theorem denT_op (i : Instr) (args : List BExpr) :
    (denT (H := H) (.op i args)) = opP i (denL args) := by
  funext c; simp only [denT, opP, denL]; rw [denXP.eq_def]

theorem denT_block (bt : BlockType) (body : List BExpr) :
    (denT (H := H) (.block bt body)) = blockP bt (denL body) := by
  funext c; simp only [denT, blockP, denL]; rw [denXP.eq_def]; rfl

theorem denT_loop (bt : BlockType) (body : List BExpr) :
    (denT (H := H) (.loop bt body)) = loopP bt (denL body) := by
  funext c; simp only [denT, loopP]; rw [denXP.eq_def]; rfl

theorem ifKP_eq (bt : BlockType) (t el : List BExpr) :
    (ifKP (H := H) bt (denL t) (denL el)) = fun r =>
      match r with
      | ⟨(f₁, .flow (.normal (cv :: stk₁)))⟩ =>
        match truthy cv, arity f₁ bt with
        | some b, some (np, nr) =>
          (if b then denListXP t f₁ (stk₁.take np) else denListXP el f₁ (stk₁.take np)) >>=
            blockKP np nr stk₁
        | _, _ => stuck
      | ⟨(_, .flow (.normal []))⟩ => stuck
      | r => pure r := by
  funext r
  rcases r with ⟨f, (fl | ⟨a, args, n⟩)⟩
  · cases fl with
    | normal stk => cases stk <;> rfl
    | _ => rfl
  · rfl

theorem denT_if (bt : BlockType) (c t el : List BExpr) :
    (denT (H := H) (.if_ bt c t el)) = ifP bt (denL c) (denL t) (denL el) := by
  funext x; simp only [denT, ifP]; rw [ifKP_eq, denXP.eq_def]; rfl

theorem denT_try (bt : BlockType) (cs : List Catch) (body : List BExpr) :
    (denT (H := H) (.tryTable bt cs body)) = tryP bt cs (denL body) := by
  funext c; simp only [denT, tryP, denL]; rw [denXP.eq_def]; rfl

theorem loopP_unfold (bt : BlockType) (g : PHom H Cfg ResP) :
    loopP bt g = fun c => loopStepP bt g c >>= Sum.elim pure (loopP bt g) :=
  Silmaril.Elgot.LawfulElgotMonad.fixpoint (m := M (CallSig H) H) (loopStepP bt g)

/-! ## Congruence for the observable quotient -/

theorem contP_congr {g g' : PHom H Cfg ResP} (h : ∀ c, collapse (g c) = collapse (g' c))
    (r : ResP) : collapse (contP g r) = collapse (contP g' r) := by
  rcases resP_cases (H := H) r with ⟨f, stk, rfl⟩ | hp
  · exact h _
  · simp only [contP, hp]

theorem thenKP_congr {k k' : Frame → List Val → M (CallSig H) H ResP}
    (h : ∀ f stk, collapse (k f stk) = collapse (k' f stk)) (r : ResP) :
    collapse (thenKP k r) = collapse (thenKP k' r) := by
  rcases resP_cases (H := H) r with ⟨f, stk, rfl⟩ | hp
  · exact h _ _
  · simp only [hp]

theorem seqP_congr {g₁ g₁' g₂ g₂' : PHom H Cfg ResP} (h₁ : FullCollapseEquiv g₁ g₁')
    (h₂ : FullCollapseEquiv g₂ g₂') : FullCollapseEquiv (seqP g₁ g₂) (seqP g₁' g₂') := by
  refine FullCollapseEquiv.comp h₁ ((fullCollapseEquiv_iff _ _).2 fun r => ?_)
  exact contP_congr ((fullCollapseEquiv_iff _ _).1 h₂) r

theorem opP_congr (i : Instr) {g g' : PHom H Cfg ResP} (h : FullCollapseEquiv g g') :
    FullCollapseEquiv (opP i g) (opP i g') :=
  FullCollapseEquiv.comp h ((fullCollapseEquiv_iff _ _).2 fun _ => rfl)

theorem blockP_congr (bt : BlockType) {g g' : PHom H Cfg ResP} (h : FullCollapseEquiv g g') :
    FullCollapseEquiv (blockP bt g) (blockP bt g') := by
  rw [fullCollapseEquiv_iff] at h ⊢
  intro c
  unfold blockP
  split
  · rw [collapse_bind, collapse_bind, h]
  · rfl

theorem loopStepP_congr (bt : BlockType) {g g' : PHom H Cfg ResP} (h : FullCollapseEquiv g g') :
    FullCollapseEquiv (loopStepP bt g) (loopStepP bt g') := by
  rw [fullCollapseEquiv_iff] at h ⊢
  intro c
  unfold loopStepP
  split
  · rw [collapse_bind, collapse_bind, h]
  · rfl

theorem loopP_congr (bt : BlockType) {g g' : PHom H Cfg ResP} (h : FullCollapseEquiv g g') :
    FullCollapseEquiv (loopP bt g) (loopP bt g') :=
  FullCollapseEquiv.iter (loopStepP_congr bt h)

theorem tryP_congr (bt : BlockType) (cs : List Catch) {g g' : PHom H Cfg ResP}
    (h : FullCollapseEquiv g g') : FullCollapseEquiv (tryP bt cs g) (tryP bt cs g') := by
  rw [fullCollapseEquiv_iff] at h ⊢
  intro c
  unfold tryP
  split
  · rw [collapse_bind, collapse_bind, h]
  · rfl

theorem ifKP_congr (bt : BlockType) {gt gt' ge ge' : PHom H Cfg ResP}
    (ht : ∀ c, collapse (gt c) = collapse (gt' c)) (he : ∀ c, collapse (ge c) = collapse (ge' c))
    (r : ResP) : collapse (ifKP bt gt ge r) = collapse (ifKP bt gt' ge' r) := by
  rcases r with ⟨f, (fl | ⟨a, args, n⟩)⟩
  · cases fl with
    | normal stk =>
      cases stk with
      | nil => rfl
      | cons cv stk₁ =>
        simp only [ifKP]
        split
        · rename_i b np nr _ _
          cases b
          · simp only [Bool.false_eq_true, ite_false, collapse_bind, he]
          · simp only [ite_true, collapse_bind, ht]
        · rfl
    | _ => rfl
  · rfl

theorem ifP_congr (bt : BlockType) {gc gc' gt gt' ge ge' : PHom H Cfg ResP}
    (hc : FullCollapseEquiv gc gc') (ht : FullCollapseEquiv gt gt')
    (he : FullCollapseEquiv ge ge') :
    FullCollapseEquiv (ifP bt gc gt ge) (ifP bt gc' gt' ge') := by
  refine FullCollapseEquiv.comp hc ((fullCollapseEquiv_iff _ _).2 fun r => ?_)
  exact ifKP_congr bt ((fullCollapseEquiv_iff _ _).1 ht) ((fullCollapseEquiv_iff _ _).1 he) r

end Silmaril.Proofs.Wasm.Abstract.ExposePStruct
