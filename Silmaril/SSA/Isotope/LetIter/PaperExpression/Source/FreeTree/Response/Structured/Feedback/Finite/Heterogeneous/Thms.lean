module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Denotation.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Observation
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Square
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Denotation
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Replay

/-! # Reflection for rendered heterogeneous feedback tables -/

public section

open Silmaril.Isotope Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless (Tm Derivation HasTypeEffect AbortEquiv)
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic (repairedDenoteInSyntax)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous

variable {n : Nat} {F : Family n} {S T B : Code} {L : Table F S B} {R : Table F T B}
  {s₀ : S.Value} {t₀ : T.Value}

/-- Unfold the observation of an immediate return or a single typed call. -/
theorem Table.run_unfold (M : Table F S B) (s : S.Value) :
    M.run s = match M s with
    | .ret v => ITree.ret (B.raise v)
    | .call f x k => ITree.vis (.call f x) (fun r => Sum.elim (fun b => ITree.ret (B.raise b)) M.run (k r)) :=
  Proofs.run_unfold M s

/-- A commuting state map preserves all weak observations. -/
theorem runs_eq {h : S.Value → T.Value} (comm : Commutes L R h) (s : S.Value) :
    L.run s = R.run (h s) :=
  Proofs.runs_eq comm s

/-- Initial equality propagates along every synchronized repeat path. -/
theorem PairedReach.run_eq (obs : L.run s₀ = R.run t₀)
    {p : S.Value × T.Value} (reach : PairedReach L R s₀ t₀ p) :
    L.run p.1 = R.run p.2 :=
  Proofs.run_eq_of_reach obs reach

/-- If all repeat targets are calls, equal observations force the reply modes to agree. -/
theorem aligned_of_guarded (obs : L.run s₀ = R.run t₀) (left : Guarded L) (right : Guarded R) :
    ReplyAligned L R s₀ t₀ :=
  Proofs.aligned_of_guarded obs left right

/-- Encode the synchronized reachable pairs when reply modes agree. Visible
node inversion identifies the full dependent request and compares each reply
after transporting along equality of its opcode. -/
theorem exists_cover (obs : L.run s₀ = R.run t₀) (aligned : ReplyAligned L R s₀ t₀) :
    Nonempty (Cover L R s₀ t₀) :=
  Proofs.exists_cover obs aligned

/-- Both cover projections preserve reply modes, so alignment is necessary
for this form of replay on the synchronized reachable pairs. -/
theorem Cover.aligned (C : Cover L R s₀ t₀) : ReplyAligned L R s₀ t₀ :=
  Proofs.aligned_of_cover C

/-- A rendered row references only the local reply variable. -/
theorem Row.source_subst (row : Row F S B) (σ : Nat → Expr (Opcode F)) :
    row.source.subst σ = row.source :=
  Proofs.row_closed row σ

variable {ε : Type} [HasEff (Opcode F) ε] [SemilatticeSup ε] [OrderBot ε]
  {e : ε} {s : S.Value} {t : T.Value}

local notation "Ops" => Opcode F
local notation "Free" => (Ctx.nil : Ctx Empty (Ty Unit))
local notation "D" => Ty.denote (Lifted carriers)
local notation "γ" => (fun x : Empty => x.elim)
local notation "ρ₀" => (fun i : Fin 0 => i.elim0)
local notation "slot[" c "]" => (Code.ty c, (⊥ : ε))

/-- A rendered row has its declared control result in any ambient context. -/
theorem Row.source_wf (row : Row F S B) (hf : ∀ f : Ops, instrEff f ≤ e)
    {Γ : EffectCtx (Ty Unit) ε} : Wf Γ row.source (Code.sum B S).ty e :=
  Proofs.row_wf row hf

/-- The rendered body has its declared control result at the supplied bound. -/
theorem Table.step_wf (L : Table F S B) (hf : ∀ f : Ops, instrEff f ≤ e) :
    Wf [slot[S]] L.source (Code.sum B S).ty e :=
  Proofs.step_wf L hf

/-- A commuting map yields a source equation at the supplied bound. -/
theorem source_square {L : Table F S B} {R : Table F T B}
    (h : S.Value → T.Value) (square : Commutes L R h) (hf : ∀ f : Ops, instrEff f ≤ e) :
    Eqv [slot[S]] (Code.sum B T).ty e
      (.case L.source (.inl (.var 0)) (.inr (stateMap S T h)))
      (T.dispatch (fun t => (R t).source) (stateMap S T h)) :=
  Proofs.source_square h square hf

variable [EffectIteration ε]

/-- The actual lowered step gives the exact immediate return or typed request. -/
theorem step_denote (P : PureMaps (Φ := Ops) (ε := ε) carriers)
    (visible : ∀ f : Ops, ¬ IsPure (⊥ : ε) f) (M : Table F S B)
    (hf : ∀ f : Ops, instrEff f ≤ e) (s : S.Value)
    {b : Tm Empty Ops 1} (hb : M.source.toLetIter 1 = some b)
    (db : Derivation Ops Free (.snoc .nil S.ty) b (Code.sum B S).ty) :
    db.denote D (instructions carriers P) γ (BoundEnv.snoc ρ₀ (S.raise s)) = (M s).step :=
  Proofs.step_denote P visible M hf s hb db

/-- The actual lowered iterator denotes the table interpreter on the encoded state. -/
theorem loop_denote (P : PureMaps (Φ := Ops) (ε := ε) carriers)
    (visible : ∀ f : Ops, ¬ IsPure (⊥ : ε) f) (M : Table F S B)
    (hf : ∀ f : Ops, instrEff f ≤ e) (s : S.Value)
    {a : Tm Empty Ops 0} {b : Tm Empty Ops 1}
    (ha : (S.literal s).toLetIter 0 = some a) (hb : M.source.toLetIter 1 = some b)
    (da : Derivation Ops Free .nil a S.ty) (db : Derivation Ops Free (.snoc .nil S.ty) b (Code.sum B S).ty) :
    (da.iter db).denote D (instructions carriers P) γ ρ₀ = M.run s :=
  Proofs.loop_denote P visible M hf s ha hb da db

/-- Replay both cover projections by native uniformity at the supplied bound. -/
theorem replay_of_run_eq (obs : L.run s = R.run t)
    (aligned : ReplyAligned L R s t) (hf : ∀ f : Ops, instrEff f ≤ e) (he : IsIterative e) :
    ∃ (a a' : Tm Empty Ops 0) (b b' : Tm Empty Ops 1),
      (S.literal s).toLetIter 0 = some a ∧ (T.literal t).toLetIter 0 = some a' ∧
      L.source.toLetIter 1 = some b ∧ R.source.toLetIter 1 = some b' ∧
      HasTypeEffect Free .nil (.iter a b) B.ty e ∧ HasTypeEffect Free .nil (.iter a' b') B.ty e ∧
      AbortEquiv (⊥ : ε) Free .nil (.iter a b) (.iter a' b') B.ty :=
  Proofs.replay_of_run_eq obs aligned hf he

/-- Under reply alignment, table observation equality is equivalent to equality
of the repaired packed denotations. -/
theorem packed_eq_iff_run_eq {a a' : Tm Empty Ops 0} {b b' : Tm Empty Ops 1}
    (ha : (S.literal s).toLetIter 0 = some a) (hb : L.source.toLetIter 1 = some b)
    (ha' : (T.literal t).toLetIter 0 = some a') (hb' : R.source.toLetIter 1 = some b')
    (da : Derivation Ops Free .nil a S.ty) (db : Derivation Ops Free (.snoc .nil S.ty) b (Code.sum B S).ty)
    (da' : Derivation Ops Free .nil a' T.ty) (db' : Derivation Ops Free (.snoc .nil T.ty) b' (Code.sum B T).ty)
    (P : PureMaps (Φ := Ops) (ε := ε) carriers)
    (visible : ∀ f : Ops, ¬ IsPure (⊥ : ε) f) (aligned : ReplyAligned L R s t) (hf : ∀ f : Ops, instrEff f ≤ e)
    (he : IsIterative e) :
    repairedDenoteInSyntax (⊥ : ε) (da.iter db) = repairedDenoteInSyntax (⊥ : ε) (da'.iter db') ↔
      L.run s = R.run t :=
  Proofs.packed_eq_iff_run_eq ha hb ha' hb' da db da' db' P visible aligned hf he

/-- Reflect equality of the actual native weak denotations into the repaired
packed model under reply alignment. -/
theorem packed_eq_iff_rendered_denote_eq {a a' : Tm Empty Ops 0} {b b' : Tm Empty Ops 1}
    (ha : (S.literal s).toLetIter 0 = some a) (hb : L.source.toLetIter 1 = some b)
    (ha' : (T.literal t).toLetIter 0 = some a') (hb' : R.source.toLetIter 1 = some b')
    (da : Derivation Ops Free .nil a S.ty) (db : Derivation Ops Free (.snoc .nil S.ty) b (Code.sum B S).ty)
    (da' : Derivation Ops Free .nil a' T.ty) (db' : Derivation Ops Free (.snoc .nil T.ty) b' (Code.sum B T).ty)
    (P : PureMaps (Φ := Ops) (ε := ε) carriers)
    (visible : ∀ f : Ops, ¬ IsPure (⊥ : ε) f) (aligned : ReplyAligned L R s t) (hf : ∀ f : Ops, instrEff f ≤ e)
    (he : IsIterative e) :
    repairedDenoteInSyntax (⊥ : ε) (da.iter db) = repairedDenoteInSyntax (⊥ : ε) (da'.iter db') ↔
      (da.iter db).denote D (instructions carriers P) γ ρ₀ =
      (da'.iter db').denote D (instructions carriers P) γ ρ₀ := by
  rw [loop_denote P visible L hf s ha hb da db, loop_denote P visible R hf t ha' hb' da' db']
  exact packed_eq_iff_run_eq ha hb ha' hb' da db da' db' P visible aligned hf he

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous
