module

public import Silmaril.Logic.STLCMatching.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.STLCMatching
open Silmaril.Calculi.TypedLambda Silmaril.Calculi.LambdaCube
open Cslib.LambdaCalculus.LocallyNameless.Stlc

def appInputs {B : Type} (a b : Ty B) : Fin 2 → Ty B :=
  Fin.cases (.arrow a b) (Fin.cases a Fin.elim0)

inductive Operation (S : Signature) : (n : Nat) → (Fin n → Ty S.Base) → Ty S.Base → Type where
  | primitive {τ} (p : Primitive S τ) : Operation S 0 Fin.elim0 τ
  | app (a b) : Operation S 2 (appInputs a b) b

abbrev nativeSignature (S : Signature) : Matching.SortMaps.Signature :=
  ⟨Ty S.Base, ⟨Operation S⟩⟩

theorem carrier_nonempty {S : Signature} (M : Model S) (a : Ty S.Base) :
    Nonempty (STLC.carrier M.toSetModel.base a) := by
  induction a with
  | base b => exact M.nonempty b
  | arrow a b _ ih => exact ⟨fun _ => Classical.choice ih⟩

/-- Independent native algebra: every primitive and application is singleton-valued. -/
def nativeModel {S : Signature} (M : Model S) :
    Matching.FirstOrder.Model (nativeSignature S).symbols where
  carrier := STLC.carrier M.toSetModel.base
  nonempty := carrier_nonempty M
  operation := fun op args => match op with
    | .primitive p => {p.eval M.toSetModel}
    | .app _ _ => {(args 0) (args 1)}

def nativeApp {S : Signature} {k : Nat} {Γ : Fin k → Ty S.Base} {a b}
    (f : Matching.FirstOrder.Pattern (nativeSignature S).symbols Γ (.arrow a b))
    (x : Matching.FirstOrder.Pattern (nativeSignature S).symbols Γ a) :
    Matching.FirstOrder.Pattern (nativeSignature S).symbols Γ b :=
  .app (.app a b) (Fin.cases f (Fin.cases x (fun i => i.elim0)))

def Comb.pattern {S : Signature} {Γ : Ctx S.Base} {k : Nat}
    {Δ : Fin k → Ty S.Base}
    (vars : Tuple (Matching.FirstOrder.Pattern (nativeSignature S).symbols Δ) Γ) :
    {τ : Ty S.Base} → Comb S Γ τ →
      Matching.FirstOrder.Pattern (nativeSignature S).symbols Δ τ
  | _, .var v => vars _ v
  | _, .primitive p => .app (.primitive p) (fun i => i.elim0)
  | _, .app f a => nativeApp (f.pattern vars) (a.pattern vars)

theorem denote_nativeApp {S : Signature} (M : Model S) {k : Nat}
    {Γ : Fin k → Ty S.Base} (ρ : ∀ i, (nativeModel M).carrier (Γ i)) {a b}
    (f : Matching.FirstOrder.Pattern (nativeSignature S).symbols Γ (.arrow a b))
    (x : Matching.FirstOrder.Pattern (nativeSignature S).symbols Γ a)
    (fv : STLC.carrier M.toSetModel.base (.arrow a b))
    (xv : STLC.carrier M.toSetModel.base a)
    (hf : (nativeModel M).denote ρ f = {fv})
    (hx : (nativeModel M).denote ρ x = {xv}) :
    (nativeModel M).denote ρ (nativeApp f x) = {fv xv} := by
  apply Set.Subset.antisymm
  · show (nativeModel M).denote ρ (nativeApp f x) ⊆ {fv xv}
    intro result hr
    simp only [nativeApp, Matching.FirstOrder.Model.denote] at hr
    obtain ⟨values, member, output⟩ := hr
    have h0 : values 0 = fv := by
      have member0 : values 0 ∈ (nativeModel M).denote ρ f := member 0
      rw [hf] at member0
      exact member0
    have h1 : values 1 = xv := by
      have member1 : values 1 ∈ (nativeModel M).denote ρ x := member 1
      rw [hx] at member1
      exact member1
    have result_value : result = values 0 (values 1) := output
    change result = fv xv
    exact result_value.trans (congrArg₂ (fun g y => g y) h0 h1)
  · show {fv xv} ⊆ (nativeModel M).denote ρ (nativeApp f x)
    intro result hr
    simp only [nativeApp, Matching.FirstOrder.Model.denote]
    have function_member : fv ∈ (nativeModel M).denote ρ f := by rw [hf]; rfl
    have argument_member : xv ∈ (nativeModel M).denote ρ x := by rw [hx]; rfl
    refine ⟨Fin.cases fv (Fin.cases xv (fun i => i.elim0)), ?_, ?_⟩
    · intro i
      exact Fin.cases function_member
        (fun j => Fin.cases argument_member (fun z => z.elim0) j) i
    · change result = fv xv
      exact hr

theorem Comb.denote_pattern {S : Signature} (M : Model S) {Γ : Ctx S.Base}
    {k : Nat} {Δ : Fin k → Ty S.Base}
    (vars : Tuple (Matching.FirstOrder.Pattern (nativeSignature S).symbols Δ) Γ)
    (ρ : ∀ i, (nativeModel M).carrier (Δ i))
    (env : Tuple (STLC.carrier M.toSetModel.base) Γ)
    (hvars : ∀ a (v : Var Γ a), (nativeModel M).denote ρ (vars _ v) = {env _ v})
    {τ : Ty S.Base} (t : Comb S Γ τ) :
    (nativeModel M).denote ρ (t.pattern vars) = {t.eval M.toSetModel env} := by
  induction t with
  | var v => simpa [Comb.pattern, Comb.eval] using hvars _ v
  | primitive p =>
      simp only [Comb.pattern, Comb.eval, Matching.FirstOrder.Model.denote]
      ext result
      constructor
      · rintro ⟨_, _, hr⟩
        exact hr
      · intro hr
        exact ⟨(fun i => i.elim0), fun i => i.elim0, hr⟩
  | app f a ihf iha =>
      simpa [Comb.pattern, Comb.eval] using denote_nativeApp M ρ _ _ _ _ ihf iha

def nativeVars {S : Signature} (Γ : Ctx S.Base) :
    Tuple (Matching.FirstOrder.Pattern (nativeSignature S).symbols Γ.get) Γ :=
  Tuple.ofFn (fun i => .var i)

theorem denote_nativeVars {S : Signature} (M : Model S) (Γ : Ctx S.Base)
    (ρ : ∀ i, (nativeModel M).carrier (Γ.get i)) :
    ∀ a (v : Var Γ a), (nativeModel M).denote ρ (nativeVars Γ _ v) =
      {Tuple.ofFn ρ _ v} := by
  have h : (fun a v => (nativeModel M).denote ρ (nativeVars Γ a v)) =
      (fun a v => ({Tuple.ofFn ρ a v} : Set ((nativeModel M).carrier a))) := by
    apply (Tuple.equivFn Γ).injective
    funext i
    dsimp only [Tuple.equivFn, nativeVars]
    change (nativeModel M).denote ρ (Tuple.ofFn (fun i =>
      (Matching.FirstOrder.Pattern.var i : Matching.FirstOrder.Pattern
        (nativeSignature S).symbols Γ.get (Γ.get i))) _ (Var.ofFin i)) =
      {Tuple.ofFn ρ _ (Var.ofFin i)}
    rw [Tuple.ofFn_ofFin, Tuple.ofFn_ofFin]
    rfl
  intro a v
  exact congrFun (congrFun h a) v

def termPattern {S : Signature} {Γ : Ctx S.Base} {τ : Ty S.Base}
    (t : Term S Γ τ) : Matching.FirstOrder.Pattern (nativeSignature S).symbols Γ.get τ :=
  (compile t).pattern (nativeVars Γ)

theorem denote_termPattern {S : Signature} (M : Model S)
    {Γ : Ctx S.Base} {τ : Ty S.Base} (t : Term S Γ τ)
    (ρ : ∀ i, (nativeModel M).carrier (Γ.get i)) :
    (nativeModel M).denote ρ (termPattern t) =
      {STLC.eval M.toSetModel t (Tuple.ofFn ρ)} := by
  exact (Comb.denote_pattern M _ ρ (Tuple.ofFn ρ) (denote_nativeVars M Γ ρ) _).trans
    (congrArg (fun x : STLC.carrier M.toSetModel.base τ => ({x} : Set _))
      (eval_compile M.toSetModel t _))

/-- Boolean equivalence as an actual native pattern. -/
def equivalent {S : Signature} {k : Nat} {Γ : Fin k → Ty S.Base} {τ}
    (p q : Matching.FirstOrder.Pattern (nativeSignature S).symbols Γ τ) :=
  Matching.FirstOrder.Pattern.conj (.neg (.conj p (.neg q))) (.neg (.conj q (.neg p)))

theorem mem_equivalent {S : Signature} (M : Model S) {k : Nat}
    {Γ : Fin k → Ty S.Base} {τ} (ρ : ∀ i, (nativeModel M).carrier (Γ i))
    (p q : Matching.FirstOrder.Pattern (nativeSignature S).symbols Γ τ)
    (x : (nativeModel M).carrier τ) :
    x ∈ (nativeModel M).denote ρ (equivalent p q) ↔
      (x ∈ (nativeModel M).denote ρ p ↔ x ∈ (nativeModel M).denote ρ q) := by
  simp only [equivalent, Matching.FirstOrder.Model.denote, Set.mem_inter_iff,
    Set.mem_compl_iff]
  tauto

def equationSentence {S : Signature} {Γ : Ctx S.Base} {τ : Ty S.Base}
    (t u : Term S Γ τ) : Matching.FirstOrder.Sentence (nativeSignature S).symbols :=
  ⟨Γ.length, Γ.get, τ, equivalent (termPattern t) (termPattern u)⟩

theorem satisfies_equationSentence {S : Signature} (M : Model S)
    {Γ : Ctx S.Base} {τ : Ty S.Base} (t u : Term S Γ τ) :
    Matching.FirstOrder.Sentence.Satisfies (nativeModel M) (equationSentence t u) ↔
      STLC.Sat M.toSetModel (.equation t u) := by
  unfold Matching.FirstOrder.Sentence.Satisfies equationSentence STLC.Sat
  dsimp only
  constructor
  · intro h ρ
    have hv := (mem_equivalent M (fun i => ρ _ (Var.ofFin i))
      (termPattern t) (termPattern u) (STLC.eval M.toSetModel t ρ)).mp
        (h (fun i => ρ _ (Var.ofFin i)) (STLC.eval M.toSetModel t ρ))
    rw [denote_termPattern M t (fun i => ρ _ (Var.ofFin i)),
      denote_termPattern M u (fun i => ρ _ (Var.ofFin i)), Tuple.ofFn_eta] at hv
    exact hv.mp rfl
  · intro h ρ x
    apply (mem_equivalent M ρ _ _ x).mpr
    rw [denote_termPattern, denote_termPattern, h]

end Silmaril.Logic.STLCMatching
