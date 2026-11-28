module

public import Silmaril.Logic.ACL2.Recursive.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.ACL2.Recursive

open Silmaril.Logic.ACL2 Silmaril.Logic.ACL2.Recursive

variable {S R : Signature} {n : Nat}

private theorem reduct_interpret (B : Block S) (M : Model S) (rank : Rank M B.members)
    (h : B.Terminates M rank) :
    (fun {k} => @((B.model M rank h).reduct B.inclusion).interpret k) =
      (fun {k} => @M.interpret k) := by
  funext k f args
  have hf : B.members.arity f.val ≠ some k := by
    intro hm
    have declared := f.property
    simp [B.fresh hm] at declared
  simp [Model.reduct, Block.model, Signature.Hom.symbol, hf]

theorem model_reduct (B : Block S) (M : Model S) (rank : Rank M B.members)
    (h : B.Terminates M rank) : (B.model M rank h).reduct B.inclusion = M :=
  congrArg (Model.mk M.primitives) (reduct_interpret B M rank h)

theorem model_interpret (B : Block S) (M : Model S) (rank : Rank M B.members)
    (h : B.Terminates M rank) (state : Call B.members M.primitives.Value) :
    (B.model M rank h).interpret (B.symbol state.symbol) state.args =
      B.interpret M rank h state := by
  cases state with
  | mk k f args => simp [Block.model, Block.symbol, f.property]

theorem interpret_unfold (B : Block S) (M : Model S) (rank : Rank M B.members)
    (h : B.Terminates M rank) (state : Call B.members M.primitives.Value) :
    B.interpret M rank h state =
      (B.body state.symbol).eval M rank (rank state) state.args
        (fun next _ => B.interpret M rank h next) (h state) := by
  unfold Block.interpret
  rw [WellFounded.fix_eq]
  rfl

theorem eval_map (B : Block S) (M : Model S) (rank : Rank M B.members)
    (h : B.Terminates M rank) (env : Env M n) (term : Term S n) :
    (term.map B.inclusion).eval (B.model M rank h) env = term.eval M env := by
  refine (Term.eval_map B.inclusion (B.model M rank h) env term).trans ?_
  let evaluate (interp : ∀ {k : Nat}, S.Symbol k → Env M k → M.primitives.Value) :
      M.primitives.Value := term.eval (Model.mk M.primitives (fun {k} => @interp k)) env
  exact congrArg evaluate (reduct_interpret B M rank h)

theorem eval_toTerm (B : Block S) (M : Model S) (rank : Rank M B.members)
    (h : B.Terminates M rank) (caller : Nat) (env : Env M n)
    (body : Body S B.members n) (decreases : body.Decreases M rank caller env) :
    (body.toTerm B).eval (B.model M rank h) env =
      body.eval M rank caller env (fun next _ => B.interpret M rank h next) decreases := by
  induction body with
  | base term => simpa only [Body.toTerm, Body.eval] using eval_map B M rank h env term
  | call f args =>
    simp only [Body.toTerm, Body.eval, Term.eval, eval_map B M rank h]
    exact model_interpret B M rank h (Call.ofTerms M env f args)
  | apply context args ih =>
    rw (config := { transparency := .default })
      [Body.toTerm, Term.eval_subst, eval_map B M rank h]
    simp only [Body.eval]
    exact congrArg (fun values => context.eval M values) (funext fun i => ih i (decreases i))
  | ite test yes no ihy ihn =>
    simp only [Body.toTerm, Term.eval, Body.eval, Primitives.ite]
    rw (config := { transparency := .default }) [eval_map B M rank h env test]
    by_cases ht : test.eval M env = M.primitives.nil
    · simpa only [Block.model, ht, ite_true, dite_true] using ihn (decreases.2 ht)
    · simpa only [Block.model, ht, ite_false, dite_false] using ihy (decreases.1 ht)

theorem equation (B : Block S) (M : Model S) (rank : Rank M B.members)
    (h : B.Terminates M rank) {k : Nat} (f : B.members.Symbol k) :
    (B.equation f).Holds (B.model M rank h) := by
  apply (Sentence.holds_eq _ _ _).2
  intro env
  let state : Call B.members M.primitives.Value := ⟨k, f, env⟩
  change (B.model M rank h).interpret (B.symbol f) env =
    ((B.body f).toTerm B).eval (B.model M rank h) env
  rw [model_interpret B M rank h state, interpret_unfold B M rank h state]
  exact (eval_toTerm B M rank h (rank state) env (B.body f) (h state)).symm

theorem callsSatisfy_mono (M : Model S) (env : Env M n)
    {p q : Call R M.primitives.Value → Prop} (imp : ∀ state, p state → q state)
    (body : Body S R n) (h : body.CallsSatisfy M env p) : body.CallsSatisfy M env q := by
  induction body with
  | base => trivial
  | call => exact imp _ h
  | apply _ _ ih => exact fun i => ih i (h i)
  | ite _ _ _ ihy ihn => exact ⟨fun ht => ihy (h.1 ht), fun ht => ihn (h.2 ht)⟩

theorem callInduction (B : Block S) (M : Model S) (rank : Rank M B.members)
    (h : B.Terminates M rank) (p : Call B.members M.primitives.Value → Prop)
    (step : ∀ state, (B.body state.symbol).CallsSatisfy M state.args p → p state) :
    ∀ state, p state := by
  intro state
  induction state using (measure rank).wf.induction with
  | h state ih => exact step state (callsSatisfy_mono M state.args ih _ (h state))

end Silmaril.Proofs.Logic.ACL2.Recursive
