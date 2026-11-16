module

public import Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Defs

@[expose] public section

namespace Silmaril.Logic.Smt.Uflia.SExpr.Renaming

open CategoryTheory Silmaril.Logic.Algebraic

variable {E F : Environment}

/-- An indexed typed symbol retains the output sort of its actual declaration. -/
theorem symbol_output {n : Nat} {inputs : Fin n → SortCode String}
    {output : SortCode String} (symbol : Symbol E n inputs output) :
    (E.declarations.get (symbolIndex symbol)).output = output := by
  cases symbol
  rfl

/-- Its declaration has the actual arity, not merely a coinciding name. -/
theorem symbol_arity {n : Nat} {inputs : Fin n → SortCode String}
    {output : SortCode String} (symbol : Symbol E n inputs output) :
    (E.declarations.get (symbolIndex symbol)).inputs.length = n := by
  cases symbol
  rfl

/-- Reconstruction uses heterogeneous equality because the declaration carries
its own arity and input family. It does not infer profiles from index equality. -/
theorem symbol_reconstruct {n : Nat} {inputs : Fin n → SortCode String}
    {output : SortCode String} (symbol : Symbol E n inputs output) :
    HEq (Symbol.declared (symbolIndex symbol)) symbol := by
  cases symbol
  rfl

/-- Dependent sort checking commutes with an actual abstract signature map. -/
theorem expect_mapPacked (f : E.signature ⟶ F.signature)
    (sort : SortCode String) (t : PackedTerm E) :
    (mapPacked f t).expect? sort = (t.expect? sort).map (Uflia.Term.map f) := by
  rcases t with ⟨s, t⟩
  by_cases h : s = sort
  · subst s
    simp [mapPacked, PackedTerm.expect?]
  · simp [mapPacked, PackedTerm.expect?, h]

/-- Mapping a nullary operation only needs extensionality on an empty domain. -/
theorem map_nullary (f : E.signature ⟶ F.signature)
    {inputs : Fin 0 → SortCode String} {sort : SortCode String}
    (op : Operation E.signature 0 inputs sort) :
    Uflia.Term.map f (.app op (fun i => Fin.elim0 i)) =
      .app (Operation.map f op) (fun i => Fin.elim0 i) := by
  change ManySorted.Term.app _ _ = ManySorted.Term.app _ _
  congr 1
  funext i
  exact Fin.elim0 i

/-- Mapping a homogeneous-input binary node preserves its explicit argument
order. Input and output sorts may differ, as in integer comparison. -/
theorem map_binary (f : E.signature ⟶ F.signature)
    {input output : SortCode String}
    (op : Operation E.signature 2 (fun _ => input) output)
    (a b : Uflia.Term E.signature input) :
    Uflia.Term.map f (.app op (Fin.cases a (fun _ => b))) =
      .app (Operation.map f op)
        (Fin.cases (Uflia.Term.map f a) (fun _ => Uflia.Term.map f b)) := by
  change ManySorted.Term.app _ _ = ManySorted.Term.app _ _
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i

/-- UF renaming does not change whether a typed term is a literal coefficient. -/
theorem integerValue_map (f : E.signature ⟶ F.signature)
    {sort : SortCode String} (t : Uflia.Term E.signature sort) :
    integerValue? (Uflia.Term.map f t) = integerValue? t := by
  induction t with
  | var i => exact Fin.elim0 i
  | app op args ih =>
      cases op <;> simp only [Uflia.Term.map, ManySorted.Term.map,
        Signature.expandMap, Operation.map, integerValue?]
      case integer n =>
        have h : args = (fun i => Fin.elim0 i) := funext (fun i => Fin.elim0 i)
        rw [h]
        rfl
      case scale k => exact congrArg (Option.map (k * ·)) (ih 0)

/-- Name maps preserve the declaration actually selected by source lookup. -/
theorem lookup_globalName (f : NameMap E F) (name : String)
    (i : Fin E.declarations.length) (h : lookup? E name = some i) :
    lookup? F (globalName E f.rename name) =
      some (symbolIndex (f.abstract.operations (.declared i))) := by
  simpa [globalName, h] using f.lookup name i h

end Silmaril.Logic.Smt.Uflia.SExpr.Renaming
