module

public import Silmaril.Logic.Matching.SortMaps.Thms
public import Silmaril.Logic.Institution.Examples.FirstOrder

/-! An explicitly guarded matching presentation for possibly empty FOL sorts.
All interpretation conditions concern native operation graphs, never formula truth. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GuardedFOL
open CategoryTheory Silmaril.Logic.Institution.Examples

inductive MatchingSort (S : FOL.Signature) where
  | object : S.S → MatchingSort S
  | truth : MatchingSort S

inductive Operation (S : FOL.Signature) : (n : Nat) → (Fin n → MatchingSort S) → MatchingSort S → Type where
  | function {n inputs output} (op : S.Op n inputs output) :
      Operation S n (MatchingSort.object ∘ inputs) (.object output)
  | relation {n inputs} (rel : S.Rel n inputs) : Operation S n (MatchingSort.object ∘ inputs) .truth
  | active (s : S.S) : Operation S 0 (fun _ => .truth) (.object s)
  | defined (s : S.S) : Operation S 1 (fun _ => .object s) .truth
  | truth : Operation S 0 (fun _ => .truth) .truth

abbrev signature (S : FOL.Signature) : SortMaps.Signature := ⟨MatchingSort S, ⟨Operation S⟩⟩

def sortMap {S T : FOL.Signature} (f : S ⟶ T) : MatchingSort S → MatchingSort T
  | .object s => .object (f.sorts s)
  | .truth => .truth

def signatureMap {S T : FOL.Signature} (f : S ⟶ T) : signature S ⟶ signature T where
  sorts := sortMap f
  operations op := match op with
    | .function o => .function (f.ops o)
    | .relation r => .relation (f.rels r)
    | .active s => .active (f.sorts s)
    | .defined s => .defined (f.sorts s)
    | .truth => .truth

/-- Active carriers may be empty even though every raw carrier is inhabited. -/
abbrev Active {S : FOL.Signature} (M : FirstOrder.Model (signature S).symbols) (s : S.S) :=
  {x : M.carrier (.object s) // x ∈ M.operation (.active s) (fun i => i.elim0)}

/-- All restrictions concern raw operation graphs on active input tuples. -/
structure Model (S : FOL.Signature) where
  base : FirstOrder.Model (signature S).symbols
  function : ∀ {n inputs output} (op : S.Op n inputs output) (args : ∀ i, Active base (inputs i)),
    ∃ y : Active base output, base.operation (.function op) (fun i => (args i).val) = {y.val}
  relation : ∀ {n inputs} (r : S.Rel n inputs) args,
    base.operation (.relation r) args = ∅ ∨ base.operation (.relation r) args = Set.univ
  definedness : ∀ s args, base.operation (.defined s) args = Set.univ
  truth : ∀ args, base.operation .truth args = Set.univ

/-- Functions and relations are read from actual raw operation graphs. -/
abbrev decode {S : FOL.Signature} (M : Model S) : FOL.Structure S where
  carrier := Active M.base
  op op args := Classical.choose (M.function op args)
  rel r args := M.base.operation (.relation r) (fun i => (args i).val) = Set.univ


abbrev objContext {S : FOL.Signature} {k : Nat} (Γ : Fin k → S.S) : Fin k → MatchingSort S := MatchingSort.object ∘ Γ

def term {S : FOL.Signature} {k : Nat} {Γ : Fin k → S.S} {s : S.S} :
    EQ.Term S.toSignature Γ s → FirstOrder.Pattern (signature S).symbols (objContext Γ) (.object s)
  | .var i => .var i
  | .app op args => .app (.function op) (fun i => term (args i))

def top {S : FOL.Signature} {k : Nat} {Γ : Fin k → MatchingSort S} :
    FirstOrder.Pattern (signature S).symbols Γ .truth := .app .truth (fun i => i.elim0)

def defined {S : FOL.Signature} {k : Nat} {Γ : Fin k → MatchingSort S} {s : S.S}
    (p : FirstOrder.Pattern (signature S).symbols Γ (.object s)) :
    FirstOrder.Pattern (signature S).symbols Γ .truth := .app (.defined s) (fun _ => p)

def imp {S : FOL.Signature} {k : Nat} {Γ : Fin k → MatchingSort S}
    (p q : FirstOrder.Pattern (signature S).symbols Γ .truth) :
    FirstOrder.Pattern (signature S).symbols Γ .truth := .neg (.conj p (.neg q))

theorem context_extend {S : FOL.Signature} {k : Nat} {Γ : Fin k → S.S}
    {Δ : Fin (k+1) → S.S} (h : Δ ∘ Fin.succ = Γ) :
    objContext Δ = Fin.cases (.object (Δ 0)) (objContext Γ) := by
  funext i
  exact Fin.cases rfl (fun j => congrArg MatchingSort.object (congrFun h j)) i

abbrev activeGuard {S : FOL.Signature} {k : Nat} (Δ : Fin (k+1) → S.S) :
    FirstOrder.Pattern (signature S).symbols (objContext Δ) .truth :=
  defined (.conj (.var 0) (.app (.active (Δ 0)) (fun i => i.elim0)))

def allContext {S : FOL.Signature} {k : Nat} {Γ : Fin k → S.S}
    {Δ : Fin (k+1) → S.S} (h : Δ ∘ Fin.succ = Γ)
    (p : FirstOrder.Pattern (signature S).symbols (objContext Δ) .truth) :
    FirstOrder.Pattern (signature S).symbols (objContext Γ) .truth :=
  .neg (.ex (.object (Δ 0)) (.neg ((context_extend h) ▸ p)))

/-- Active-domain universal quantification: inactive raw values are ignored. -/
def formula {S : FOL.Signature} {k : Nat} {Γ : Fin k → S.S} :
    FOL.Formula S Γ → FirstOrder.Pattern (signature S).symbols (objContext Γ) .truth
  | .eq t u => defined (.conj (term t) (term u))
  | .rel r args => .app (.relation r) (fun i => term (args i))
  | .tt => top
  | .not p => .neg (formula p)
  | .and p q => .conj (formula p) (formula q)
  | .all h p => allContext h
      (imp (activeGuard _) (formula p))

end Silmaril.Logic.Matching.GuardedFOL
