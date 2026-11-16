module

public import Silmaril.Logic.CommonLogic.Source.Thms
public import Mathlib.Data.List.Nodup

/-! Simultaneous spelling renaming of declarations, occurrences and both binder
classes. A spelling permutation preserves first-match lookup and shadowing. This
is an operation on the raw AST, not a claim about byte-level CLIF rewriting. -/
@[expose] public section
namespace Silmaril.Logic.CommonLogic.Source

/-- Rename spelling keys while retaining the original semantic symbols. -/
def Names.rename {S : Core.Signature} (names : Names S) (r : Equiv.Perm String) : Names S where
  discourse := names.discourse.map (fun p => (r p.1, p.2))
  nondiscourse := names.nondiscourse.map (fun p => (r p.1, p.2))
  marker := names.marker.map (fun p => (r p.1, p.2))

def Expr.rename (r : Equiv.Perm String) : {a : Core.Kind} → Expr a → Expr a
  | _, .individual x => .individual (r x)
  | _, .reference x => .reference (r x)
  | _, .sequence x => .sequence (r x)
  | _, .lift t => .lift (t.rename r)
  | _, .app h args => .app (h.rename r) (args.rename r)
  | _, .nil => .nil
  | _, .cons t ts => .cons (t.rename r) (ts.rename r)
  | _, .append xs ys => .append (xs.rename r) (ys.rename r)

def Formula.rename (r : Equiv.Perm String) : Formula → Formula
  | .equal t u => .equal (t.rename r) (u.rename r)
  | .pred h args => .pred (h.rename r) (args.rename r)
  | .tt => .tt
  | .ff => .ff
  | .neg p => .neg (p.rename r)
  | .conj p q => .conj (p.rename r) (q.rename r)
  | .disj p q => .disj (p.rename r) (q.rename r)
  | .impl p q => .impl (p.rename r) (q.rename r)
  | .iff p q => .iff (p.rename r) (q.rename r)
  | .all x p => .all (r x) (p.rename r)
  | .ex x p => .ex (r x) (p.rename r)
  | .allSeq x p => .allSeq (r x) (p.rename r)
  | .exSeq x p => .exSeq (r x) (p.rename r)

/-- Move an environment along the spelling permutation. -/
def renameEnv {α : Type} (r : Equiv.Perm String) (ρ : String → Option α) :
    String → Option α := fun x => ρ (r.symm x)

end Silmaril.Logic.CommonLogic.Source
