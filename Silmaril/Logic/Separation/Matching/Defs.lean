module

public import Silmaril.Logic.Separation.Thms
public import Silmaril.Logic.Matching.FixedPoint

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Separation
open CategoryTheory Silmaril.Logic.Institution
variable {A B C : Signature}

inductive MatchingOperation (A : Signature) : (n : Nat) → (Fin n → Unit) → Unit → Type where
  | atom (a : A.Atom) : MatchingOperation A 0 (fun _ => ()) ()
  | emp : MatchingOperation A 0 (fun _ => ()) ()
  | join : MatchingOperation A 2 (fun _ => ()) ()
  | extension : MatchingOperation A 2 (fun _ => ()) ()

abbrev matchingSignature (A : Signature) : Algebraic.ManySorted.Signature Unit := ⟨MatchingOperation A⟩

def matchingMap (f : A ⟶ B) : matchingSignature A ⟶ matchingSignature B :=
  ⟨fun op => match op with
    | .atom a => .atom (f a)
    | .emp => .emp
    | .join => .join
    | .extension => .extension⟩

/-- No satisfaction evidence occurs here: native resource operations alone
supply the four interpretations. The resource unit supplies nonemptiness. -/
abbrev matchingModel (M : Model A) : Matching.FirstOrder.Model (matchingSignature A) where
  carrier _ := M.resource.carrier
  nonempty _ := ⟨M.resource.unit⟩
  operation op args := match op with
    | .atom a => M.atom a
    | .emp => {M.resource.unit}
    | .join => {h | M.resource.join (args 0) (args 1) h}
    | .extension => {h | M.resource.join h (args 0) (args 1)}

abbrev EmptyContext : Fin 0 → Unit := fun i => i.elim0
abbrev MatchingAssertion (A : Signature) := Matching.FirstOrder.Pattern (matchingSignature A) EmptyContext ()

def compileBase : Assertion A → MatchingAssertion A
  | .atom a => .app (.atom a) (fun i => i.elim0)
  | .emp => .app .emp (fun i => i.elim0)
  | .neg p => .neg (compileBase p)
  | .conj p q => .conj (compileBase p) (compileBase q)
  | .sep p q => .app .join (Fin.cases (compileBase p) (fun _ => compileBase q))
  | .wand p q => .neg (.app .extension (Fin.cases (compileBase p) (fun _ => .neg (compileBase q))))

abbrev MatchingPattern (A : Signature) (r : Nat) :=
  Matching.FixedPoint.Pattern (matchingSignature A) (fun _ : Fin r => ()) EmptyContext ()

def compilePattern {r} : Pattern A r → MatchingPattern A r
  | .base p => .base (compileBase p)
  | .var i => .setvar i
  | .conj p q => .conj (compilePattern p) (compilePattern q)
  | .disj p q => .disj (compilePattern p) (compilePattern q)
  | .sep p q => .app .join (Fin.cases (compilePattern p) (fun _ => compilePattern q))
  | .wand p q => .dualApp .extension
      (Fin.cases (.base (.neg (compileBase p))) (fun _ => compilePattern q))
  | .mu p => .mu (P' := fun _ => ()) (compilePattern p)

abbrev encode (p : Sentence A) : Matching.FixedPoint.Sentence (matchingSignature A) :=
  ⟨0, 0, (fun _ => ()), EmptyContext, (), .disj (compilePattern p.pre).dual (compilePattern p.post)⟩

end Silmaril.Logic.Separation
