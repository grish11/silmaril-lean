module

import Silmaril.Logic.ACL2.Recursive.Thms
import Mathlib.Data.Fin.VecNotation

namespace Silmaril.Logic.ACL2.Recursive.Tests

-- A small carrier for executable regressions. The checker itself uses only Primitives and CdrSize.
inductive Tree where
  | nil | truth | other
  | cons (car cdr : Tree)
  deriving DecidableEq, Repr

def treeCar : Tree → Tree
  | .cons x _ => x
  | _ => .nil

def treeCdr : Tree → Tree
  | .cons _ y => y
  | _ => .nil

def treeConsp : Tree → Bool
  | .cons .. => true
  | _ => false

def primitives : Primitives where
  Value := Tree
  nil := .nil
  truth := .truth
  cons := .cons
  car := treeCar
  cdr := treeCdr
  consp := treeConsp
  truth_ne_nil := by decide
  consp_nil := rfl
  consp_truth := rfl
  consp_cons _ _ := rfl
  car_cons _ _ := rfl
  cdr_cons _ _ := rfl
  car_atom x h := by cases x <;> simp_all [treeCar, treeConsp]
  cdr_atom x h := by cases x <;> simp_all [treeCdr, treeConsp]

def spine : Tree → Nat
  | .cons _ y => spine y + 1
  | _ => 0

def cdrSize : CdrSize primitives where
  size := spine
  cdr_lt x h := by cases x <;> simp_all [primitives, treeConsp, treeCdr, spine]

def emptyModel (P : Primitives) : Model Signature.empty :=
  ⟨P, fun f => nomatch f.property⟩

def singleton (name : Name) (arity : Nat) : Signature := Signature.empty.add name arity

theorem singleton_arity {name : Name} {arity k : Nat} (f : (singleton name arity).Symbol k) :
    k = arity := by
  have declared := f.property
  by_cases hf : f.val = name <;> simp_all [singleton, Signature.add, Signature.empty]

def singletonBlock (S : Signature) (name : Name) (arity : Nat) (fresh : S.arity name = none)
    (body : Body S (singleton name arity) arity) : Block S where
  members := singleton name arity
  fresh := by
    intro candidate k declared
    by_cases hf : candidate = name <;> simp_all [singleton, Signature.add, Signature.empty]
  body f := singleton_arity f ▸ body

def firstArg {name : Name} {arity : Nat} (positive : 0 < arity) :
    MeasureArgument (singleton name arity) :=
  fun f => ⟨0, singleton_arity f ▸ positive⟩

def listName : Name := ⟨"ACL2", "TRUE-LISTP"⟩
def appendName : Name := ⟨"ACL2", "BINARY-APPEND"⟩

def listSymbol : (singleton listName 1).Symbol 1 := Signature.empty.addSymbol listName 1
def appendSymbol : (singleton appendName 2).Symbol 2 := Signature.empty.addSymbol appendName 2

-- ACL2 8.7 axioms.lisp. EQ expands via its logical EQUAL equation.
def listBlock : Block Signature.empty :=
  singletonBlock _ listName 1 rfl
    (.ite (.consp (.var 0)) (.call listSymbol ![.cdr (.var 0)]) (.base (.equal (.var 0) .nil)))

-- COND uses ENDP, which is ATOM in the logic. Swap the branches to test CONSP directly.
def appendBlock : Block listBlock.signature :=
  singletonBlock _ appendName 2 rfl
    (.ite (.consp (.var 0))
      (.apply (.cons (.var 0) (.var 1))
        ![.base (.car (.var 0)), .call appendSymbol ![.cdr (.var 0), .var 1]])
      (.base (.var 1)))

def listCert : BlockCertificate listBlock := fun _ => .ite (.cdr 0) .base
def appendCert : BlockCertificate appendBlock := fun _ => .ite (.apply [.base, .cdr 0]) .base

theorem listAccepted : listCert.Accepted listBlock (firstArg (by decide)) := by
  intro k f
  have hk := singleton_arity f
  subst k
  rfl

theorem appendAccepted : appendCert.Accepted appendBlock (firstArg (by decide)) := by
  intro k f
  have hk := singleton_arity f
  subst k
  rfl

theorem listDone {P : Primitives} (size : CdrSize P) :
    listBlock.Terminates (emptyModel P) (size.rank (firstArg (by decide))) :=
  listCert.terminates _ _ listAccepted

def listModel {P : Primitives} (size : CdrSize P) := listBlock.model _ _ (listDone size)

theorem appendDone {P : Primitives} (size : CdrSize P) :
    appendBlock.Terminates (listModel size) (size.rank (firstArg (by decide))) :=
  appendCert.terminates _ _ appendAccepted

def appendModel {P : Primitives} (size : CdrSize P) := appendBlock.model _ _ (appendDone size)

def isList {P : Primitives} (size : CdrSize P) (x : P.Value) : P.Value :=
  (listModel size).interpret (listBlock.symbol listSymbol) ![x]

def append {P : Primitives} (size : CdrSize P) (x y : P.Value) : P.Value :=
  (appendModel size).interpret (appendBlock.symbol appendSymbol) ![x, y]

theorem mapVec1 {A B : Type} (f : A → B) (x : A) :
    (fun i => f (![x] i)) = ![f x] :=
  funext (Fin.forall_fin_one.2 rfl)

theorem mapVec2 {A B : Type} (f : A → B) (x y : A) :
    (fun i => f (![x, y] i)) = ![f x, f y] :=
  funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)

theorem listEquation {P : Primitives} (size : CdrSize P) (x : P.Value) :
    isList size x = if P.consp x then isList size (P.cdr x) else P.equal x P.nil := by
  have h := (Sentence.holds_eq _ _ _).1 (listBlock.equation_holds (listDone size) listSymbol) ![x]
  simp only [listBlock, singletonBlock, Body.toTerm, Term.eval, Term.map, mapVec1] at h
  change isList size x = P.ite (P.ofBool (P.consp x)) (isList size (P.cdr x)) (P.equal x P.nil) at h
  cases hc : P.consp x <;> simpa [hc, Primitives.ite, Primitives.ofBool, P.truth_ne_nil] using h

theorem appendEquation {P : Primitives} (size : CdrSize P) (x y : P.Value) :
    append size x y = if P.consp x then P.cons (P.car x) (append size (P.cdr x) y) else y := by
  have h :=
    (Sentence.holds_eq _ _ _).1 (appendBlock.equation_holds (appendDone size) appendSymbol) ![x, y]
  simp only [appendBlock, singletonBlock, Body.toTerm, Term.subst, Term.eval, Term.map,
    mapVec2, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  change append size x y =
    P.ite (P.ofBool (P.consp x)) (P.cons (P.car x) (append size (P.cdr x) y)) y at h
  cases hc : P.consp x <;> simpa [hc, Primitives.ite, Primitives.ofBool, P.truth_ne_nil] using h

def appendCall {P : Primitives} (x y : P.Value) : Call appendBlock.members P.Value :=
  ⟨2, appendSymbol, ![x, y]⟩

-- The induction hypotheses come from the admitted body. The two branch arguments below
-- reconstruct the theorem in Lean using the ACL2 CONS-CAR-CDR law supplied by the carrier.
theorem appendToNil {P : Primitives} (size : CdrSize P)
    (reconstruct : ∀ x, P.consp x = true → P.cons (P.car x) (P.cdr x) = x)
    (x : P.Value) (hx : isList size x ≠ P.nil) : append size x P.nil = x := by
  let property (state : Call appendBlock.members P.Value) :=
    ∀ x, state = appendCall x P.nil → isList size x ≠ P.nil → append size x P.nil = x
  apply appendBlock.callInduction (appendDone size) property _ (appendCall x P.nil) x rfl hx
  intro state ih x hs hl
  subst state
  rw [appendEquation]
  rw [listEquation] at hl
  cases hc : P.consp x with
  | true =>
    have branch : P.ofBool (P.consp x) ≠ P.nil := by
      simpa [hc, Primitives.ofBool] using P.truth_ne_nil
    have calls := ih.1 branch
    have smaller := calls 1
    change property (Call.ofTerms (listModel size) (appendCall x P.nil).args appendSymbol
      ![.cdr (.var (0 : Fin 2)), .var (1 : Fin 2)]) at smaller
    have same : Call.ofTerms (listModel size) (appendCall x P.nil).args appendSymbol
        ![.cdr (.var (0 : Fin 2)), .var (1 : Fin 2)] = appendCall (P.cdr x) P.nil := by
      exact congrArg (fun args : Fin 2 → P.Value => Call.mk 2 appendSymbol args)
        (funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩))
    have ih' := Eq.mp (congrArg property same) smaller
    have hl' : isList size (P.cdr x) ≠ P.nil := by simpa only [hc, ite_true] using hl
    simp only [ite_true, ih' _ rfl hl', reconstruct x hc]
  | false =>
    have hnil : x = P.nil := by
      by_contra h
      simp [hc, Primitives.equal, Primitives.ofBool, h] at hl
    simp [hnil]

def appendToNilStatement : Sentence appendBlock.signature :=
  let x : Term appendBlock.signature 1 := .var 0
  ⟨1, (Term.app (appendBlock.inclusion.symbol (listBlock.symbol listSymbol)) ![x]).implies
    (.equal (.app (appendBlock.symbol appendSymbol) ![x, .nil]) x)⟩

theorem appendToNilHolds {P : Primitives} (size : CdrSize P)
    (reconstruct : ∀ x, P.consp x = true → P.cons (P.car x) (P.cdr x) = x) :
    appendToNilStatement.Holds (appendModel size) := by
  intro env
  change Env (appendModel size) 1 at env
  have old := appendBlock.eval_map (appendDone size) env (.app (listBlock.symbol listSymbol) ![.var 0])
  simp only [Term.map, Term.eval, mapVec1] at old
  change (appendModel size).interpret (appendBlock.inclusion.symbol (listBlock.symbol listSymbol))
    ![env 0] = isList size (env 0) at old
  simp only [appendToNilStatement, Term.implies, Term.eval, mapVec1, mapVec2]
  change P.ite ((appendModel size).interpret
    (appendBlock.inclusion.symbol (listBlock.symbol listSymbol)) ![env 0])
    (P.ite (P.equal (append size (env 0) P.nil) (env 0)) P.truth P.nil) P.truth ≠ P.nil
  rw [old]
  by_cases hl : isList size (env 0) = P.nil
  · simpa [Primitives.ite, hl] using P.truth_ne_nil
  · have he := appendToNil size reconstruct (env 0) hl
    have self (a : P.Value) : P.equal a a = P.truth := by
      simp [Primitives.equal, Primitives.ofBool]
    rw (config := { transparency := .default }) [he, self]
    simp [Primitives.ite, hl, P.truth_ne_nil]

example : append cdrSize (.cons .truth .other) .other = Tree.cons .truth .other := by
  rw (config := { transparency := .default }) [appendEquation]
  change Tree.cons .truth (append cdrSize .other .other) = Tree.cons .truth .other
  rw (config := { transparency := .default }) [appendEquation]
  rfl
example : append cdrSize (.cons .truth .other) .nil = Tree.cons .truth .nil := by
  rw (config := { transparency := .default }) [appendEquation]
  change Tree.cons .truth (append cdrSize .other .nil) = Tree.cons .truth .nil
  rw (config := { transparency := .default }) [appendEquation]
  rfl
example : isList cdrSize (.cons .truth .other) = Tree.nil := by
  rw (config := { transparency := .default }) [listEquation]
  change isList cdrSize .other = Tree.nil
  rw (config := { transparency := .default }) [listEquation]
  rfl

-- Mutate independent pieces of the checked body and certificate.
def checkAppend (body : Body listBlock.signature appendBlock.members 2)
    (cert : Certificate) : Bool :=
  cert.check (firstArg (by decide)) 0 [] body

example : checkAppend (appendBlock.body appendSymbol) (.ite (.apply [.base, .cdr 1]) .base)
    = false := rfl

example : checkAppend (appendBlock.body appendSymbol) (.ite (.apply [.base]) .base)
    = false := rfl

example : checkAppend (appendBlock.body appendSymbol) (.ite (.apply [.base, .base]) .base)
    = false := rfl

example : checkAppend (.ite (.consp (.var 0)) (.base (.var 1))
    (.call appendSymbol ![.cdr (.var 0), .var 1])) (.ite .base (.cdr 0)) = false := rfl

example : checkAppend (.ite (.consp (.var 0))
    (.call appendSymbol ![.var 0, .var 1]) (.base (.var 1))) (.ite (.cdr 0) .base) = false := rfl

example : checkAppend (.ite (.consp (.var 1))
    (.call appendSymbol ![.cdr (.var 0), .var 1]) (.base (.var 1))) (.ite (.cdr 0) .base) = false := rfl

-- The two members select different argument positions and call each other.
def leftName : Name := ⟨"ACL2", "SILMARIL-LEFT"⟩
def rightName : Name := ⟨"ACL2", "SILMARIL-RIGHT"⟩

def alternators : Signature := (singleton leftName 1).add rightName 2

def leftSymbol : alternators.Symbol 1 := ⟨leftName, rfl⟩
def rightSymbol : alternators.Symbol 2 := ⟨rightName, rfl⟩

theorem alternator_arity {k : Nat} (f : alternators.Symbol k) :
    if f.val = rightName then k = 2 else k = 1 := by
  have declared := f.property
  by_cases hr : f.val = rightName
  · simpa [alternators, Signature.add, hr] using declared.symm
  · by_cases hl : f.val = leftName
    · simpa [alternators, singleton, Signature.add, hr, hl, show leftName ≠ rightName from by decide]
        using declared.symm
    · simp [alternators, singleton, Signature.add, Signature.empty, hr, hl] at declared

def leftBody : Body Signature.empty alternators 1 :=
  .ite (.consp (.var 0)) (.call rightSymbol ![.nil, .cdr (.var 0)]) (.base .truth)

def rightBody : Body Signature.empty alternators 2 :=
  .ite (.consp (.var 1))
    (.ite (.var 0) (.base .nil) (.call leftSymbol ![.cdr (.var 1)])) (.base .nil)

def alternatorBlock : Block Signature.empty where
  members := alternators
  fresh := fun _ => rfl
  body f :=
    if hr : f.val = rightName then
      (ite_eq_left hr ▸ alternator_arity f) ▸ rightBody
    else (ite_eq_right hr ▸ alternator_arity f) ▸ leftBody

def alternatorArg : MeasureArgument alternators := fun f =>
  if hr : f.val = rightName then
    (ite_eq_left hr ▸ alternator_arity f) ▸ (1 : Fin 2)
  else (ite_eq_right hr ▸ alternator_arity f) ▸ (0 : Fin 1)

def leftCert : Certificate := .ite (.cdr 0) .base
def rightCert : Certificate := .ite (.ite .base (.cdr 1)) .base

def alternatorCert : BlockCertificate alternatorBlock := fun f =>
  if f.val = rightName then rightCert else leftCert

theorem alternatorAccepted : alternatorCert.Accepted alternatorBlock alternatorArg := by
  intro k f
  by_cases hr : f.val = rightName
  · have hk : k = 2 := by simpa only [hr, ite_true] using alternator_arity f
    subst k
    unfold alternatorCert alternatorBlock alternatorArg
    split <;> simp_all [rightCert]
    rfl
  · have hk : k = 1 := by simpa only [hr, ite_false] using alternator_arity f
    subst k
    unfold alternatorCert alternatorBlock alternatorArg
    split <;> simp_all [leftCert]
    rfl

theorem alternatorDone :
    alternatorBlock.Terminates (emptyModel primitives) (cdrSize.rank alternatorArg) :=
  alternatorCert.terminates _ _ alternatorAccepted

def leftCall (x : Tree) : Call alternatorBlock.members Tree := ⟨1, leftSymbol, ![x]⟩
def rightCall (token x : Tree) : Call alternatorBlock.members Tree := ⟨2, rightSymbol, ![token, x]⟩

def alternate := alternatorBlock.interpret _ _ alternatorDone

theorem leftCons (x y : Tree) :
    alternate (leftCall (.cons x y)) = alternate (rightCall .nil y) := by
  unfold alternate
  rw [alternatorBlock.interpret_unfold alternatorDone (leftCall (.cons x y))]
  apply congrArg (alternatorBlock.interpret _ _ alternatorDone)
  exact congrArg (fun args : Fin 2 → Tree => Call.mk 2 rightSymbol args)
    (funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩))

theorem rightCons (x y : Tree) :
    alternate (rightCall .nil (.cons x y)) = alternate (leftCall y) := by
  unfold alternate
  rw [alternatorBlock.interpret_unfold alternatorDone (rightCall .nil (.cons x y))]
  apply congrArg (alternatorBlock.interpret _ _ alternatorDone)
  exact congrArg (fun args : Fin 1 → Tree => Call.mk 1 leftSymbol args)
    (funext (Fin.forall_fin_one.2 rfl))

example : alternate (leftCall (.cons .truth (.cons .truth .nil))) = Tree.truth := by
  rw [leftCons, rightCons]
  exact alternatorBlock.interpret_unfold alternatorDone (leftCall .nil)

example : alternate (rightCall .nil (.cons .truth .nil)) = Tree.truth := by
  rw [rightCons]
  exact alternatorBlock.interpret_unfold alternatorDone (leftCall .nil)

example : (.ite (.ite .base (.cdr 0)) .base : Certificate).check alternatorArg 1 [] rightBody =
    false := rfl

example : leftCert.check alternatorArg (0 : Fin 1) ([] : Path Signature.empty 1)
    (.ite (.consp (.var 0)) (.call rightSymbol ![.cdr (.var 0), .nil]) (.base .truth)) =
    false := rfl

#print axioms Block.interpret
#print axioms Block.equation_holds
#print axioms Block.callInduction
#print axioms BlockCertificate.terminates
#print axioms appendToNilHolds

end Silmaril.Logic.ACL2.Recursive.Tests
