module

public import Silmaril.Logic.ACL2.Books.Thms

@[expose] public section

namespace Silmaril.Logic.ACL2.Standard

/-- Escape case-sensitive Lisp symbol constituents. The host must already know the package. -/
def symbolPart (s : String) : String :=
  "|" ++ ((s.replace "\\" "\\\\").replace "|" "\\|") ++ "|"

def symbol (n : Name) : String := symbolPart n.package ++ "::" ++ symbolPart n.symbol

def variableName (i : Nat) : String := "SILMARIL-V" ++ toString i

def form (head : String) (args : List String) : String :=
  "(" ++ String.intercalate " " (head :: args) ++ ")"

/-- Render logical core terms in ACL2 syntax, using a fixed finite set of formal variable names. -/
def term {S : Signature} {n : Nat} : Term S n → String
  | .var i => variableName i.val
  | .app f args => form (symbol f.val) (List.ofFn fun i => term (args i))
  | .nil => "nil"
  | .truth => "t"
  | .cons x y => form "cons" [term x, term y]
  | .car x => form "car" [term x]
  | .cdr x => form "cdr" [term x]
  | .consp x => form "consp" [term x]
  | .equal x y => form "equal" [term x, term y]
  | .ite x y z => form "if" [term x, term y, term z]

/-- Emit a standard logical event. The host ACL2 prover may use its own proof search for defthm. -/
def event {W V : World} : Event W V → String
  | .defun (name := name) _ (n := n) body =>
    form "defun" [symbol name, "(" ++ String.intercalate " " (List.ofFn (n := n)
      fun i => variableName i.val) ++ ")", "(declare (xargs :mode :logic))", term body]
  | .defthm (name := name) _ p _ =>
    form "defthm" [symbol name, term p.term, ":rule-classes", "nil"]

def events {W V : World} : Book W V → List String
  | .nil _ => []
  | .cons e rest => event e :: events rest

/-- Text for a logical ACL2 book. Package setup and certification belong to the host world. -/
def source {W V : World} (b : Book W V) : String :=
  "(in-package \"ACL2\")\n\n" ++ String.intercalate "\n\n" (events b) ++ "\n"

/-- Adapter obligations for an external ACL2. The relations record successful standard
admissions and includes. The interpretation exposes the logical, total functions on ACL2 values. -/
structure Interface where
  HostWorld : Type
  admit : HostWorld → String → HostWorld → Prop
  /-- A successful include whose logical event trace is the given list of rendered events. -/
  includeBook : HostWorld → String → List String → HostWorld → Prop
  primitives : Primitives
  arity : HostWorld → Name → Option Nat
  call : HostWorld → Name → (n : Nat) → (Fin n → primitives.Value) → primitives.Value
  theoremRecorded : HostWorld → Name → String → Prop

def Interface.model (A : Interface) (host : A.HostWorld) (S : Signature) : Model S :=
  ⟨A.primitives, fun {n} f => A.call host f.val n⟩

/-- The correspondence is a caller obligation. Names in the fragment have the declared arities,
the host realizes the named defining equations, and the host records the named statements. -/
structure Realizes (A : Interface) (host : A.HostWorld) (W : World) : Prop where
  arity : ∀ f n, W.signature.arity f = some n → A.arity host f = some n
  definitions : W.presentation.Models (A.model host W.signature)
  theorems : ∀ f p, W.theoremAt f = some p → A.theoremRecorded host f (term p.term)

/-- An external replay relates a checked fragment book to observed ACL2 admissions.
The checked core proof and the host's acceptance are independent evidence. -/
inductive Replay (A : Interface) : {W V : World} → Book W V → A.HostWorld → A.HostWorld → Prop
  | nil (W : World) (host : A.HostWorld) : Replay A (.nil W) host host
  | cons {W V U : World} {e : Event W V} {rest : Book V U} {start middle finish : A.HostWorld} :
      A.admit start (event e) middle → Replay A rest middle finish →
      Replay A (.cons e rest) start finish

/-- Associate the native include result with the event trace for the same certified source.
The interface provider supplies both observations. -/
structure Included (A : Interface) {W V : World} (b : Book W V) (path : String)
    (start finish : A.HostWorld) : Prop where
  certifiedSource : A.includeBook start path (events b) finish
  replay : Replay A b start finish

end Silmaril.Logic.ACL2.Standard
