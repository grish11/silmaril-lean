module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Institution.Thms

/-! A syntactic forward simulation of named packet CFGs. A private address
may be mapped to a private address or a public port. Copying matches the
whole labelled body after renaming. Skipping is allowed for a jump that
forwards its parameter unchanged and stays at the same mapped address. -/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link

variable {V F : Type} [DecidableEq V] {a b n : Nat}

/-- A graph made entirely of direct port-to-port wires. -/
def Graph.wiring (wire : Fin a → Fin b) : Graph V F a b where
  locals := 0
  entry := Sum.inr ∘ wire
  block := Fin.elim0
  closed i := Fin.elim0 i

/-- The two local syntactic simulation rules. -/
inductive BlockMatch (right : Graph V F a b) (route : Label n b → Label right.locals b)
    (source : Block V (Label n b) F) (image : Label right.locals b) : Prop
  | copy (target : Fin right.locals) (address : image = .inl target)
      (body : source.relabel route = right.block target) : BlockMatch right route source image
  | forward (target : Label n b)
      (body : source.body = .term (.br target (.var source.param)))
      (address : image = route target) : BlockMatch right route source image

/-- The certificate maps private labels and leaves public exits unchanged. -/
structure Simulation (left right : Graph V F a b) where
  address : Fin left.locals → Label right.locals b
  entry : ∀ port, Sum.elim address Sum.inr (left.entry port) = right.entry port
  block : ∀ i, BlockMatch right (Sum.elim address Sum.inr) (left.block i) (address i)

namespace Simulation

variable {left right : Graph V F a b}

def route (sim : Simulation left right) : Label left.locals b → Label right.locals b :=
  Sum.elim sim.address Sum.inr

/-- Combine the address maps in the two private ranges and match each middle
port's handoff to the same port's handoff in the target. -/
def linkedAddress {c : Nat} {next next' : Graph V F b c}
    (first : Simulation left right) (second : Simulation next next') :
    Fin (left.linkedCount next) → Label (right.linkedCount next') c :=
  Fin.addCases
    (Fin.addCases (fun index => right.leftLabel next' (first.address index))
      (fun port => right.leftLabel next' (.inr port)))
    (fun index => right.rightLabel next' (second.address index))

/-- Check the local rules for a proposed map of private addresses. -/
def checkBlock [DecidableEq F] (right : Graph V F a b) (route : Label n b → Label right.locals b)
    (source : Block V (Label n b) F) (image : Label right.locals b) : Bool :=
  let copy := match image with
    | .inl target => decide (source.relabel route = right.block target)
    | .inr _ => false
  copy || source.body.targets.any fun target =>
    decide (source.body = .term (.br target (.var source.param)) ∧ image = route target)

/-- Check a finite certificate over all input ports and private blocks. -/
def check [DecidableEq F] (left right : Graph V F a b)
    (address : Fin left.locals → Label right.locals b) : Bool :=
  let route := Sum.elim address Sum.inr
  (List.finRange a).all (fun port => decide (route (left.entry port) = right.entry port)) &&
    (List.finRange left.locals).all (fun index => checkBlock right route (left.block index) (address index))

end Simulation

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link
