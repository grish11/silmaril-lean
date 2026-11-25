module

import Silmaril.Logic.Temporal.TLA.Surface.Defs

/-! Handwritten ASTs of two specifications and focused syntax examples. -/

namespace Silmaril.Logic.Temporal.TLA.Surface.Examples

private def name (id : Ident) : Expr := .ref (.operator (.ident id)) [] []
private def call (id : Ident) (args : List Expr) : Expr :=
  .ref (.operator (.ident id)) (args.map .expr) []
private def infixOp (op : String) (left right : Expr) : Expr :=
  .infix (.symbol op) left right
private def natural (n : Nat) : Expr := .literal (.natural n)
private def operator (id : Ident) (body : Expr) : ModuleUnit :=
  .definition (.operator .ordinary (.ident id []) body)
private def stepRef (level : Nat) (id : Ident) : Expr :=
  .ref (.step ⟨.explicit level, id⟩) [] []

/-!
```tla
---- MODULE BoundedQueue ----
EXTENDS Naturals, Sequences
CONSTANTS Messages, Capacity
VARIABLE q
ASSUME Capacity \in Nat

Init == q = <<>>
Enqueue(m) ==
  /\ Len(q) < Capacity
  /\ q' = Append(q, m)
Dequeue ==
  /\ q # <<>>
  /\ q' = Tail(q)
Next ==
  \/ \E m \in Messages : Enqueue(m)
  \/ Dequeue
TypeOK ==
  /\ q \in Seq(Messages)
  /\ Len(q) <= Capacity
Spec ==
  /\ Init
  /\ [][Next]_q
  /\ WF_q(Dequeue)
THEOREM QueueSafety == Spec => []TypeOK
<1>1. Init => TypeOK
  OBVIOUS
<1>2. TypeOK /\ [Next]_q => TypeOK'
  PROOF OMITTED
<1>3. QED BY <1>1, <1>2 DEF Spec
====
```
-/

private def queueSpec : Expr :=
  .junction .conjunction
    [ name "Init",
      .prefix .always (.action .square (name "Next") (name "q")),
      .fairness .weak (name "q") (name "Dequeue") ]

private def queueProof : Proof :=
  .steps
    [ ⟨⟨.explicit 1, some "1"⟩,
        .assert (.expr (infixOp "=>" (name "Init") (name "TypeOK"))) (some .obvious)⟩,
      ⟨⟨.explicit 1, some "2"⟩,
        .assert (.expr (infixOp "=>"
          (infixOp "/\\" (name "TypeOK") (.action .square (name "Next") (name "q")))
          (.postfix .prime (name "TypeOK")))) (some .omitted)⟩ ]
    ⟨.explicit 1, some "3"⟩
    (some (.byFacts false
      ⟨[.expr (stepRef 1 "1"), .expr (stepRef 1 "2")], [.expr (name "Spec")]⟩))

private def boundedQueue : Module where
  name := "BoundedQueue"
  extendsModules := ["Naturals", "Sequences"]
  units :=
    [ .constants [.ident "Messages" 0, .ident "Capacity" 0],
      .variables ["q"],
      .assumption none (infixOp "\\in" (name "Capacity") (name "Nat")),
      operator "Init" (infixOp "=" (name "q") (.tuple [])),
      .definition (.operator .ordinary (.ident "Enqueue" [.ident "m" 0])
        (.junction .conjunction
          [ infixOp "<" (call "Len" [name "q"]) (name "Capacity"),
            infixOp "=" (.postfix .prime (name "q")) (call "Append" [name "q", name "m"]) ])),
      operator "Dequeue" (.junction .conjunction
        [ infixOp "#" (name "q") (.tuple []),
          infixOp "=" (.postfix .prime (name "q")) (call "Tail" [name "q"]) ]),
      operator "Next" (.junction .disjunction
        [ .rigidQuant .exists (.bounded [⟨.names ["m"], name "Messages"⟩])
            (call "Enqueue" [name "m"]),
          name "Dequeue" ]),
      operator "TypeOK" (.junction .conjunction
        [ infixOp "\\in" (name "q") (call "Seq" [name "Messages"]),
          infixOp "<=" (call "Len" [name "q"]) (name "Capacity") ]),
      operator "Spec" queueSpec,
      .theoremDecl ⟨some "QueueSafety",
        .expr (infixOp "=>" (name "Spec") (.prefix .always (name "TypeOK"))), some queueProof⟩ ]

example :
    (match boundedQueue.units.reverse with
     | .theoremDecl ⟨_, _, some (.steps
         [⟨_, .assert _ (some .obvious)⟩, ⟨_, .assert _ (some .omitted)⟩]
         ⟨.explicit 1, some "3"⟩ (some (.byFacts false ⟨[_, _], [_]⟩)))⟩ ::
         .definition (.operator _ (.ident "Spec" [])
           (.junction .conjunction [_, .prefix .always (.action .square _ _),
             .fairness .weak _ _])) :: _ => true
     | _ => false) = true := rfl

/-!
```tla
---- MODULE Dispatcher ----
EXTENDS Naturals
CONSTANT Workers
VARIABLE status

---- MODULE Worker ----
CONSTANTS Id, Ready(_)
VARIABLE workerState
Tick ==
  /\ Ready(workerState[Id])
  /\ workerState' = [workerState EXCEPT ![Id].count = @ + 1, ![Id].ready = FALSE]
====

Eligible(s) == s.ready
WorkerAt(w) == INSTANCE Worker WITH Id <- w, Ready <- Eligible, workerState <- status
Init == status = [w \in Workers |-> [ready |-> TRUE, count |-> 0]]
Next == \E w \in Workers : WorkerAt(w)!Tick
Spec == Init /\ [][Next]_status
====
```
-/

private def worker : Module where
  name := "Worker"
  extendsModules := []
  units :=
    [ .constants [.ident "Id" 0, .ident "Ready" 1],
      .variables ["workerState"],
      operator "Tick" (.junction .conjunction
        [ call "Ready" [.index (name "workerState") [name "Id"]],
          infixOp "=" (.postfix .prime (name "workerState"))
            (.except (name "workerState")
              [ ⟨[.index [name "Id"], .field "count"], infixOp "+" .oldValue (natural 1)⟩,
                ⟨[.index [name "Id"], .field "ready"], name "FALSE"⟩ ]) ]) ]

private def dispatchNext : Expr :=
  .rigidQuant .exists (.bounded [⟨.names ["w"], name "Workers"⟩])
    (.ref (.operator (.ident "WorkerAt")) [.expr (name "w")] [.named (.ident "Tick") []])

private def dispatcher : Module where
  name := "Dispatcher"
  extendsModules := ["Naturals"]
  units :=
    [ .constants [.ident "Workers" 0],
      .variables ["status"],
      .submodule worker,
      .definition (.operator .ordinary (.ident "Eligible" [.ident "s" 0])
        (.field (name "s") "ready")),
      .definition (.namedInstance .ordinary "WorkerAt" [.ident "w" 0]
        ⟨"Worker", [⟨.ident "Id", .expr (name "w")⟩,
          ⟨.ident "Ready", .expr (name "Eligible")⟩,
          ⟨.ident "workerState", .expr (name "status")⟩]⟩),
      operator "Init" (infixOp "=" (name "status")
        (.function [⟨.names ["w"], name "Workers"⟩]
          (.record [⟨"ready", name "TRUE"⟩, ⟨"count", natural 0⟩]))),
      operator "Next" dispatchNext,
      operator "Spec" (infixOp "/\\" (name "Init")
        (.prefix .always (.action .square (name "Next") (name "status")))) ]

example :
    (match dispatcher.units with
     | _ :: _ :: .submodule ⟨"Worker", _, _⟩ :: _ ::
         .definition (.namedInstance _ "WorkerAt" _ ⟨"Worker", [_, second, _]⟩) :: _ ::
         .definition (.operator _ (.ident "Next" []) (.rigidQuant .exists _
           (.ref (.operator (.ident "WorkerAt")) [.expr _] [.named (.ident "Tick") []]))) :: _ =>
       match second with
       | ⟨.ident "Ready", .expr (.ref (.operator (.ident "Eligible")) [] [])⟩ => true
       | _ => false
     | _ => false) = true := rfl

-- Apply(LAMBDA x : x + 1, M(2)!F!Label(0)!1)
example : Expr :=
  .ref (.operator (.ident "Apply"))
    [ .lambda ["x"] (infixOp "+" (name "x") (natural 1)),
      .expr (.ref (.operator (.ident "M")) [.expr (natural 2)]
        [.named (.ident "F") [], .named (.ident "Label") [.expr (natural 0)],
          .structural (.operand 1)]) ] []

-- \AA v : LET RECURSIVE F(_)  F(x) == L(x):: IF x = 0 THEN v ELSE F(x - 1) IN F(1)
example : Expr :=
  .temporalQuant .forall ["v"] (.letIn
    [ .recursive [.ident "F" 1],
      .definition (.operator .ordinary (.ident "F" [.ident "x" 0])
        (.labeled ⟨"L", ["x"]⟩ (.ifThenElse
          (infixOp "=" (name "x") (natural 0))
          (name "v") (call "F" [infixOp "-" (name "x") (natural 1)])))) ]
    (call "F" [natural 1]))

-- A SUFFICES step with its own proof. The outer proof still has a separate QED.
example : Proof :=
  .steps [⟨⟨.explicit 1, some "a"⟩, .suffices
    (.assumeProve .plain [.newBoundConstant "m" (name "Messages")] .plain
      (call "P" [name "m"]))
    (some (.steps [⟨⟨.next, some "a"⟩, .have (name "Fact")⟩]
      ⟨.current, none⟩ (some .obvious)))⟩]
    ⟨.explicit 1, none⟩ (some (.byFacts true ⟨[.expr (stepRef 1 "a")], []⟩))

end Silmaril.Logic.Temporal.TLA.Surface.Examples
