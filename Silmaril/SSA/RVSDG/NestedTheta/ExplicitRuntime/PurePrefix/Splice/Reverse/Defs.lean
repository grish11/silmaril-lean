module

public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.PurePrefix.Splice.Defs

/-! # Rebase the ordered suffix of a checked mixed splice -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.PurePrefix.Splice.Reverse

open OrderedRuntime.Structured (Ty newestIndex newestPort)
open ExplicitRuntime.Splice (weaken splitOutput)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
variable {V : Type u} {P E Q : Dialect.{u,v} V PUnit.{u+1}}
variable {entry args outs : Ports (Ty V)}
variable {past localRows rows : List (Ports (Ty V))}

/-- An earlier origin can be admitted at the new boundary or rejected. -/
abbrev Routing (entry : Ports (Ty V)) (past : List (Ports (Ty V)))
    (args : Ports (Ty V)) (localRows : List (Ports (Ty V))) :=
  ∀ {t : Ty V}, Origin entry past t → Option (Origin args localRows t)

def Routing.push (route : Routing entry past args localRows) (head : Ports (Ty V)) :
    Routing entry (past ++ [head]) args (localRows ++ [head])
  | _, .arg p => (route (.arg p)).map (weaken head)
  | _, .output i p =>
    match splitOutput head past i p with
    | .inl ⟨j,q⟩ => (route (.output j q)).map (weaken head)
    | .inr q => some (.output (newestIndex head localRows) (newestPort q localRows))

def Routing.wires (route : Routing entry past args localRows) :
    {outs : Ports (Ty V)} → Wires entry past outs → Option (Wires args localRows outs)
  | _, .nil => some .nil
  | _, .cons wire rest => do
    return .cons (← route wire) (← route.wires rest)

def Routing.identity : Routing entry past entry past := fun wire => some wire

/-- Only the tuple at the cut becomes the new input. The original root
arguments and the rows before the cut cannot be referenced from the suffix. -/
def boundary (past : List (Ports (Ty V))) (args : Ports (Ty V)) :
    Routing entry (past ++ [args]) args []
  | _, .arg _ => none
  | _, .output i p =>
    match splitOutput args past i p with
    | .inl _ => none
    | .inr q => some (.arg q)

def collectChildren : {n : Nat} → {T : Fin n → Type w} →
    ((i : Fin n) → Option (T i)) → Option ((i : Fin n) → T i)
  | 0, _, _ => some (fun i => i.elim0)
  | _ + 1, _, f => do
    return Fin.cases (← f 0) (← collectChildren fun i => f i.succ)

/-- Strip the ordered opcode tag and rebase every input and result origin.
Nested scopes already have their own arguments and vertex positions. -/
def orderedSuffix : {entry args outs : Ports (Ty V)} →
    {past localRows rows : List (Ports (Ty V))} →
    Routing entry past args localRows → Term (Op P E Q) entry past rows outs →
    Option (Term (Ordered P E) args localRows rows outs)
  | _, _, _, _, _, _, route, .ret wires => (route.wires wires).map .ret
  | _, _, _, _, _, _, route, .bind ⟨ins, .base (.simple (.ordered op)), wires, sigs⟩ _ rest =>
    (route.wires wires).bind fun inputs => do
      let rest ← orderedSuffix (route.push _) rest
      return .bind ⟨ins, .base (.simple op), inputs, sigs⟩ (fun i => i.elim0) rest
  | _, _, _, _, _, _, route, .bind ⟨_, .base (.gamma (entry := ports) n), wires, sigs⟩ children rest =>
    (route.wires wires).bind fun inputs => do
      let children ← collectChildren.{max u v} fun i => orderedSuffix Routing.identity (children i)
      let rest ← orderedSuffix (route.push _) rest
      return .bind ⟨_, .base (.gamma (entry := ports) n), inputs, sigs⟩ children rest
  | _, _, _, _, _, _, route, .bind ⟨_, .theta ports, wires, sigs⟩ children rest =>
    (route.wires wires).bind fun inputs => do
      let children ← collectChildren.{max u v} fun i => orderedSuffix Routing.identity (children i)
      let rest ← orderedSuffix (route.push _) rest
      return .bind ⟨_, .theta ports, inputs, sigs⟩ children rest
  | _, _, _, _, _, _, _, .bind ⟨_, .base (.simple (.pure ..)), _, _⟩ _ _ => none

end Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.PurePrefix.Splice.Reverse
