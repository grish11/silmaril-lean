module

public import Silmaril.Games.Abstract.StratSession.Defs
public import Silmaril.Games.Handler.Defs

/-!
# Sessions composed with one-call handlers: definitions

A *one-call handler* `callH g f : Handler E (sig1 A B)` answers each question `a` by exactly one
call `g a : E.Op`, returning `f a n` for the answer `n`. Such handlers route and rename: a
handler that sends each outer question to one side of a pairing, or that translates answers
along a bijection, is of this form.

* `callS g f : ObsTriple E PUnit A (B ⊕ PUnit)` is the stateless session triple of `callH g f`:
  a round at `a` is the single call `⟨g a, n⟩` and returns `f a n`, a trap answer `.inr ()`
  being a continuing trap. Its only pending call is `g a`; it has no productive stream. For
  `g = id` and `f a = id` it is `SessionCat.idS`.
* `mapS g f t : ObsTriple E S A' (B' ⊕ PUnit)` pre-composes the questions of a session triple
  `t : ObsTriple E S A (B ⊕ PUnit)` with `g : A' → A` and post-composes its answers (values and
  continuing traps alike) with `f a'`. Logs, pending calls and productive streams are those of
  `t` at `g a'`; plain traps and divergence are kept (`mapEnd`).

Theorems in `Silmaril.Games.Abstract.SessionRoute.Thms`: the session of `callS g f` is the
strategy of `callH g f`, and a session served to `callH g f` is the session of `mapS g f t`.
-/

@[expose] public section

namespace Silmaril.Games.Abstract.SessionRoute

open Silmaril.Games Silmaril.Games.Abstract.StratObs

universe u

variable {E : Sig.{u}} {S A A' B B' : Type u}

/-- **The one-call handler**: the question `a` calls `g a` and returns `f a n` on the answer
`n`. -/
def callH (g : A → E.Op) (f : (a : A) → E.Ar (g a) → B ⊕ PUnit.{u + 1}) : Handler E (sig1 A B) :=
  fun a => .call (g a) fun n => .pure (f a n)

/-- **The session triple of a one-call handler**: a round at `a` is the call `⟨g a, n⟩`,
returning `f a n` in the unit store. -/
def callS (g : A → E.Op) (f : (a : A) → E.Ar (g a) → B ⊕ PUnit.{u + 1}) :
    ObsTriple E PUnit.{u + 1} A (B ⊕ PUnit.{u + 1}) :=
  (fun _ a => {x | ∃ n, x = ([⟨g a, n⟩], End.ret (f a n) PUnit.unit)},
    fun _ a => {([], g a)},
    fun _ _ => ∅)

/-- Map the answer of an end; traps and divergence are kept. -/
def mapEnd (k : B → B') : End S B → End S B'
  | .ret b s => .ret (k b) s
  | .trap => .trap
  | .div => .div

/-- **A session triple with mapped questions and answers**: at `a'`, the behaviours of `t` at
`g a'`, answers mapped by `f a'`. -/
def mapS (g : A' → A) (f : A' → B ⊕ PUnit.{u + 1} → B' ⊕ PUnit.{u + 1})
    (t : ObsTriple E S A (B ⊕ PUnit.{u + 1})) : ObsTriple E S A' (B' ⊕ PUnit.{u + 1}) :=
  (fun s a => (fun x => (x.1, mapEnd (f a) x.2)) '' t.1 s (g a),
    fun s a => t.2.1 s (g a),
    fun s a => t.2.2 s (g a))

end Silmaril.Games.Abstract.SessionRoute
