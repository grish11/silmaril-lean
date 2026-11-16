module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Reduction

@[expose] public section

/-!
# An explicitly extended left-linear raw J computation

This separately named relation retains the full intensional term syntax but
contracts `j A a C d b (refl c)` without comparing `a`, `b` and `c`.
It does not replace the existing exact based-J rule or checked equality.
-/

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT.LinearJ

/-- Parallel raw contraction, with independent endpoint annotations in its J root rule. -/
inductive Parallel : {n : ℕ} → Term n → Term n → Prop
  | var {n : ℕ} (i : Fin n) : Parallel ((.var i) : Term n) (.var i)
  | univ {n : ℕ} (i : ℕ) : Parallel ((.univ i) : Term n) (.univ i)
  | empty {n : ℕ}  : Parallel ((.empty) : Term n) (.empty)
  | unit {n : ℕ}  : Parallel ((.unit) : Term n) (.unit)
  | star {n : ℕ}  : Parallel ((.star) : Term n) (.star)
  | nat {n : ℕ}  : Parallel ((.nat) : Term n) (.nat)
  | zero {n : ℕ}  : Parallel ((.zero) : Term n) (.zero)
  | succ {n : ℕ} {t t' : Term n}
      (ht : Parallel t t') : Parallel (.succ t) (.succ t')
  | pi {n : ℕ} {A A' : Term n} {B B' : Term (n + 1)}
      (hA : Parallel A A') (hB : Parallel B B') : Parallel (.pi A B) (.pi A' B')
  | sigma {n : ℕ} {A A' : Term n} {B B' : Term (n + 1)}
      (hA : Parallel A A') (hB : Parallel B B') : Parallel (.sigma A B) (.sigma A' B')
  | lam {n : ℕ} {A A' : Term n} {body body' : Term (n + 1)}
      (hA : Parallel A A') (hbody : Parallel body body') : Parallel (.lam A body) (.lam A' body')
  | app {n : ℕ} {f f' : Term n} {a a' : Term n}
      (hf : Parallel f f') (ha : Parallel a a') : Parallel (.app f a) (.app f' a')
  | pair {n : ℕ} {a a' : Term n} {b b' : Term n}
      (ha : Parallel a a') (hb : Parallel b b') : Parallel (.pair a b) (.pair a' b')
  | fst {n : ℕ} {p p' : Term n}
      (hp : Parallel p p') : Parallel (.fst p) (.fst p')
  | snd {n : ℕ} {p p' : Term n}
      (hp : Parallel p p') : Parallel (.snd p) (.snd p')
  | natrec {n : ℕ} {C C' : Term (n + 1)} {z z' : Term n} {s s' : Term n} {t t' : Term n}
      (hC : Parallel C C') (hz : Parallel z z') (hs : Parallel s s') (ht : Parallel t t') : Parallel (.natrec C z s t) (.natrec C' z' s' t')
  | absurd {n : ℕ} {A A' : Term n} {e e' : Term n}
      (hA : Parallel A A') (he : Parallel e e') : Parallel (.absurd A e) (.absurd A' e')
  | id {n : ℕ} {A A' : Term n} {a a' : Term n} {b b' : Term n}
      (hA : Parallel A A') (ha : Parallel a a') (hb : Parallel b b') : Parallel (.id A a b) (.id A' a' b')
  | refl {n : ℕ} {a a' : Term n}
      (ha : Parallel a a') : Parallel (.refl a) (.refl a')
  | j {n : ℕ} {A A' : Term n} {a a' : Term n} {C C' : Term (n + 2)} {d d' : Term n} {b b' : Term n} {p p' : Term n}
      (hA : Parallel A A') (ha : Parallel a a') (hC : Parallel C C') (hd : Parallel d d') (hb : Parallel b b') (hp : Parallel p p') : Parallel (.j A a C d b p) (.j A' a' C' d' b' p')
  | beta {n : ℕ} {A a a' : Term n} {body body' : Term (n + 1)}
      (ht : Parallel body body') (ha : Parallel a a') :
      Parallel (.app (.lam A body) a) (body'.instantiate a')
  | fst_pair {n : ℕ} {a a' b : Term n} (ha : Parallel a a') :
      Parallel (.fst (.pair a b)) a'
  | snd_pair {n : ℕ} {a b b' : Term n} (hb : Parallel b b') :
      Parallel (.snd (.pair a b)) b'
  | nat_zero {n : ℕ} {C : Term (n + 1)} {z z' s : Term n} (hz : Parallel z z') :
      Parallel (.natrec C z s .zero) z'
  | nat_succ {n : ℕ} {C C' : Term (n + 1)} {z z' s s' t t' : Term n}
      (hC : Parallel C C') (hz : Parallel z z') (hs : Parallel s s') (ht : Parallel t t') :
      Parallel (.natrec C z s (.succ t)) (.app (.app s' t') (.natrec C' z' s' t'))
  | j_refl {n : ℕ} {A a b c d d' : Term n} {C : Term (n + 2)} (hd : Parallel d d') :
      Parallel (.j A a C d b (.refl c)) d'

/-- Complete development for the explicitly extended left-linear relation. -/
def develop : {n : ℕ} → Term n → Term n
  | _, .app (.lam _ body) a => (develop body).instantiate (develop a)
  | _, .fst (.pair a _) => develop a
  | _, .snd (.pair _ b) => develop b
  | _, .natrec _ z _ .zero => develop z
  | _, .natrec C z s (.succ t) => .app (.app (develop s) (develop t)) (.natrec (develop C) (develop z) (develop s) (develop t))
  | _, .j _ _ _ d _ (.refl _) => develop d
  | _, .var i => .var i
  | _, .univ i => .univ i
  | _, .empty => .empty
  | _, .unit => .unit
  | _, .star => .star
  | _, .nat => .nat
  | _, .zero => .zero
  | _, .succ t => .succ (develop t)
  | _, .pi A B => .pi (develop A) (develop B)
  | _, .sigma A B => .sigma (develop A) (develop B)
  | _, .lam A body => .lam (develop A) (develop body)
  | _, .app f a => .app (develop f) (develop a)
  | _, .pair a b => .pair (develop a) (develop b)
  | _, .fst p => .fst (develop p)
  | _, .snd p => .snd (develop p)
  | _, .natrec C z s t => .natrec (develop C) (develop z) (develop s) (develop t)
  | _, .absurd A e => .absurd (develop A) (develop e)
  | _, .id A a b => .id (develop A) (develop a) (develop b)
  | _, .refl a => .refl (develop a)
  | _, .j A a C d b p => .j (develop A) (develop a) (develop C) (develop d) (develop b) (develop p)

/-- Finite directed computation in the separately named left-linear extension. -/
abbrev Reduces {n : ℕ} : Term n → Term n → Prop := Relation.ReflTransGen Parallel

/-- Conversion generated by the separately named left-linear extension. -/
abbrev Convertible {n : ℕ} : Term n → Term n → Prop := Relation.EqvGen Parallel

end Silmaril.Logic.TypeTheory.IntensionalMLTT.LinearJ
