module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Rules.Defs
public import Mathlib.Logic.Relation

@[expose] public section

/-! Directed computation for the existing full intensional term grammar. -/

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT

/-- The six oriented primitive beta laws, including the existing based J law. -/
inductive RootReduction : {n : ℕ} → Term n → Term n → Prop
  | beta {n : ℕ} (A : Term n) (body : Term (n + 1)) (a : Term n) :
      RootReduction (.app (.lam A body) a) (body.instantiate a)
  | fst_pair {n : ℕ} (a b : Term n) : RootReduction (.fst (.pair a b)) a
  | snd_pair {n : ℕ} (a b : Term n) : RootReduction (.snd (.pair a b)) b
  | nat_zero {n : ℕ} (C : Term (n + 1)) (z s : Term n) :
      RootReduction (.natrec C z s .zero) z
  | nat_succ {n : ℕ} (C : Term (n + 1)) (z s t : Term n) :
      RootReduction (.natrec C z s (.succ t)) (.app (.app s t) (.natrec C z s t))
  | j_refl {n : ℕ} (A a : Term n) (C : Term (n + 2)) (d : Term n) :
      RootReduction (.j A a C d a (.refl a)) d

/-- Exactly one primitive contraction in one subterm, including annotations and motives. -/
inductive ReductionStep : {n : ℕ} → Term n → Term n → Prop
  | root {n : ℕ} {t u : Term n} : RootReduction t u → ReductionStep t u
  | succ {n : ℕ}  {t t' : Term n}
      (h : ReductionStep t t') : ReductionStep (.succ t) (.succ t')
  | pi_domain {n : ℕ} {B : Term (n + 1)} {A A' : Term n}
      (h : ReductionStep A A') : ReductionStep (.pi A B) (.pi A' B)
  | pi_codomain {n : ℕ} {A : Term n} {B B' : Term (n + 1)}
      (h : ReductionStep B B') : ReductionStep (.pi A B) (.pi A B')
  | sigma_domain {n : ℕ} {B : Term (n + 1)} {A A' : Term n}
      (h : ReductionStep A A') : ReductionStep (.sigma A B) (.sigma A' B)
  | sigma_codomain {n : ℕ} {A : Term n} {B B' : Term (n + 1)}
      (h : ReductionStep B B') : ReductionStep (.sigma A B) (.sigma A B')
  | lam_domain {n : ℕ} {body : Term (n + 1)} {A A' : Term n}
      (h : ReductionStep A A') : ReductionStep (.lam A body) (.lam A' body)
  | lam_body {n : ℕ} {A : Term n} {body body' : Term (n + 1)}
      (h : ReductionStep body body') : ReductionStep (.lam A body) (.lam A body')
  | app_function {n : ℕ} {a : Term n} {f f' : Term n}
      (h : ReductionStep f f') : ReductionStep (.app f a) (.app f' a)
  | app_argument {n : ℕ} {f : Term n} {a a' : Term n}
      (h : ReductionStep a a') : ReductionStep (.app f a) (.app f a')
  | pair_left {n : ℕ} {b : Term n} {a a' : Term n}
      (h : ReductionStep a a') : ReductionStep (.pair a b) (.pair a' b)
  | pair_right {n : ℕ} {a : Term n} {b b' : Term n}
      (h : ReductionStep b b') : ReductionStep (.pair a b) (.pair a b')
  | fst {n : ℕ}  {p p' : Term n}
      (h : ReductionStep p p') : ReductionStep (.fst p) (.fst p')
  | snd {n : ℕ}  {p p' : Term n}
      (h : ReductionStep p p') : ReductionStep (.snd p) (.snd p')
  | natrec_motive {n : ℕ} {z : Term n} {s : Term n} {t : Term n} {C C' : Term (n + 1)}
      (h : ReductionStep C C') : ReductionStep (.natrec C z s t) (.natrec C' z s t)
  | natrec_zero {n : ℕ} {C : Term (n + 1)} {s : Term n} {t : Term n} {z z' : Term n}
      (h : ReductionStep z z') : ReductionStep (.natrec C z s t) (.natrec C z' s t)
  | natrec_step {n : ℕ} {C : Term (n + 1)} {z : Term n} {t : Term n} {s s' : Term n}
      (h : ReductionStep s s') : ReductionStep (.natrec C z s t) (.natrec C z s' t)
  | natrec_scrutinee {n : ℕ} {C : Term (n + 1)} {z : Term n} {s : Term n} {t t' : Term n}
      (h : ReductionStep t t') : ReductionStep (.natrec C z s t) (.natrec C z s t')
  | absurd_type {n : ℕ} {e : Term n} {A A' : Term n}
      (h : ReductionStep A A') : ReductionStep (.absurd A e) (.absurd A' e)
  | absurd_term {n : ℕ} {A : Term n} {e e' : Term n}
      (h : ReductionStep e e') : ReductionStep (.absurd A e) (.absurd A e')
  | id_type {n : ℕ} {a : Term n} {b : Term n} {A A' : Term n}
      (h : ReductionStep A A') : ReductionStep (.id A a b) (.id A' a b)
  | id_left {n : ℕ} {A : Term n} {b : Term n} {a a' : Term n}
      (h : ReductionStep a a') : ReductionStep (.id A a b) (.id A a' b)
  | id_right {n : ℕ} {A : Term n} {a : Term n} {b b' : Term n}
      (h : ReductionStep b b') : ReductionStep (.id A a b) (.id A a b')
  | refl {n : ℕ}  {a a' : Term n}
      (h : ReductionStep a a') : ReductionStep (.refl a) (.refl a')
  | j_type {n : ℕ} {a : Term n} {C : Term (n + 2)} {d : Term n} {b : Term n} {p : Term n} {A A' : Term n}
      (h : ReductionStep A A') : ReductionStep (.j A a C d b p) (.j A' a C d b p)
  | j_left {n : ℕ} {A : Term n} {C : Term (n + 2)} {d : Term n} {b : Term n} {p : Term n} {a a' : Term n}
      (h : ReductionStep a a') : ReductionStep (.j A a C d b p) (.j A a' C d b p)
  | j_motive {n : ℕ} {A : Term n} {a : Term n} {d : Term n} {b : Term n} {p : Term n} {C C' : Term (n + 2)}
      (h : ReductionStep C C') : ReductionStep (.j A a C d b p) (.j A a C' d b p)
  | j_base {n : ℕ} {A : Term n} {a : Term n} {C : Term (n + 2)} {b : Term n} {p : Term n} {d d' : Term n}
      (h : ReductionStep d d') : ReductionStep (.j A a C d b p) (.j A a C d' b p)
  | j_right {n : ℕ} {A : Term n} {a : Term n} {C : Term (n + 2)} {d : Term n} {p : Term n} {b b' : Term n}
      (h : ReductionStep b b') : ReductionStep (.j A a C d b p) (.j A a C d b' p)
  | j_path {n : ℕ} {A : Term n} {a : Term n} {C : Term (n + 2)} {d : Term n} {b : Term n} {p p' : Term n}
      (h : ReductionStep p p') : ReductionStep (.j A a C d b p) (.j A a C d b p')

/-- A finite sequence of directed compatible contractions, allowing zero steps. -/
abbrev Reduces {n : ℕ} : Term n → Term n → Prop := Relation.ReflTransGen ReductionStep

/-- Finite conversion zigzags generated by directed compatible contractions. -/
abbrev ReductionZigzag {n : ℕ} : Term n → Term n → Prop := Relation.EqvGen ReductionStep

end Silmaril.Logic.TypeTheory.IntensionalMLTT
