module

public import Silmaril.Logic.ACL2.Recursive.Certificate

@[expose] public section

namespace Silmaril.Proofs.Logic.ACL2.Recursive

open Silmaril.Logic.ACL2 Silmaril.Logic.ACL2.Recursive

variable {S R : Signature} {n : Nat}

theorem path_cons {M : Model S} {env : Env M n} {path : Path S n}
    {fact : Term S n × Bool}
    (h : if fact.2 then fact.1.eval M env ≠ M.primitives.nil
      else fact.1.eval M env = M.primitives.nil)
    (hp : path.Holds M env) : Path.Holds (fact :: path) M env := by
  intro entry he
  rcases List.mem_cons.mp he with rfl | he
  · exact h
  · exact hp entry he

theorem checkCdr_sound {M : Model S} (size : CdrSize M.primitives) (env : Env M n)
    (caller : Fin n) (argument : Term S n) (fact : Term S n × Bool)
    (holds : if fact.2 then fact.1.eval M env ≠ M.primitives.nil
      else fact.1.eval M env = M.primitives.nil)
    (accepted : checkCdr caller argument fact = true) :
    size.size (argument.eval M env) < size.size (env caller) := by
  obtain ⟨test, branch⟩ := fact
  cases branch <;> cases argument <;> cases test <;> simp [checkCdr] at accepted
  rename_i x y
  cases x <;> cases y <;> simp_all
  rename_i i j
  obtain ⟨rfl, rfl⟩ := accepted
  apply size.cdr_lt
  cases hc : M.primitives.consp (env j) with
  | true => exact hc
  | false => simp [Term.eval, hc, Primitives.ofBool] at holds

theorem check_sound {M : Model S} (size : CdrSize M.primitives)
    (arg : MeasureArgument R) (caller : Fin n) (env : Env M n)
    (body : Body S R n) (cert : Certificate) (path : Path S n)
    (holds : path.Holds M env) (accepted : cert.check arg caller path body = true) :
    body.Decreases M (size.rank arg) (size.size (env caller)) env := by
  induction body generalizing cert path with
  | base => trivial
  | call f args =>
    cases cert <;> simp [Certificate.check] at accepted
    rename_i guard
    cases hg : path[guard]? with
    | none => simp [hg] at accepted
    | some fact =>
      exact checkCdr_sound size env caller (args (arg f)) fact
        (holds fact (List.mem_of_getElem? hg)) (by simpa [hg] using accepted)
  | apply context args ih =>
    cases cert <;> simp only [Certificate.check, Bool.false_eq_true] at accepted
    rename_i certs
    intro i
    have hc := (List.all_eq_true.mp (Bool.and_eq_true_iff.mp accepted).2) i (List.mem_finRange i)
    cases hi : certs[i.val]? with
    | none => simp [hi] at hc
    | some c => exact ih i c path holds (by simpa [hi] using hc)
  | ite test yes no ihy ihn =>
    cases cert <;> simp only [Certificate.check, Bool.false_eq_true] at accepted
    rename_i cy cn
    obtain ⟨hy, hn⟩ := Bool.and_eq_true_iff.mp accepted
    exact ⟨fun ht => ihy cy _ (path_cons (fact := (test, true)) ht holds) hy,
      fun ht => ihn cn _ (path_cons (fact := (test, false)) ht holds) hn⟩

theorem accepted_terminates (B : Block S) {M : Model S} (size : CdrSize M.primitives)
    (arg : MeasureArgument B.members) (cert : BlockCertificate B)
    (accepted : cert.Accepted B arg) : B.Terminates M (size.rank arg) := by
  intro state
  exact check_sound size arg (arg state.symbol) state.args (B.body state.symbol) (cert state.symbol)
    [] (by simp [Path.Holds]) (accepted state.symbol)

end Silmaril.Proofs.Logic.ACL2.Recursive
