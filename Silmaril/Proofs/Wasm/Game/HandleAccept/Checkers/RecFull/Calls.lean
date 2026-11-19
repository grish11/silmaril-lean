module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.Basic

/-!
# Reader checkers: rules for bodies that may return conditionally, and internal calls

The shared checker rules (`Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.X.call`, …) ask the
postcondition to accept every `return` (`Leaves`). A function whose normal return certifies a
property (here: its argument is accepted) accepts only some returns, so this file restates the
import rules for a postcondition accepting **traps and exceptions** (`TrapsQ`), and adds the
**internal call rule** for a Wasm function with a valid specification:

* `Shape.of_okR`: the checker shape, with the instruction comparison extended by
  `unreachable` (`ieqR`);
* `hwp_importT`, `R.call`, `R.kind`, `R.car`, `R.cdr`, `R.accept`: cons reader imports;
* `X.callSpec`: `call x` of the function at address `a` meeting `S` for every number of steps
  (`FSpecValid`), by `Safe.callIdx` at each step index. Recursive specifications are proved by
  an outer induction (on a size bound of the argument) that supplies `FSpecValid` for the
  smaller instances, so no step-indexed reasoning is needed inside bodies.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.RecFull

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
  Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.GameLink
  Silmaril.Formats Silmaril.Wasm.Game.HandleAccept Silmaril.Wasm.Game.HandleAccept.Checkers
  Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers
open Silmaril.Wasm.Logic.Strategy (ISpec resultOutcome)
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {P : Profile} {host : HostSemantics Nat} {s : Store Nat} {f : Frame} {us : List Val}
  {is : List Instr} {Q : Post Nat}

/-- `Q` accepts every trap and exception in the store `s`. -/
def TrapsQ (Q : Post Nat) (s : Store Nat) : Prop := ∀ f, Q s f .trap ∧ ∀ a, Q s f (.throw a)

/-- `Q` accepts the return of no values in the store `s`. -/
def RetQ (Q : Post Nat) (s : Store Nat) : Prop := ∀ f, Q s f (.ret [])

theorem TrapsQ.loop {Inv : Store Nat → Frame → List Val → Prop} (h : TrapsQ Q s) :
    TrapsQ (loopPost 0 [] Inv Q) s := fun f => ⟨(h f).1, (h f).2⟩

theorem TrapsQ.label {rest : List Admin} (h : TrapsQ Q s) :
    TrapsQ (labelPost P host 0 [] us (seqPost P host rest Q)) s := fun f => ⟨(h f).1, (h f).2⟩

theorem RetQ.loop {Inv : Store Nat → Frame → List Val → Prop} (h : RetQ Q s) :
    RetQ (loopPost 0 [] Inv Q) s := fun f => h f

theorem RetQ.label {rest : List Admin} (h : RetQ Q s) :
    RetQ (labelPost P host 0 [] [] (seqPost P host rest Q)) s := fun f => h f

/-! ## The internal call rule -/

/-- **`call x` of a Wasm function with a valid specification**: from its precondition, every
normal outcome the specification allows must make the rest safe, and its traps and exceptions
must be allowed. -/
theorem X.callSpec {S : FSpec Nat} {a : Nat} {x : FuncIdx} {fi : FuncInst Nat} {args : List Val}
    (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi)
    (hS : FSpecValid P host a S) (hpre : S.pre s args)
    (hk : ∀ s' res, S.post s args s' (.normal res) →
      HWP P host s' f (vals (us ++ res) ++ expression is) Q)
    (ht : ∀ s', S.post s args s' .trap → Q s' f .trap)
    (hth : ∀ s' y, S.post s args s' (.throw y) → Q s' f (.throw y)) :
    HWP P host s f (vals (us ++ args) ++ expression (.call x :: is)) Q
  | 0 => trivial
  | n + 1 => by
    refine Safe.callIdx (x := x) (S := S) hx hf (hS n) hpre ?_
    rintro s' o ⟨-, ⟨res, rfl, hR⟩ | ⟨rfl, hR⟩ | ⟨y, rfl, hR⟩⟩
    · exact hk s' res hR n
    · exact ht s' hR
    · exact hth s' y hR

/-! ## Import calls under a trapping postcondition -/

section Import

variable {I : ScalarInstance} {Ii : ISpec I.E}

/-- A call of import `k` when the postcondition accepts traps and exceptions. -/
theorem hwp_importT {x : FuncIdx} {k : Nat} {fk : FuncInst Nat} {ps rs : Ty (.list .val)}
    {args : List Val}
    (hx : f.module.funcs[x.toNat]? = some k) (hf : s.funcs[k]? = some fk)
    (hcode : fk.code = .host k)
    (he : Expand fk.type (.func ps rs)) (hps : ps.length = args.length)
    (hop : ∃ e, I.importOp? k args = some e ∧ Ii.pre e)
    (hk : ∀ e (v : I.E.Ar e), I.importOp? k args = some e → Ii.post e v →
      ∀ res, Answer.toResult (ft := I.imports.get e.1) v = .values res →
        HWP P (gameHost I Ii) s f (vals (us ++ res) ++ expression is) Q)
    (hQ : TrapsQ Q s) :
    HWP P (gameHost I Ii) s f (vals (us ++ args) ++ expression (.call x :: is)) Q
  | 0 => trivial
  | n + 1 => by
    have hS : importCtx I Ii (id k) = some (importSpec I Ii k) := rfl
    refine Safe.callIdx (x := x)
      (S := Silmaril.Wasm.Logic.Open.stubSpec k k (importSpec I Ii k)) hx hf
      (Silmaril.Wasm.Logic.Open.FSpecAt.stub hS n) ⟨⟨fk, ps, rs, hf, hcode, he, hps.symm⟩, hop⟩ ?_
    rintro s' o ⟨-, ⟨res, rfl, hR⟩ | ⟨rfl, hR⟩ | ⟨y, rfl, hR⟩⟩
    · obtain ⟨rfl, hall⟩ := hR
      obtain ⟨e, he', -⟩ := hop
      obtain ⟨v, hv, ho⟩ := hall e he'
      have hr : Answer.toResult (ft := I.imports.get e.1) v = .values res := by
        revert ho
        cases v <;> simp [Answer.toResult, resultOutcome]
      exact hk e v he' hv res hr n
    · obtain ⟨rfl, -⟩ := hR
      exact (hQ f).1
    · obtain ⟨rfl, -⟩ := hR
      exact (hQ f).2 y

end Import

section Calls

variable {I : ScalarInstance} {locals : List ValType} {body : List Instr} {D : List (Option Val)}
  (hS : Shape I locals body D) (hs : s.funcs = I.store.funcs)
  (hm : f.module.funcs = [0, 1, 2, 3, 4, 5])
  {ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))} {L : Set (SExp2 (BitVec 64))}
  {a : BitVec 32}

include hS hs hm

/-- A call of import `k < 5` by an instantiated checker, for a trapping postcondition. -/
theorem R.call {k : Nat} (hk : k < 5) {x : FuncIdx} (hx : x.toNat = k)
    (hop : ∃ e, I.importOp? k [.i32 a] = some e ∧ (consISpec (ts := I.imports) consIx ρ L).pre e)
    (hc : ∀ e (v : I.E.Ar e), I.importOp? k [.i32 a] = some e →
      (consISpec (ts := I.imports) consIx ρ L).post e v →
      ∀ res, Answer.toResult (ft := I.imports.get e.1) v = .values res →
        HWP P (gameHost I (consISpec consIx ρ L)) s f (vals (us ++ res) ++ expression is) Q)
    (hQ : TrapsQ Q s) :
    HWP P (gameHost I (consISpec consIx ρ L)) s f
      (vals (us ++ [.i32 a]) ++ expression (.call x :: is)) Q := by
  obtain ⟨fk, ps, rs, hf, hcode, he, hps⟩ := hS.stub k hk
  refine hwp_importT (fk := fk) (ps := ps) (rs := rs) ?_ (by rw [hs]; exact hf) hcode he
    (by simp [hps]) hop hc hQ
  rw [hm, hx]
  rcases k with _ | _ | _ | _ | _ | k <;> first | rfl | omega

/-- `kind(a)`. -/
theorem R.kind (hQ : TrapsQ Q s)
    (hc : ∀ c, ((c = 0 ∧ ρ a = some .nil) ∨ (c = 1 ∧ ∃ w, ρ a = some (.atom w)) ∨
      (c = 2 ∧ ∃ x y, ρ a = some (.cons x y))) →
      HWP P (gameHost I (consISpec consIx ρ L)) s f (vals (us ++ [.i32 c]) ++ expression is) Q) :
    HWP P (gameHost I (consISpec consIx ρ L)) s f
      (vals (us ++ [.i32 a]) ++ expression (.call ⟨0⟩ :: is)) Q :=
  R.call hS hs hm (k := 0) (by omega) rfl (pre_of_ne hS.imports (by omega) (by omega) a)
    (fun _ _ he hv res hr => by
      obtain ⟨c, rfl, h⟩ := kind_post hS.imports he hv hr
      exact hc c h) hQ

/-- `car(a)`. -/
theorem R.car (hQ : TrapsQ Q s)
    (hc : ∀ c x y, ρ a = some (.cons x y) → ρ c = some x →
      HWP P (gameHost I (consISpec consIx ρ L)) s f (vals (us ++ [.i32 c]) ++ expression is) Q) :
    HWP P (gameHost I (consISpec consIx ρ L)) s f
      (vals (us ++ [.i32 a]) ++ expression (.call ⟨1⟩ :: is)) Q :=
  R.call hS hs hm (k := 1) (by omega) rfl (pre_of_ne hS.imports (by omega) (by omega) a)
    (fun _ _ he hv res hr => by
      obtain ⟨c, rfl, x, y, h₁, h₂⟩ := car_post hS.imports he hv hr
      exact hc c x y h₁ h₂) hQ

/-- `cdr(a)`. -/
theorem R.cdr (hQ : TrapsQ Q s)
    (hc : ∀ c x y, ρ a = some (.cons x y) → ρ c = some y →
      HWP P (gameHost I (consISpec consIx ρ L)) s f (vals (us ++ [.i32 c]) ++ expression is) Q) :
    HWP P (gameHost I (consISpec consIx ρ L)) s f
      (vals (us ++ [.i32 a]) ++ expression (.call ⟨2⟩ :: is)) Q :=
  R.call hS hs hm (k := 2) (by omega) rfl (pre_of_ne hS.imports (by omega) (by omega) a)
    (fun _ _ he hv res hr => by
      obtain ⟨c, rfl, x, y, h₁, h₂⟩ := cdr_post hS.imports he hv hr
      exact hc c x y h₁ h₂) hQ

/-- `accept(a)`, for `a` denoting a member of `L`. -/
theorem R.accept (hL : ∀ t, ρ a = some t → t ∈ L) (hQ : TrapsQ Q s)
    (hc : HWP P (gameHost I (consISpec consIx ρ L)) s f (vals us ++ expression is) Q) :
    HWP P (gameHost I (consISpec consIx ρ L)) s f
      (vals (us ++ [.i32 a]) ++ expression (.call ⟨4⟩ :: is)) Q :=
  R.call hS hs hm (k := 4) (by omega) rfl (pre_accept hS.imports a hL)
    (fun _ _ he _ res hr => by
      obtain rfl := accept_post hS.imports he hr
      simpa using hc) hQ

end Calls

/-! ## The shape of a checker whose body may trap (`unreachable`) -/

mutual
/-- `ieq` (structural equality on the checkers' instructions) extended by `unreachable`. -/
def ieqR : Instr → Instr → Bool
  | .unreachable, .unreachable => true
  | .return_, .return_ => true
  | .loop bt b, .loop bt' b' => bt == bt' && ieqsR b b'
  | .if_ bt t e, .if_ bt' t' e' => bt == bt' && ieqsR t t' && ieqsR e e'
  | .br l, .br l' => l == l'
  | .call f, .call f' => f == f'
  | .localGet x, .localGet x' | .localSet x, .localSet x' => x == x'
  | .intConst t b, .intConst t' b' => t == t' && b.toNat == b'.toNat
  | .intTestOp t o, .intTestOp t' o' => t == t' && o == o'
  | .intRelOp t o, .intRelOp t' o' => t == t' && o == o'
  | _, _ => false
/-- `ieqR` on lists. -/
def ieqsR : List Instr → List Instr → Bool
  | [], [] => true
  | i :: is, i' :: is' => ieqR i i' && ieqsR is is'
  | _, _ => false
end

theorem ieqsR_sound_of {b b' : List Instr} (h : ieqsR b b' = true)
    (ih : ∀ j ∈ b, ∀ j', ieqR j j' = true → j = j') : b = b' := by
  induction b generalizing b' with
  | nil =>
    cases b' with
    | nil => rfl
    | cons j' js' => unfold ieqsR at h; simp at h
  | cons j js ihl =>
    cases b' with
    | nil => unfold ieqsR at h; simp at h
    | cons j' js' =>
      unfold ieqsR at h
      simp only [Bool.and_eq_true] at h
      rw [ih j (by simp) j' h.1, ihl h.2 (fun k hk => ih k (by simp [hk]))]

theorem ieqR_sound_lt : ∀ (n : Nat) (i i' : Instr), sizeOf i < n → ieqR i i' = true → i = i'
  | 0, _, _, hs, _ => absurd hs (Nat.not_lt_zero _)
  | n + 1, i, i', hs, h => by
    have hlist : ∀ b b' : List Instr, sizeOf b < n → ieqsR b b' = true → b = b' :=
      fun b _ hb hbb => ieqsR_sound_of hbb fun j hj j' =>
        ieqR_sound_lt n j j' (by have := List.sizeOf_lt_of_mem hj; omega)
    unfold ieqR at h
    split at h
    all_goals (try simp only [Bool.and_eq_true, beq_iff_eq] at h)
    all_goals first
      | rfl
      | (subst h; rfl)
      | (obtain ⟨rfl, rfl⟩ := h; rfl)
      | (simp at h; done)
      | (obtain ⟨⟨rfl, h2⟩, h3⟩ := h; simp only [Instr.if_.sizeOf_spec] at hs;
         rw [hlist _ _ (by omega) h2, hlist _ _ (by omega) h3])
      | (obtain ⟨rfl, h2⟩ := h; simp only [Instr.loop.sizeOf_spec] at hs;
         rw [hlist _ _ (by omega) h2])
      | (obtain ⟨rfl, h2⟩ := h; rw [BitVec.eq_of_toNat_eq h2])
      | (obtain ⟨rfl, -⟩ := h; cases ‹IntTestOp›; cases ‹IntTestOp›; rfl)

theorem ieqsR_sound {is is' : List Instr} (h : ieqsR is is' = true) : is = is' :=
  ieqsR_sound_of h fun _ _ _ => ieqR_sound_lt _ _ _ (Nat.lt_succ_self _)

/-- `fnOk` with `ieqsR`. -/
def fnOkR (locals : List ValType) (body : List Instr) (D : List (Option Val))
    (fi : FuncInst Nat) : Bool :=
  (match fi.code with
    | .wasm c => c.locals == locals && ieqsR c.body body
    | _ => false) &&
  (match fi.type.expand? with
    | some (.func ps rs) => ps.length == 1 && rs.length == 0
    | _ => false) &&
  fi.module.funcs == [0, 1, 2, 3, 4, 5] &&
  locals.map (fun t => defaultVal? ((liftVal t).substAll (fi.module.types.map .dt))) == D

/-- `shapeOk` with `fnOkR`. -/
def shapeOkR (I : ScalarInstance) (locals : List ValType) (body : List Instr)
    (D : List (Option Val)) : Bool :=
  I.imports == consFTs && I.exports == [aFT] && I.addrs == [5] &&
  match I.store.funcs with
  | [f₀, f₁, f₂, f₃, f₄, f₅] => stubOk 0 f₀ && stubOk 1 f₁ && stubOk 2 f₂ && stubOk 3 f₃ &&
      stubOk 4 f₄ && fnOkR locals body D f₅
  | _ => false

theorem fnOkR_spec {locals : List ValType} {body : List Instr} {D : List (Option Val)}
    {fi : FuncInst Nat} (h : fnOkR locals body D fi = true) :
    ∃ (code : Func) (ps rs : Ty (.list .val)),
    fi.code = .wasm code ∧ code.locals = locals ∧ code.body = body ∧
    Expand fi.type (.func ps rs) ∧ ps.length = 1 ∧ rs.length = 0 ∧
    fi.module.funcs = [0, 1, 2, 3, 4, 5] ∧
    locals.map (fun t => defaultVal? ((liftVal t).substAll (fi.module.types.map .dt))) = D := by
  unfold fnOkR at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩ := h
  split at h₁
  · rename_i c hc
    split at h₂
    · rename_i ps rs he
      simp only [Bool.and_eq_true, beq_iff_eq] at h₁ h₂ h₃ h₄
      exact ⟨c, ps, rs, hc, h₁.1, ieqsR_sound h₁.2, Expand.iff.2 he, h₂.1, h₂.2, h₃, h₄⟩
    · cases h₂
  · cases h₁

theorem Shape.of_okR {I : ScalarInstance} {locals : List ValType} {body : List Instr}
    {D : List (Option Val)} (h : shapeOkR I locals body D = true) : Shape I locals body D := by
  unfold shapeOkR at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hi, he⟩, ha⟩, hf⟩ := h
  split at hf
  · rename_i f₀ f₁ f₂ f₃ f₄ f₅ hfs
    simp only [Bool.and_eq_true] at hf
    obtain ⟨⟨⟨⟨⟨h₀, h₁⟩, h₂⟩, h₃⟩, h₄⟩, h₅⟩ := hf
    refine ⟨hi, he, fun j => ?_, fun k hk => ?_, ?_⟩
    · have hl : I.exports.length = 1 := by rw [he]; rfl
      have hj : j.val = 0 := by have := j.2; omega
      simp [ScalarInstance.addr, ha, hj]
    · rcases k with _ | _ | _ | _ | _ | k
      · obtain ⟨ps, rs, h⟩ := stubOk_spec h₀; exact ⟨f₀, ps, rs, by simp [hfs], h⟩
      · obtain ⟨ps, rs, h⟩ := stubOk_spec h₁; exact ⟨f₁, ps, rs, by simp [hfs], h⟩
      · obtain ⟨ps, rs, h⟩ := stubOk_spec h₂; exact ⟨f₂, ps, rs, by simp [hfs], h⟩
      · obtain ⟨ps, rs, h⟩ := stubOk_spec h₃; exact ⟨f₃, ps, rs, by simp [hfs], h⟩
      · obtain ⟨ps, rs, h⟩ := stubOk_spec h₄; exact ⟨f₄, ps, rs, by simp [hfs], h⟩
      · omega
    · obtain ⟨c, ps, rs, h⟩ := fnOkR_spec h₅
      exact ⟨f₅, c, ps, rs, by simp [hfs], h⟩
  · cases hf

end Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.RecFull
