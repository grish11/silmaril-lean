module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.RecFull.Sat
public import Silmaril.Wasm.Logic.Total.Thms
public import Silmaril.Wasm.Logic.OpenTotal.Thms

/-!
# `recFullCheck` terminates: total correctness

The partial-correctness proof of `recFullCheck` (`RecFull.Sat`) is redone in the
total-correctness logic (`Silmaril.Wasm.Logic.Hoare.TWP`, `Silmaril.Wasm.Logic.Total`) under the
most general **terminating** environment of the cons reader specification (`gameHostT`):

* the rules `T.*`: straight-line instructions (the mode-generic `Wp` rules at `.total`), `if`
  and the end of a block (`TWP.if_`, `TWP.block`), `return`, `br 0`, and **the loop with a
  variant** (`T.loop`, from `TWP.loop`);
* the import calls (`twp_importT`, `RT.kind`, `RT.car`, `RT.cdr`, `RT.accept`) through the total
  stub rule `OpenTotal.TFSpecAt.stub`; its liveness obligation (every allowed call has an
  allowed answer) holds because a trapping answer decodes to no read (`cons_live`);
* the recursive call (`RT.self`) through the total call rule `TSafe.callIdx`;
* the spine loop terminates with the variant `rfV ρ f`, the number of cons cells of the tree
  that the cursor (local `1`) denotes: every branch back follows a `cdr`, so the variant drops
  from `rfSize (cons x y)` to `rfSize y`;
* `rf_validT`: the internal call meets `rfSpec ρ B` **totally**, by induction on `B` (the
  recursive calls are on strictly smaller elements), and `recFullCheck_tsat`: the export meets
  the cons reader specification for `recProperL` totally (`TGameSat`), in every environment
  `ρ` and profile.

Every fixed environment `ρ : Env (BitVec 32) (SExp2 (BitVec 64))` is well founded for this
purpose: it maps handles to finite trees, and correct `car`/`cdr` answers name the subtrees.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.RecFull

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.GameLink
  Silmaril.Formats Silmaril.Wasm.Game.HandleAccept Silmaril.Wasm.Game.HandleAccept.Checkers
  Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers
open Silmaril.Wasm.Logic.Strategy (ISpec resultOutcome)
open Silmaril.Wasm.Logic.Core (Outcome Post)

section Rules

variable {P : Profile} {host : HostSemantics Nat} {s : Store Nat} {f : Frame} {us : List Val}
  {is : List Instr} {Q : Post Nat}

/-! ## Total rules -/

theorem T.localGet {x : LocalIdx} {v : Val} (hv : f.local? x = some (some v))
    (h : TWP P host s f (vals (us ++ [v]) ++ expression is) Q) :
    TWP P host s f (vals us ++ expression (.localGet x :: is)) Q :=
  Wp.localGet (m := .total) hv h

theorem T.localSet {x : LocalIdx} {v : Val} (hx : x.toNat < f.locals.length)
    (h : TWP P host s (f.setLocal x v) (vals us ++ expression is) Q) :
    TWP P host s f (vals (us ++ [v]) ++ expression (.localSet x :: is)) Q :=
  Wp.localSet (m := .total) hx h

theorem T.i32Const {c : BitVec 32}
    (h : TWP P host s f (vals (us ++ [.i32 c]) ++ expression is) Q) :
    TWP P host s f (vals us ++ expression (.intConst .i32 c :: is)) Q := by
  simpa [vals, expression, Val.i32, Val.toAdmin] using h

theorem T.eqz {c : BitVec 32}
    (h : TWP P host s f (vals (us ++ [.i32 (bool32 (c == 0))]) ++ expression is) Q) :
    TWP P host s f (vals (us ++ [.i32 c]) ++ expression (.intTestOp .i32 .eqz :: is)) Q :=
  Wp.intTestOp (m := .total) (t := .i32) (x := c) h

theorem T.neConst {x y : BitVec 32}
    (h : TWP P host s f (vals (us ++ [.i32 (bool32 (x != y))]) ++ expression is) Q) :
    TWP P host s f (vals (us ++ [.i32 x]) ++
      expression (.intConst .i32 y :: .intRelOp .i32 .ne :: is)) Q := by
  refine T.i32Const ?_
  rw [List.append_assoc]
  exact Wp.intRelOp (m := .total) (t := .i32) (x := x) (y := y) h

theorem T.return_ (hq : Q s f (.ret us)) :
    TWP P host s f (vals us ++ expression (.return_ :: is)) Q :=
  TSafe.exit (.ret us) ⟨_, rfl⟩ hq

theorem T.br0 (hq : Q s f (.br 0 us)) :
    TWP P host s f (vals us ++ expression (.br ⟨0⟩ :: is)) Q :=
  Wp.br (m := .total) (l := ⟨0⟩) hq

theorem T.unreachable (hq : Q s f .trap) :
    TWP P host s f (vals us ++ expression (.unreachable :: is)) Q :=
  Wp.unreachable (m := .total) hq

/-- The end of a block body of type `[] → []`. -/
theorem T.blockEnd (h : TWP P host s f (vals us ++ expression is) Q) :
    TWP P host s f (vals [] ++ expression [])
      (labelPostT P host 0 [] us (seqPostT P host (expression is) Q)) := by
  refine TSafe.exit (.normal []) rfl ?_
  show TSafe P host Q ⟨s, f, vals (us ++ []) ++ expression is⟩
  rw [List.append_nil]
  exact h

/-- `if` with an empty `else`, both of block type `[] → []`. -/
theorem T.if_ {c : BitVec 32} {b : List Instr}
    (h₁ : c ≠ 0 → TWP P host s f (vals [] ++ expression b)
      (labelPostT P host 0 [] us (seqPostT P host (expression is) Q)))
    (h₂ : c = 0 → TWP P host s f (vals us ++ expression is) Q) :
    TWP P host s f (vals (us ++ [.i32 c]) ++ expression (.if_ .empty b [] :: is)) Q := by
  refine TWP.if_ ?_
  by_cases hc : c = 0
  · simp only [ne_eq, hc, not_true_eq_false, ↓reduceIte]
    have hb := TWP.block (P := P) (host := host) (us := us) (vs := []) (bt := .empty) (t₁ := [])
      (t₂ := []) (f := f) (rest := expression is) (body := []) rfl rfl (T.blockEnd (h₂ hc))
    rwa [List.append_nil] at hb
  · simp only [ne_eq, hc, not_false_eq_true, ↓reduceIte]
    have hb := TWP.block (P := P) (host := host) (us := us) (vs := []) (bt := .empty) (t₁ := [])
      (t₂ := []) (f := f) (rest := expression is) rfl rfl (h₁ hc)
    rwa [List.append_nil] at hb

/-- **A loop of block type `[] → []` with an invariant and a variant** on the store and frame. -/
theorem T.loop {Inv : Store Nat → Frame → Prop} {V : Store Nat → Frame → Nat}
    {body : List Instr}
    (hbody : ∀ s f, Inv s f → TWP P host s f (vals [] ++ expression body)
      (loopPostT 0 [] (fun s f vs => vs = [] ∧ Inv s f) (fun s f _ => V s f) (V s f) Q))
    (hi : Inv s f) : TWP P host s f (vals [] ++ expression [.loop .empty body]) Q :=
  TWP.loop (us := []) (vs := []) (t₁ := []) (t₂ := [])
    (Inv := fun s f vs => vs = [] ∧ Inv s f) (V := fun s f _ => V s f)
    (fun _ _ _ _ => rfl) (fun _ _ _ h => by rw [h.1]; rfl)
    (fun s f vs h => by obtain ⟨rfl, h⟩ := h; exact hbody s f h) ⟨rfl, hi⟩

theorem TrapsQ.loopT {Inv : Store Nat → Frame → List Val → Prop}
    {V : Store Nat → Frame → List Val → Nat} {v : Nat} (h : TrapsQ Q s) :
    TrapsQ (loopPostT 0 [] Inv V v Q) s := fun f => ⟨(h f).1, (h f).2⟩

theorem TrapsQ.labelT {rest : List Admin} (h : TrapsQ Q s) :
    TrapsQ (labelPostT P host 0 [] us (seqPostT P host rest Q)) s := fun f =>
  ⟨(h f).1, (h f).2⟩

theorem RetQ.loopT {Inv : Store Nat → Frame → List Val → Prop}
    {V : Store Nat → Frame → List Val → Nat} {v : Nat} (h : RetQ Q s) :
    RetQ (loopPostT 0 [] Inv V v Q) s := fun f => h f

theorem RetQ.labelT {rest : List Admin} (h : RetQ Q s) :
    RetQ (labelPostT P host 0 [] [] (seqPostT P host rest Q)) s := fun f => h f

end Rules

/-! ## Import calls under the terminating environment -/

section Import

variable {P : Profile} {s : Store Nat} {f : Frame} {us : List Val} {is : List Instr}
  {Q : Post Nat} {I : ScalarInstance}
  {ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))} {L : Set (SExp2 (BitVec 64))}

/-- **Liveness of the cons reader specification**: a trapping answer is always allowed. -/
theorem cons_live (k : Nat) (s : Store Nat) (args : List Val) :
    ∃ s' r, (importSpec I (consISpec (ts := I.imports) consIx ρ L) k).post s args s'
      (resultOutcome r) :=
  ⟨s, .trap, rfl, fun e _ => ⟨.trap, fun q a hd => by simp [consDecAns, ansVals] at hd, rfl⟩⟩

/-- A call of import `k`, for a postcondition accepting traps and exceptions. -/
theorem twp_importT {x : FuncIdx} {k : Nat} {fk : FuncInst Nat} {ps rs : Ty (.list .val)}
    {args : List Val}
    (hx : f.module.funcs[x.toNat]? = some k) (hf : s.funcs[k]? = some fk)
    (hcode : fk.code = .host k)
    (he : Expand fk.type (.func ps rs)) (hps : ps.length = args.length)
    (hop : ∃ e, I.importOp? k args = some e ∧ (consISpec (ts := I.imports) consIx ρ L).pre e)
    (hk : ∀ e (v : I.E.Ar e), I.importOp? k args = some e →
      (consISpec (ts := I.imports) consIx ρ L).post e v →
      ∀ res, Answer.toResult (ft := I.imports.get e.1) v = .values res →
        TWP P (gameHostT I (consISpec consIx ρ L)) s f (vals (us ++ res) ++ expression is) Q)
    (hQ : TrapsQ Q s) :
    TWP P (gameHostT I (consISpec consIx ρ L)) s f
      (vals (us ++ args) ++ expression (.call x :: is)) Q := by
  have hS : importCtx I (consISpec (ts := I.imports) consIx ρ L) (id k) =
      some (importSpec I (consISpec consIx ρ L) k) := rfl
  refine TSafe.callIdx (x := x)
    (S := Silmaril.Wasm.Logic.Open.stubSpec k k (importSpec I (consISpec consIx ρ L) k)) hx hf
    (Silmaril.Wasm.Logic.OpenTotal.TFSpecAt.stub hS fun s args _ => cons_live k s args)
    ⟨⟨fk, ps, rs, hf, hcode, he, hps.symm⟩, hop⟩ ?_
  rintro s' o ⟨-, ⟨res, rfl, hR⟩ | ⟨rfl, hR⟩ | ⟨y, rfl, hR⟩⟩
  · obtain ⟨rfl, hall⟩ := hR
    obtain ⟨e, he', -⟩ := hop
    obtain ⟨v, hv, ho⟩ := hall e he'
    have hr : Answer.toResult (ft := I.imports.get e.1) v = .values res := by
      revert ho
      cases v <;> simp [Answer.toResult, resultOutcome]
    exact hk e v he' hv res hr
  · obtain ⟨rfl, -⟩ := hR
    exact (hQ f).1
  · obtain ⟨rfl, -⟩ := hR
    exact (hQ f).2 y

variable {locals : List ValType} {body : List Instr} {D : List (Option Val)}
  (hS : Shape I locals body D) (hs : s.funcs = I.store.funcs)
  (hm : f.module.funcs = [0, 1, 2, 3, 4, 5]) {a : BitVec 32}

include hS hs hm

/-- A call of import `k < 5` by an instantiated checker. -/
theorem RT.call {k : Nat} (hk : k < 5) {x : FuncIdx} (hx : x.toNat = k)
    (hop : ∃ e, I.importOp? k [.i32 a] = some e ∧ (consISpec (ts := I.imports) consIx ρ L).pre e)
    (hc : ∀ e (v : I.E.Ar e), I.importOp? k [.i32 a] = some e →
      (consISpec (ts := I.imports) consIx ρ L).post e v →
      ∀ res, Answer.toResult (ft := I.imports.get e.1) v = .values res →
        TWP P (gameHostT I (consISpec consIx ρ L)) s f (vals (us ++ res) ++ expression is) Q)
    (hQ : TrapsQ Q s) :
    TWP P (gameHostT I (consISpec consIx ρ L)) s f
      (vals (us ++ [.i32 a]) ++ expression (.call x :: is)) Q := by
  obtain ⟨fk, ps, rs, hf, hcode, he, hps⟩ := hS.stub k hk
  refine twp_importT (fk := fk) (ps := ps) (rs := rs) ?_ (by rw [hs]; exact hf) hcode he
    (by simp [hps]) hop hc hQ
  rw [hm, hx]
  rcases k with _ | _ | _ | _ | _ | k <;> first | rfl | omega

/-- `kind(a)`. -/
theorem RT.kind (hQ : TrapsQ Q s)
    (hc : ∀ c, ((c = 0 ∧ ρ a = some .nil) ∨ (c = 1 ∧ ∃ w, ρ a = some (.atom w)) ∨
      (c = 2 ∧ ∃ x y, ρ a = some (.cons x y))) →
      TWP P (gameHostT I (consISpec consIx ρ L)) s f (vals (us ++ [.i32 c]) ++ expression is) Q) :
    TWP P (gameHostT I (consISpec consIx ρ L)) s f
      (vals (us ++ [.i32 a]) ++ expression (.call ⟨0⟩ :: is)) Q :=
  RT.call hS hs hm (k := 0) (by omega) rfl (pre_of_ne hS.imports (by omega) (by omega) a)
    (fun _ _ he hv res hr => by
      obtain ⟨c, rfl, h⟩ := kind_post hS.imports he hv hr
      exact hc c h) hQ

/-- `car(a)`. -/
theorem RT.car (hQ : TrapsQ Q s)
    (hc : ∀ c x y, ρ a = some (.cons x y) → ρ c = some x →
      TWP P (gameHostT I (consISpec consIx ρ L)) s f (vals (us ++ [.i32 c]) ++ expression is) Q) :
    TWP P (gameHostT I (consISpec consIx ρ L)) s f
      (vals (us ++ [.i32 a]) ++ expression (.call ⟨1⟩ :: is)) Q :=
  RT.call hS hs hm (k := 1) (by omega) rfl (pre_of_ne hS.imports (by omega) (by omega) a)
    (fun _ _ he hv res hr => by
      obtain ⟨c, rfl, x, y, h₁, h₂⟩ := car_post hS.imports he hv hr
      exact hc c x y h₁ h₂) hQ

/-- `cdr(a)`. -/
theorem RT.cdr (hQ : TrapsQ Q s)
    (hc : ∀ c x y, ρ a = some (.cons x y) → ρ c = some y →
      TWP P (gameHostT I (consISpec consIx ρ L)) s f (vals (us ++ [.i32 c]) ++ expression is) Q) :
    TWP P (gameHostT I (consISpec consIx ρ L)) s f
      (vals (us ++ [.i32 a]) ++ expression (.call ⟨2⟩ :: is)) Q :=
  RT.call hS hs hm (k := 2) (by omega) rfl (pre_of_ne hS.imports (by omega) (by omega) a)
    (fun _ _ he hv res hr => by
      obtain ⟨c, rfl, x, y, h₁, h₂⟩ := cdr_post hS.imports he hv hr
      exact hc c x y h₁ h₂) hQ

/-- `accept(a)`, for `a` denoting a member of `L`. -/
theorem RT.accept (hL : ∀ t, ρ a = some t → t ∈ L) (hQ : TrapsQ Q s)
    (hc : TWP P (gameHostT I (consISpec consIx ρ L)) s f (vals us ++ expression is) Q) :
    TWP P (gameHostT I (consISpec consIx ρ L)) s f
      (vals (us ++ [.i32 a]) ++ expression (.call ⟨4⟩ :: is)) Q :=
  RT.call hS hs hm (k := 4) (by omega) rfl (pre_accept hS.imports a hL)
    (fun _ _ he _ res hr => by
      obtain rfl := accept_post hS.imports he hr
      simpa using hc) hQ

end Import

/-! ## The variant -/

/-- **The variant of the spine loop**: the number of cons cells of the tree the cursor
(local `1`) denotes (`0` when it denotes none). -/
noncomputable def rfV (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))
    (f : Frame) : Nat :=
  open Classical in
  if h : ∃ c t, f.locals[1]? = some (some (Val.i32 c)) ∧ ρ c = some t then
    rfSize (Classical.choose (Classical.choose_spec h))
  else 0

theorem rfV_eq (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))
    (h cur k e : BitVec 32) (mi : ModuleInst) {t : SExp2 (BitVec 64)} (ht : ρ cur = some t) :
    rfV ρ ⟨[some (.i32 h), some (.i32 cur), some (.i32 k), some (.i32 e)], mi⟩ = rfSize t := by
  have hex : ∃ c t, ([some (Val.i32 h), some (.i32 cur), some (.i32 k), some (.i32 e)] :
      List (Option Val))[1]? = some (some (Val.i32 c)) ∧ ρ c = some t := ⟨cur, t, rfl, ht⟩
  unfold rfV
  split
  · rename_i hex'
    obtain ⟨h1, h2⟩ := Classical.choose_spec (Classical.choose_spec hex')
    have h1' : Val.i32 cur = Val.i32 (Classical.choose hex') := by simpa using h1
    have hc := i32_singleton_inj (congrArg (fun v => [v]) h1')
    rw [hc] at ht
    rw [Option.some.inj (h2.symm.trans ht)]
  · exact absurd hex ‹_›

/-! ## The body, totally -/

variable {P : Profile} {ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))}

section Body

variable {s : Store Nat} (hs : s.funcs = rfI.store.funcs) {mi : ModuleInst}
  (hm : mi.funcs = [0, 1, 2, 3, 4, 5]) {B : Nat}
  (hB : TFSpecAt P (gameHostT rfI (consISpec consIx ρ recProperL)) 5 (rfSpec ρ B))
  {h : BitVec 32} {Q : Post Nat} (hQ : TrapsQ Q s) (hR : Good ρ recProperL h → RetQ Q s)

include hs hB in
/-- The recursive call on an element denoting a tree of size below `B`. -/
theorem RT.self {f : Frame} {us : List Val} {is : List Instr} {Q' : Post Nat}
    (hQ' : TrapsQ Q' s) {e : BitVec 32} {x : SExp2 (BitVec 64)}
    (hmf : f.module.funcs = [0, 1, 2, 3, 4, 5]) (he : ρ e = some x) (hx : rfSize x < B)
    (hk : x ∈ recProperL →
      TWP P (gameHostT rfI (consISpec consIx ρ recProperL)) s f (vals us ++ expression is) Q') :
    TWP P (gameHostT rfI (consISpec consIx ρ recProperL)) s f
      (vals (us ++ [.i32 e]) ++ expression (.call ⟨5⟩ :: is)) Q' := by
  obtain ⟨fi, code, ps, rs, hf, -⟩ := rf_shape.fn
  refine TSafe.callIdx (x := ⟨5⟩) (a := 5) (fi := fi) (by rw [hmf]; rfl) (by rw [hs]; exact hf)
    hB ⟨hs, e, rfl, x, he, hx⟩ ?_
  rintro s' o ⟨-, ⟨res, rfl, ⟨rfl, hpost⟩⟩ | ⟨rfl, ⟨rfl, -⟩⟩ | ⟨y, rfl, ⟨rfl, -⟩⟩⟩
  · obtain ⟨rfl, hg⟩ := hpost res rfl
    show TSafe _ _ _ ⟨_, _, vals (us ++ []) ++ expression is⟩
    rw [List.append_nil]
    exact hk (hg e rfl x he)
  · exact (hQ' f).1
  · exact (hQ' f).2 y

include hs hm hB hQ hR

/-- The loop body, with the variant. -/
theorem rf_loopT {cur k e : BitVec 32} (hc : ∀ t, ρ cur = some t → rfSize t < B + 1)
    (hg : Good ρ recProperL cur → Good ρ recProperL h) :
    TWP P (gameHostT rfI (consISpec consIx ρ recProperL)) s
      ⟨[some (.i32 h), some (.i32 cur), some (.i32 k), some (.i32 e)], mi⟩
      (vals [] ++ expression (rfHead ++ rfElem))
      (loopPostT 0 [] (fun s' f vs => vs = [] ∧ RFInv ρ B s h mi s' f)
        (fun _ f _ => rfV ρ f)
        (rfV ρ ⟨[some (.i32 h), some (.i32 cur), some (.i32 k), some (.i32 e)], mi⟩) Q) := by
  have hL : TrapsQ (loopPostT 0 [] (fun s' f vs => vs = [] ∧ RFInv ρ B s h mi s' f)
      (fun _ f _ => rfV ρ f)
      (rfV ρ ⟨[some (.i32 h), some (.i32 cur), some (.i32 k), some (.i32 e)], mi⟩) Q) s :=
    hQ.loopT
  have hS := rf_shape
  simp only [rfHead, rfElem, List.cons_append, List.nil_append]
  refine T.localGet (v := .i32 cur) rfl ?_
  refine RT.kind hS hs hm hL (fun k' hk => ?_)
  refine T.localSet (by simp [Idx.toNat]) ?_
  refine T.localGet (v := .i32 k') rfl ?_
  refine T.eqz ?_
  refine T.if_ (fun h0 => ?_) (fun h0 => ?_)
  · -- nil: accept `h` and return
    have hk0 : k' = 0 := by simpa using bool32_ne_zero h0
    have hnil : ρ cur = some .nil := by
      rcases hk with ⟨-, hn⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact hn
      · exact absurd hk0 (by decide)
      · exact absurd hk0 (by decide)
    have hgh : Good ρ recProperL h := hg fun t ht => by
      rw [hnil] at ht
      cases ht
      exact .nil
    refine T.localGet (v := .i32 h) rfl ?_
    refine RT.accept hS hs hm hgh hL.labelT ?_
    exact T.return_ (((hR hgh).loopT).labelT _)
  · refine T.localGet (v := .i32 k') rfl ?_
    refine T.neConst ?_
    refine T.if_ (fun _ => T.unreachable (us := []) (hL.labelT _).1) (fun h2 => ?_)
    -- a cons cell: the element
    refine T.localGet (v := .i32 cur) rfl ?_
    refine RT.car hS hs hm hL (fun e' x y hcur he' => ?_)
    have hsz := hc _ hcur
    simp only [rfSize] at hsz
    refine T.localSet (by simp [Frame.setLocal, Idx.toNat]) ?_
    have adv : SExp2.IsProper x →
        TWP P (gameHostT rfI (consISpec consIx ρ recProperL)) s
          ⟨[some (.i32 h), some (.i32 cur), some (.i32 k'), some (.i32 e')], mi⟩
          (vals [] ++ expression [.localGet ⟨1⟩, .call ⟨2⟩, .localSet ⟨1⟩, .br ⟨0⟩])
          (loopPostT 0 [] (fun s' f vs => vs = [] ∧ RFInv ρ B s h mi s' f)
            (fun _ f _ => rfV ρ f)
            (rfV ρ ⟨[some (.i32 h), some (.i32 cur), some (.i32 k), some (.i32 e)], mi⟩) Q) := by
      intro hx
      refine T.localGet (v := .i32 cur) rfl ?_
      refine RT.cdr (us := []) hS hs hm hL (fun c' x' y' hcur' hc' => ?_)
      refine T.localSet (by simp [Idx.toNat]) ?_
      rw [hcur] at hcur'
      obtain ⟨rfl, rfl⟩ := SExp2.cons.inj (Option.some.inj hcur')
      refine T.br0 ⟨[], [], rfl, rfl, ⟨rfl, rfl, c', k', e', rfl,
        fun t ht => ?_, fun hg' => hg fun t ht => ?_⟩, ?_⟩
      · rw [hc'] at ht
        cases ht
        omega
      · rw [hcur] at ht
        cases ht
        rcases hx with hx | hx
        · exact .cons hx (hg' _ hc')
        · exact .cons hx (hg' _ hc')
      · show rfV ρ ⟨[some (.i32 h), some (.i32 c'), some (.i32 k'), some (.i32 e')], mi⟩ <
          rfV ρ ⟨[some (.i32 h), some (.i32 cur), some (.i32 k), some (.i32 e)], mi⟩
        rw [rfV_eq ρ h c' k' e' mi hc', rfV_eq ρ h cur k e mi hcur]
        simp only [rfSize]
        omega
    refine T.localGet (v := .i32 e') rfl ?_
    refine RT.kind hS hs hm hL (fun k₂ hk₂ => ?_)
    refine T.neConst ?_
    refine T.if_ (fun h1 => ?_) (fun h1 => ?_)
    · -- not an atom: check it recursively
      refine T.localGet (v := .i32 e') rfl ?_
      refine RT.self hs hB (us := []) hL.labelT hm he' (by omega) (fun hxp => ?_)
      exact T.blockEnd (adv (.inr hxp))
    · -- an atom
      have hk1 : k₂ = 1 := bne_eq_false_iff_eq.1 (bool32_eq_zero h1)
      obtain ⟨w, hw⟩ : ∃ w, ρ e' = some (.atom w) := by
        rcases hk₂ with ⟨rfl, -⟩ | ⟨-, hw⟩ | ⟨rfl, -⟩
        · exact absurd hk1 (by decide)
        · exact hw
        · exact absurd hk1 (by decide)
      obtain rfl : x = .atom w := Option.some.inj (he'.symm.trans hw)
      exact adv (.inl (.atom w))

/-- The body of the function, from the frame of a call on `h`. -/
theorem rf_bodyT (hh : ∀ t, ρ h = some t → rfSize t < B + 1) :
    TWP P (gameHostT rfI (consISpec consIx ρ recProperL)) s
      ⟨some (.i32 h) :: [some (.i32 0), some (.i32 0), some (.i32 0)], mi⟩
      (vals [] ++ expression rfBody) Q := by
  refine T.localGet (v := .i32 h) rfl ?_
  refine T.localSet (by simp [Idx.toNat]) ?_
  exact T.loop (Inv := RFInv ρ B s h mi) (V := fun _ f => rfV ρ f)
    (fun s' f hI => by
      obtain ⟨rfl, cur, k, e, rfl, hc, hg⟩ := hI
      exact rf_loopT hs hm hB hQ hR hc hg) ⟨rfl, h, 0, 0, rfl, hh, id⟩

end Body

/-- **The internal call meets `rfSpec … B` totally** for every bound `B`. -/
theorem rf_validT (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))) :
    ∀ B, TFSpecAt P (gameHostT rfI (consISpec consIx ρ recProperL)) 5 (rfSpec ρ B)
  | 0 => fun _ _ hpre => by
    obtain ⟨-, _, -, _, -, ht⟩ := hpre
    exact absurd ht (Nat.not_lt_zero _)
  | B + 1 => by
    have ih := rf_validT ρ B
    obtain ⟨fi, code, ps, rs, hf, hcode, hloc, hbod, he, hps, hrs, hm, hD⟩ := rf_shape.fn
    refine TFSpecAt.of_body (fi := fi) (fun s args hpre => by rw [hpre.1]; exact hf) hcode he
      (fun s args hpre => ?_) (fun s args hpre f₀ vs₀ => ?_)
    · obtain ⟨-, h, rfl, -⟩ := hpre
      simp [hps]
    · obtain ⟨hs, h, rfl, t, ht, hlt⟩ := hpre
      have hfr : Frame.forCall fi.module [.i32 h] code.locals =
          ⟨some (.i32 h) :: [some (.i32 0), some (.i32 0), some (.i32 0)], fi.module⟩ := by
        unfold Frame.forCall
        rw [hloc, hD]
        rfl
      rw [hfr, hbod]
      refine rf_bodyT hs hm ih (fun F => ⟨?_, fun a => ?_⟩) (fun hg F => ?_)
        (fun t' ht' => by rw [ht] at ht'; cases ht'; exact hlt)
      · exact ⟨rfl, .inr (.inl ⟨rfl, rfl, fun _ h => by cases h⟩)⟩
      · exact ⟨rfl, .inr (.inr ⟨a, rfl, rfl, fun _ h => by cases h⟩)⟩
      · refine ⟨[], [], by simp, by simp [hrs], rfl, .inl ⟨[], by simp, rfl, fun res hres => ?_⟩⟩
        cases hres
        exact ⟨rfl, fun h' hh' => by obtain rfl := i32_singleton_inj hh'; exact hg⟩

/-- **`recFullCheck` meets the cons reader specification for `recProperL` totally** in every
environment and every profile. -/
theorem recFullCheck_tsat (P : Profile)
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))) :
    TGameSat P rfI (StoreInv rfI) (consISpec consIx ρ recProperL) (topISpec _) := by
  intro j
  rw [rf_shape.addr j]
  obtain ⟨fi, code, ps, rs, hf, hcode, hloc, hbod, he, hps, hrs, hm, hD⟩ := rf_shape.fn
  refine TFSpecAt.of_body (fi := fi) (fun s args hpre => by rw [hpre.1]; exact hf) hcode he
    (fun s args hpre => ?_) (fun s args hpre f₀ vs₀ => ?_)
  · obtain ⟨-, ht, -⟩ := hpre
    obtain ⟨h, rfl⟩ := args_of rf_shape.exports ht
    simp [hps]
  · obtain ⟨hInv, ht, -⟩ := hpre
    obtain ⟨h, rfl⟩ := args_of rf_shape.exports ht
    have hfr : Frame.forCall fi.module [.i32 h] code.locals =
        ⟨some (.i32 h) :: [some (.i32 0), some (.i32 0), some (.i32 0)], fi.module⟩ := by
      unfold Frame.forCall
      rw [hloc, hD]
      rfl
    rw [hfr, hbod]
    exact rf_bodyT (B := match ρ h with | some t => rfSize t | none => 0) hInv hm
      (rf_validT ρ _)
      (fun F => ⟨⟨rfl, .inr (.inl ⟨rfl, hInv, fun _ _ _ => trivial⟩)⟩,
        fun a => ⟨rfl, .inr (.inr ⟨a, rfl, hInv, fun _ _ _ => trivial⟩)⟩⟩)
      (fun _ F => ⟨[] ++ [], [], by simp, by simp [hrs], rfl,
        .inl ⟨[], by simp, hInv, fun _ _ _ => trivial⟩⟩)
      (fun t ht => by simp only [ht]; omega)

end Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.RecFull
