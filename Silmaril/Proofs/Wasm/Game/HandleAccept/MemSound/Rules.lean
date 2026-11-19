module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Langs
public import Silmaril.Wasm.Logic.Instr.Thms
public import Silmaril.Wasm.Logic.Memory.Thms

/-!
# Proofs: shared rules for memory-observing example modules

* the instantiation of a module, computed (`prep`) and checked by kernel evaluation
  (`prep_of_spec`: every specification instance is the computed one), with executable shape
  checks of host stubs and Wasm functions (`stubOk`, `fnOk`, instruction equality `ieqs`);
* every-run rules (`HWP`) for the instructions of the examples, and **the import call rule under
  a contract** (`hwp_call`, through `Open.FSpecAt.stub`): the call is allowed when the contract's
  precondition holds of the callout read in the current store, and every reply the contract
  admits must make the rest safe;
* `export_valid`: an export meets `exportSpec Inv a` if its body is safe from every store meeting
  `Inv`, for every postcondition accepting the body's exits in such stores;
* memory facts: what a callout observes after a store (`segment_of_store`), and the decoding of
  `symbol`, `sexp` and `accept` callouts.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post bytesAt)
open Silmaril.Wasm.Logic.Strategy (resultOutcome)

/-! ## The instantiation of a module -/

/-- The specification's preparation of a module against fresh host functions. -/
def prep (m : Module) : Option (Config Nat × Option FuncIdx) :=
  (validate? m).bind fun mt =>
    prepare? evalConst? (importStore (CExternType.funcs mt.imports)) m (importAddrs mt)

/-- Every specification instance of a module is its computed preparation. -/
theorem prep_of_spec {m : Module} {mt : CModuleType} {Is : ScalarInstance} {c₀ : Config Nat}
    (hI : IsSpecInstance m mt Is c₀) : ∃ c st, prep m = some (c, st) ∧ c₀ = c.withStart st ∧
      c.store = Is.store ∧ exportFuncAddrs c.frame.module = Is.addrs := by
  obtain ⟨c, st, hp, h1, h2, h3⟩ := hI.prepared
  exact ⟨c, st, by simp [prep, hI.valid, hp], h1, h2, h3⟩

/-! ## Executable equality of instructions -/

mutual
/-- Structural equality on the instructions of the examples; `false` elsewhere. -/
def ieq : Instr → Instr → Bool
  | .return_, .return_ => true
  | .if_ bt t e, .if_ bt' t' e' => bt == bt' && ieqs t t' && ieqs e e'
  | .call f, .call f' => f == f'
  | .localGet x, .localGet x' | .localSet x, .localSet x' => x == x'
  | .intConst t b, .intConst t' b' => t == t' && b.toNat == b'.toNat
  | .intRelOp t o, .intRelOp t' o' => t == t' && o == o'
  | .intStore t p x a, .intStore t' p' x' a' => t == t' && p == p' && x == x' && a == a'
  | .intLoad t p x a, .intLoad t' p' x' a' => t == t' && p == p' && x == x' && a == a'
  | _, _ => false
/-- `ieq` on lists. -/
def ieqs : List Instr → List Instr → Bool
  | [], [] => true
  | i :: is, i' :: is' => ieq i i' && ieqs is is'
  | _, _ => false
end

theorem ieqs_sound_of {b b' : List Instr} (h : ieqs b b' = true)
    (ih : ∀ j ∈ b, ∀ j', ieq j j' = true → j = j') : b = b' := by
  induction b generalizing b' with
  | nil =>
    cases b' with
    | nil => rfl
    | cons j' js' => unfold ieqs at h; simp at h
  | cons j js ihl =>
    cases b' with
    | nil => unfold ieqs at h; simp at h
    | cons j' js' =>
      unfold ieqs at h
      simp only [Bool.and_eq_true] at h
      rw [ih j (by simp) j' h.1, ihl h.2 (fun k hk => ih k (by simp [hk]))]

theorem ieq_sound_lt : ∀ (n : Nat) (i i' : Instr), sizeOf i < n → ieq i i' = true → i = i'
  | 0, _, _, hs, _ => absurd hs (Nat.not_lt_zero _)
  | n + 1, i, i', hs, h => by
    have hlist : ∀ b b' : List Instr, sizeOf b < n → ieqs b b' = true → b = b' :=
      fun b _ hb hbb => ieqs_sound_of hbb fun j hj j' =>
        ieq_sound_lt n j j' (by have := List.sizeOf_lt_of_mem hj; omega)
    unfold ieq at h
    split at h
    all_goals (try simp only [Bool.and_eq_true, beq_iff_eq] at h)
    all_goals first
      | rfl
      | (subst h; rfl)
      | (obtain ⟨rfl, rfl⟩ := h; rfl)
      | (obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := h; rfl)
      | (exact absurd h Bool.false_ne_true)
      | (obtain ⟨⟨rfl, h2⟩, h3⟩ := h; simp only [Instr.if_.sizeOf_spec] at hs;
         rw [hlist _ _ (by omega) h2, hlist _ _ (by omega) h3])
      | (obtain ⟨rfl, h2⟩ := h; rw [BitVec.eq_of_toNat_eq h2])

theorem ieqs_sound {is is' : List Instr} (h : ieqs is is' = true) : is = is' :=
  ieqs_sound_of h fun _ _ _ => ieq_sound_lt _ _ _ (Nat.lt_succ_self _)

/-! ## Shapes of instantiated functions -/

/-- A host stub for import `k`, with `np` parameters. -/
def stubOk (k np : Nat) (fi : FuncInst Nat) : Bool :=
  (match fi.code with
    | .host k' => k' == k
    | _ => false) &&
  (match fi.type.expand? with
    | some (.func ps _) => ps.length == np
    | _ => false)

theorem stubOk_spec {k np : Nat} {fi : FuncInst Nat} (h : stubOk k np fi = true) :
    ∃ ps rs, fi.code = .host k ∧ Expand fi.type (.func ps rs) ∧ ps.length = np := by
  unfold stubOk at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h₁, h₂⟩ := h
  split at h₁
  · rename_i k' hc
    split at h₂
    · rename_i ps rs he
      exact ⟨ps, rs, by rw [hc, beq_iff_eq.1 h₁], Expand.iff.2 he, beq_iff_eq.1 h₂⟩
    · cases h₂
  · cases h₁

/-- A Wasm function: its locals, body, numbers of parameters and results, the function and memory
addresses of its module instance, and the default values of its locals. -/
def fnOk (locals : List ValType) (body : List Instr) (np nr : Nat) (funcs mems : List Nat)
    (D : List (Option Val)) (fi : FuncInst Nat) : Bool :=
  (match fi.code with
    | .wasm c => c.locals == locals && ieqs c.body body
    | _ => false) &&
  (match fi.type.expand? with
    | some (.func ps rs) => ps.length == np && rs.length == nr
    | _ => false) &&
  fi.module.funcs == funcs && fi.module.mems == mems &&
  locals.map (fun t => defaultVal? ((liftVal t).substAll (fi.module.types.map .dt))) == D

theorem fnOk_spec {locals : List ValType} {body : List Instr} {np nr : Nat}
    {funcs mems : List Nat} {D : List (Option Val)} {fi : FuncInst Nat}
    (h : fnOk locals body np nr funcs mems D fi = true) :
    ∃ (code : Func) (ps rs : Ty (.list .val)),
    fi.code = .wasm code ∧ code.locals = locals ∧ code.body = body ∧
    Expand fi.type (.func ps rs) ∧ ps.length = np ∧ rs.length = nr ∧
    fi.module.funcs = funcs ∧ fi.module.mems = mems ∧
    locals.map (fun t => defaultVal? ((liftVal t).substAll (fi.module.types.map .dt))) = D := by
  unfold fnOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩ := h
  split at h₁
  · rename_i c hc
    split at h₂
    · rename_i ps rs he
      simp only [Bool.and_eq_true, beq_iff_eq] at h₁ h₂ h₃ h₄ h₅
      exact ⟨c, ps, rs, hc, h₁.1, ieqs_sound h₁.2, Expand.iff.2 he, h₂.1, h₂.2, h₃, h₄, h₅⟩
    · cases h₂
  · cases h₁

/-! ## Straight-line rules -/

variable {P : Profile} {host : HostSemantics Nat} {s : Store Nat} {f : Frame} {us : List Val}
  {is : List Instr} {Q : Post Nat}

theorem X.localGet {x : LocalIdx} {v : Val} (hv : f.local? x = some (some v))
    (h : HWP P host s f (vals (us ++ [v]) ++ expression is) Q) :
    HWP P host s f (vals us ++ expression (.localGet x :: is)) Q :=
  HWP.localGet hv h

theorem X.localSet {x : LocalIdx} {v : Val} (hx : x.toNat < f.locals.length)
    (h : HWP P host s (f.setLocal x v) (vals us ++ expression is) Q) :
    HWP P host s f (vals (us ++ [v]) ++ expression (.localSet x :: is)) Q :=
  HWP.localSet hx h

theorem X.i32Const {c : BitVec 32}
    (h : HWP P host s f (vals (us ++ [.i32 c]) ++ expression is) Q) :
    HWP P host s f (vals us ++ expression (.intConst .i32 c :: is)) Q := by
  simpa [vals, expression, Val.i32, Val.toAdmin] using h

theorem X.neConst {x y : BitVec 32}
    (h : HWP P host s f (vals (us ++ [.i32 (bool32 (x != y))]) ++ expression is) Q) :
    HWP P host s f (vals (us ++ [.i32 x]) ++
      expression (.intConst .i32 y :: .intRelOp .i32 .ne :: is)) Q := by
  refine X.i32Const ?_
  rw [List.append_assoc]
  exact Wp.intRelOp (m := .part) (t := .i32) (x := x) (y := y) h

theorem X.return_ (hq : Q s f (.ret us)) :
    HWP P host s f (vals us ++ expression (.return_ :: is)) Q :=
  HWP.of_exits (o := .ret us) ⟨_, rfl⟩ hq

/-- The end of the body. -/
theorem X.done (hq : Q s f (.normal us)) : HWP P host s f (vals us ++ expression []) Q :=
  HWP.of_exits (o := .normal us) (show vals us ++ expression [] = vals us by simp [expression]) hq

/-- The end of a block body of type `[] → []`. -/
theorem X.blockEnd (h : HWP P host s f (vals us ++ expression is) Q) :
    HWP P host s f (vals [] ++ expression [])
      (labelPost P host 0 [] us (seqPost P host (expression is) Q)) := by
  refine HWP.of_vals (vs := []) ?_
  show HWP P host s f (vals (us ++ []) ++ expression is) Q
  simpa using h

/-- `if` with an empty `else`, both of block type `[] → []`. -/
theorem X.if_ {c : BitVec 32} {b : List Instr}
    (h₁ : c ≠ 0 → HWP P host s f (vals [] ++ expression b)
      (labelPost P host 0 [] us (seqPost P host (expression is) Q)))
    (h₂ : c = 0 → HWP P host s f (vals us ++ expression is) Q) :
    HWP P host s f (vals (us ++ [.i32 c]) ++ expression (.if_ .empty b [] :: is)) Q := by
  refine HWP.if_ (fun hc => ?_) (fun hc => ?_)
  · have hb := HWP.block (us := us) (vs := []) (bt := .empty) (t₁ := []) (t₂ := []) (f := f)
      (rest := expression is) rfl rfl (h₁ hc)
    rwa [List.append_nil] at hb
  · have hb := HWP.block (us := us) (vs := []) (bt := .empty) (t₁ := []) (t₂ := []) (f := f)
      (rest := expression is) (body := []) rfl rfl (X.blockEnd (h₂ hc))
    rwa [List.append_nil] at hb

/-! ## Exits of a function body -/

/-- `Q` accepts every exit of a function body without results, in every store meeting `Inv`. -/
def BodyExits (Inv : Store Nat → Prop) (Q : Post Nat) : Prop :=
  ∀ s, Inv s → ∀ f, Q s f (.normal []) ∧ (∀ vs, Q s f (.ret vs)) ∧ Q s f .trap ∧
    ∀ a, Q s f (.throw a)

theorem BodyExits.label {Inv : Store Nat → Prop} {rest : List Admin} (h : BodyExits Inv Q) :
    ∀ s, Inv s → ∀ f, (∀ vs, labelPost P host 0 [] [] (seqPost P host rest Q) s f (.ret vs)) ∧
      labelPost P host 0 [] [] (seqPost P host rest Q) s f .trap ∧
      ∀ a, labelPost P host 0 [] [] (seqPost P host rest Q) s f (.throw a) := fun s hs f =>
  ⟨fun vs => (h s hs f).2.1 ([] ++ vs), (h s hs f).2.2.1, (h s hs f).2.2.2⟩

/-- **An export meets `exportSpec`** if its body is safe from every store meeting `Inv` and
arguments `$invoke` accepts, for every postcondition accepting its exits in such stores. -/
theorem export_valid {Inv : Store Nat → Prop} {a : Nat} {fi : FuncInst Nat} {code : Func}
    {ps rs : Ty (.list .val)} (hfi : ∀ s, Inv s → s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm code) (he : Expand fi.type (.func ps rs)) (hrs : rs.length = 0)
    (hbody : ∀ s args, Inv s → InvokeOk s a args → ∀ Q : Post Nat, BodyExits Inv Q →
      HWP P host s (Frame.forCall fi.module args code.locals) (vals [] ++ expression code.body) Q) :
    FSpecValid P host a (exportSpec Inv a) := by
  intro n
  cases n with
  | zero => exact fun _ _ _ _ _ _ _ => trivial
  | succ n =>
    refine FSpecAt.of_body (fi := fi) (fun s args hpre => hfi s hpre.1) hcode he
      (fun s args hpre => ?_) (fun s args hpre f₀ vs₀ => ?_)
    · obtain ⟨hInv, fi', ps', rs', hf', he', hall⟩ := hpre
      obtain rfl : fi' = fi := Option.some.inj (hf'.symm.trans (hfi s hInv))
      have hps : ps' = ps := by
        have h1 := Expand.iff.1 he
        have h2 := Expand.iff.1 he'
        rw [h1] at h2
        cases h2
        rfl
      subst hps
      exact hall.length_eq
    · refine hbody s args hpre.1 hpre.2 _ (fun s' hs' F => ?_) n
      have hR : ∀ o, (exportSpec Inv a).post s args s' o := fun _ => hs'
      refine ⟨⟨by simp [hrs], rfl, .inl ⟨[], by simp, hR _⟩⟩, fun vs => ?_,
        ⟨rfl, .inr (.inl ⟨rfl, hR _⟩)⟩, fun a => ⟨rfl, .inr (.inr ⟨a, rfl, hR _⟩)⟩⟩
      exact ⟨[] ++ vs, [], by simp, by simp [hrs], rfl, .inl ⟨[], by simp, hR _⟩⟩

/-! ## Import calls under a contract -/

section Calls

variable {X I O C : Type} {m : Module} {memAddr : Option Nat} {R : Roles X I O C}
  {K : MemContract I}

/-- **The import call rule under a contract.** -/
theorem hwp_call {x : FuncIdx} {k : Nat} {fk : FuncInst Nat} {ps rs : Ty (.list .val)}
    {args : List Val} {i : Import}
    (hx : f.module.funcs[x.toNat]? = some k) (hf : s.funcs[k]? = some fk)
    (hcode : fk.code = .host k) (he : Expand fk.type (.func ps rs)) (hn : args.length = ps.length)
    (hi : m.imports[k]? = some i) (hpre : K.pre (calloutIn i memAddr s args))
    (hk : ∀ s' r, K.reply ⟨k, s, args⟩ ⟨s', r⟩ →
      (∀ y, R.answerIn (calloutIn i memAddr s args) ⟨r, memOf memAddr s'⟩ = some y → K.ans y) →
      (∀ res, r = .values res →
        HWP P (memHost m memAddr R K) s' f (vals (us ++ res) ++ expression is) Q) ∧
      (r = .trap → Q s' f .trap) ∧ (∀ a, r = .throw a → Q s' f (.throw a))) :
    HWP P (memHost m memAddr R K) s f (vals (us ++ args) ++ expression (.call x :: is)) Q
  | 0 => trivial
  | n + 1 => by
    have hS : memCtx m memAddr R K (id k) = some (importSpec k i memAddr R K) := by
      simp [memCtx, hi]
    refine Safe.callIdx (x := x)
      (S := Silmaril.Wasm.Logic.Open.stubSpec k k (importSpec k i memAddr R K)) hx hf
      (Silmaril.Wasm.Logic.Open.FSpecAt.stub hS n) ⟨⟨fk, ps, rs, hf, hcode, he, hn⟩, hpre⟩ ?_
    rintro s' o ⟨-, ⟨res, rfl, hR⟩ | ⟨rfl, hR⟩ | ⟨y, rfl, hR⟩⟩
    · obtain ⟨r, hr, hrep, hans⟩ := hR
      obtain rfl : r = .values res := by cases r <;> simp_all [resultOutcome]
      exact (hk s' _ hrep hans).1 res rfl n
    · obtain ⟨r, hr, hrep, hans⟩ := hR
      obtain rfl : r = .trap := by cases r <;> simp_all [resultOutcome]
      exact (hk s' _ hrep hans).2.1 rfl
    · obtain ⟨r, hr, hrep, hans⟩ := hR
      obtain rfl : r = .throw y := by cases r <;> simp_all [resultOutcome]
      exact (hk s' _ hrep hans).2.2 y rfl

end Calls

/-! ## Memory observations -/

theorem readBytes_toList {B : ByteArray} {a n : Nat} (h : a + n ≤ B.size) :
    (Memory.readBytes B a n).map (·.data.toList) = some (bytesAt B ⟨a, n⟩) := by
  simp only [Memory.readBytes, h, ↓reduceIte, Option.map_some, ByteArray.data_extract,
    Array.toList_extract, List.extract_eq_take_drop, Nat.add_sub_cancel_left, bytesAt]

theorem store_inBounds {B B' : ByteArray} {a n : Nat} {w : BitVec (8 * n)}
    (h : Memory.store B a w = some B') : a + n ≤ B'.size := by
  have hs := Silmaril.Wasm.Logic.Core.size_store h
  unfold Memory.store Memory.writeBytes at h
  split at h
  · rename_i hb
    rw [Memory.encodeLE_size] at hb
    omega
  · cases h

/-- **What a callout sees after a store**: the stored bytes, little-endian. -/
theorem segment_of_store {B B' : ByteArray} {a n : Nat} {w : BitVec (8 * n)}
    (h : Memory.store B a w = some B') (o : Callout) (ho : o.mem = some B') :
    o.segment a n = some (Memory.encodeLE n w.toNat).data.toList := by
  unfold Callout.segment
  rw [ho, Option.bind_eq_bind, Option.bind_some, readBytes_toList (store_inBounds h),
    Silmaril.Wasm.Logic.Core.bytesAt_store_same h]

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound

open Silmaril.Wasm Silmaril.Wasm.Game.Accept Silmaril.Wasm.Game.IOAccept Silmaril.Accept.Handle
  Silmaril.Formats Silmaril.Formats.Api Silmaril.Wasm.Game.HandleAccept.Memory

/-! ## Decoding writer callouts -/

theorem memWrite_eq_none {ix : MemImports} {o : Callout} {w : HostReply}
    (h1 : o.imp ≠ ix.symbol) (h2 : o.imp ≠ ix.string) (h3 : o.imp ≠ ix.blob)
    (h4 : o.imp ≠ ix.sexp) : memWrite ix o w = none := by
  unfold memWrite
  cases replyI32 w <;> simp [h1, h2, h3, h4]

theorem memWrite_symbol {ix : MemImports} {o : Callout} {w : HostReply} {bs : List UInt8}
    {op : SxOp MemAtom} {args : List (BitVec 32)} {r : BitVec 32} (hi : o.imp = ix.symbol)
    (hb : o.bytes32 = some bs) (h : memWrite ix o w = some (.write op args r)) :
    ∃ str, utf8? bs = some str ∧ op = .atom ⟨.symbol, by decide, str⟩ ∧ args = [] := by
  unfold memWrite at h
  rcases hr : replyI32 w with _ | r'
  · simp [hr] at h
  · rcases hu : utf8? bs with _ | str
    · simp [hr, hi, hb, hu] at h
    · simp only [hr, hi, hb, hu, Option.bind_eq_bind, Option.bind_some, ↓reduceIte,
        Option.pure_def, Option.some.injEq, WEv.write.injEq] at h
      exact ⟨str, rfl, h.1.symm, h.2.1.symm⟩

theorem memWrite_sexp {ix : MemImports} {o : Callout} {w : HostReply}
    {op : SxOp MemAtom} {args : List (BitVec 32)} {r : BitVec 32} (hi : o.imp = ix.sexp)
    (h1 : o.imp ≠ ix.symbol) (h2 : o.imp ≠ ix.string) (h3 : o.imp ≠ ix.blob)
    (h : memWrite ix o w = some (.write op args r)) :
    op = .list ∧ handles32 o = some args ∧ replyI32 w = some r := by
  unfold memWrite at h
  rcases hr : replyI32 w with _ | r'
  · simp [hr] at h
  · simp only [hr, Option.bind_eq_bind, Option.bind_some] at h
    rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h2),
      ite_eq_right_of_eq_false _ _ (eq_false h3), ite_eq_left_of_eq_true _ _ (eq_true hi)] at h
    rcases hh : handles32 o with _ | hs
    · simp [hh] at h
    · simp only [hh, Option.bind_some, Option.pure_def, Option.some.injEq,
        WEv.write.injEq] at h
      exact ⟨h.1.symm, by rw [h.2.1], by rw [h.2.2]⟩

theorem memAccept_eq_none {ix : MemImports} {o : Callout} (h : o.imp ≠ ix.accept) :
    memAccept ix o = none := by
  simp [memAccept, h]

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound

open Silmaril.Wasm Silmaril.Wasm.Execution

theorem store_none_lt {B : ByteArray} {a n : Nat} {w : BitVec (8 * n)}
    (h : Memory.store B a w = none) : B.size < a + n := by
  unfold Memory.store Memory.writeBytes at h
  split at h
  · cases h
  · rename_i hb
    rw [Memory.encodeLE_size] at hb
    omega

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Validation Silmaril.Wasm.Game.Accept Silmaril.Wasm.Game.IOAccept
  Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api Silmaril.Wasm.Game.HandleAccept.Memory
open Silmaril.Wasm.Logic.Core (bytesAt Region)

/-! ## Decoding, forwards -/

theorem memWrite_symbol_eq {ix : MemImports} {o : Callout} {w : HostReply} {bs : List UInt8}
    {str : String} {r : BitVec 32} (hi : o.imp = ix.symbol) (hb : o.bytes32 = some bs)
    (hu : utf8? bs = some str) (hr : replyI32 w = some r) :
    memWrite ix o w = some (.write (.atom ⟨.symbol, by decide, str⟩) [] r) := by
  simp [memWrite, hr, hi, hb, hu]

theorem memWrite_sexp_eq {ix : MemImports} {o : Callout} {w : HostReply}
    {hs : List (BitVec 32)} {r : BitVec 32} (hi : o.imp = ix.sexp) (h1 : o.imp ≠ ix.symbol)
    (h2 : o.imp ≠ ix.string) (h3 : o.imp ≠ ix.blob) (hh : handles32 o = some hs)
    (hr : replyI32 w = some r) : memWrite ix o w = some (.write .list hs r) := by
  unfold memWrite
  simp only [hr, Option.bind_eq_bind, Option.bind_some]
  rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h2),
    ite_eq_right_of_eq_false _ _ (eq_false h3), ite_eq_left_of_eq_true _ _ (eq_true hi)]
  simp [hh]

theorem memAccept_inv {ix : MemImports} {o : Callout} {h h' : BitVec 32}
    (ha : o.args = [.i32 h]) (hd : memAccept ix o = some (.accept h')) : h' = h := by
  unfold memAccept at hd
  split at hd
  · simp [ha, Callout.args1, Callout.i32?, Val.i32] at hd
    exact hd.symm
  · cases hd

/-! ## Little-endian words -/

theorem le32s_encode (r : BitVec 32) (rest : List UInt8) :
    le32s ((Memory.encodeLE 4 r.toNat).data.toList ++ rest) = (le32s rest).map (r :: ·) := by
  have hl := r.isLt
  rw [Silmaril.Wasm.Logic.Core.toList_encodeLE]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons,
    List.map_nil, List.cons_append, le32s]
  congr 1
  funext hs
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, UInt8.toNat_ofNat', Nat.reducePow, Nat.reduceMul]
  omega

theorem bytesAt_append (B : ByteArray) (a n k : Nat) :
    bytesAt B ⟨a, n + k⟩ = bytesAt B ⟨a, n⟩ ++ bytesAt B ⟨a + n, k⟩ := by
  simp only [bytesAt, List.take_add, List.drop_drop]

/-! ## Stores and frames -/

theorem setMem_mems {s : Store Nat} {mi : MemInst} (hl : s.mems.length = 1) :
    (s.setMem 0 mi).mems[0]? = some mi ∧ (s.setMem 0 mi).mems.length = 1 ∧
      (s.setMem 0 mi).funcs = s.funcs := by
  simp [Store.setMem, hl]

theorem memOf_setMem {s : Store Nat} {mi : MemInst} (hl : s.mems.length = 1) :
    memOf (some 0) (s.setMem 0 mi) = some mi.bytes := by
  simp [memOf, (setMem_mems (mi := mi) hl).1]

theorem mem?_of {s : Store Nat} {F : Frame} (hF : F.module.mems = [0]) {mi : MemInst}
    (hmi : s.mems[0]? = some mi) : s.mem? F ⟨0⟩ = some (0, mi) := by
  simp only [Store.mem?, hF]
  rw [show ([0] : List Nat)[(⟨0⟩ : MemIdx).toNat]? = some 0 from rfl]
  simp [hmi]

theorem args_length {s : Store Nat} {a : Nat} {fi : FuncInst Nat} {ps rs : Ty (.list .val)}
    {args : List Val} (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
    (hok : InvokeOk s a args) : args.length = ps.length := by
  obtain ⟨fi', ps', rs', hf', he', hall⟩ := hok
  obtain rfl : fi' = fi := Option.some.inj (hf'.symm.trans hf)
  have h1 := Expand.iff.1 he
  have h2 := Expand.iff.1 he'
  rw [h1] at h2
  cases h2
  exact hall.length_eq

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post bytesAt Region)

variable {P : Profile} {host : HostSemantics Nat} {s : Store Nat} {F : Frame} {us : List Val}
  {is : List Instr} {Q : Post Nat}

/-- A packed store to memory `0` of a store with one memory: it traps, or continues in the
store holding the new bytes. -/
theorem X.storePack {sz : PackSize} {addr v : BitVec 32} (hF : F.module.mems = [0])
    (hl : s.mems.length = 1) (htrap : Q s F .trap)
    (h : ∀ mi b, s.mems[0]? = some mi →
      Memory.store mi.bytes (effAddr addr.toNat ⟨0, 0⟩) (count := sz.width / 8)
        (v.setWidth _) = some b →
      HWP P host (s.setMem 0 { mi with bytes := b }) F (vals us ++ expression is) Q) :
    HWP P host s F (vals (us ++ [.i32 addr, .i32 v]) ++
      expression (.intStore .i32 (some sz) ⟨0⟩ ⟨0, 0⟩ :: is)) Q := by
  obtain ⟨mi, hmi⟩ : ∃ mi, s.mems[0]? = some mi :=
    ⟨s.mems[0]'(by omega), List.getElem?_eq_getElem _⟩
  have hm := mem?_of hF hmi
  rcases hst : Memory.store mi.bytes (effAddr addr.toNat ⟨0, 0⟩) (count := sz.width / 8)
    (v.setWidth _) with _ | b
  · exact Wp.intStorePack_oob (m := .part) (a := .i32) (i := addr) (t := .i32) (c := v)
      hm (store_none_lt hst) htrap
  · exact Wp.intStorePack (m := .part) (a := .i32) (i := addr) (t := .i32) (c := v) hm hst
      (h mi b hmi hst)

/-- A full-width `i32` store to memory `0` of a store with one memory. -/
theorem X.store32 {addr v : BitVec 32} (hF : F.module.mems = [0])
    (hl : s.mems.length = 1) (htrap : Q s F .trap)
    (h : ∀ mi b, s.mems[0]? = some mi →
      Memory.store mi.bytes (effAddr addr.toNat ⟨0, 0⟩) (count := IntType.i32.width / 8)
        (v.setWidth _) = some b →
      HWP P host (s.setMem 0 { mi with bytes := b }) F (vals us ++ expression is) Q) :
    HWP P host s F (vals (us ++ [.i32 addr, .i32 v]) ++
      expression (.intStore .i32 none ⟨0⟩ ⟨0, 0⟩ :: is)) Q := by
  obtain ⟨mi, hmi⟩ : ∃ mi, s.mems[0]? = some mi :=
    ⟨s.mems[0]'(by omega), List.getElem?_eq_getElem _⟩
  have hm := mem?_of hF hmi
  rcases hst : Memory.store mi.bytes (effAddr addr.toNat ⟨0, 0⟩) (count := IntType.i32.width / 8)
    (v.setWidth _) with _ | b
  · exact Wp.intStore_oob (m := .part) (a := .i32) (i := addr) (t := .i32) (c := v)
      hm (store_none_lt hst) htrap
  · exact Wp.intStore (m := .part) (a := .i32) (i := addr) (t := .i32) (c := v) hm hst
      (h mi b hmi hst)

/-- The bytes a full-width `i32` store wrote. -/
theorem bytes_of_store32 {B B' : ByteArray} {a : Nat} {v : BitVec 32}
    (h : Memory.store B a (count := IntType.i32.width / 8) (v.setWidth _) = some B') :
    bytesAt B' ⟨a, 4⟩ = (Memory.encodeLE 4 v.toNat).data.toList := by
  have := Silmaril.Wasm.Logic.Core.bytesAt_store_same h
  have e : (BitVec.setWidth (8 * (IntType.i32.width / 8)) v).toNat = v.toNat := by
    rw [BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt v.isLt
  rw [e] at this
  exact this

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Game.Accept Silmaril.Wasm.Game.IOAccept Silmaril.Wasm.Game.HandleAccept.Memory
  Silmaril.Wasm.Game.HandleAccept.MemSound
open Silmaril.Wasm.Logic.Core (bytesAt Region)

/-- What `name(addr, len)` observes right after a packed store of `len` bytes at `addr`. -/
theorem bytes32_of_store {i : Import} {s : Store Nat} {mi : MemInst} {b : ByteArray}
    {addr len v : BitVec 32} {sz : PackSize} (hl : s.mems.length = 1)
    (hst : Memory.store mi.bytes (effAddr addr.toNat ⟨0, 0⟩) (count := sz.width / 8)
      (v.setWidth _) = some b) (hlen : len.toNat = sz.width / 8) :
    (calloutIn i (some 0) (s.setMem 0 { mi with bytes := b }) [.i32 addr, .i32 len]).bytes32 =
      some (Memory.encodeLE (sz.width / 8)
        (v.setWidth (8 * (sz.width / 8))).toNat).data.toList := by
  have hseg := segment_of_store hst
    (calloutIn i (some 0) (s.setMem 0 { mi with bytes := b }) [.i32 addr, .i32 len])
    (memOf_setMem hl)
  rw [Callout.bytes32]
  simp only [calloutIn, Callout.args2, Callout.i32?, Val.i32, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def]
  rw [hlen, ← hseg]
  rfl

/-- What `sexp(0, 2)` observes when the memory holds two handles at `0` and `4`. -/
theorem handles32_pair {i : Import} {s : Store Nat} {b : ByteArray} {r₁ r₂ : BitVec 32}
    (hmem : memOf (some 0) s = some b) (h8 : 8 ≤ b.size)
    (h₀ : bytesAt b ⟨0, 4⟩ = (Memory.encodeLE 4 r₁.toNat).data.toList)
    (h₄ : bytesAt b ⟨4, 4⟩ = (Memory.encodeLE 4 r₂.toNat).data.toList) :
    handles32 (calloutIn i (some 0) s [.i32 0, .i32 2]) = some [r₁, r₂] := by
  have hargs : Callout.args2 Callout.i32? [Val.i32 0, Val.i32 2] = some (0, 2) := rfl
  unfold handles32
  simp only [calloutIn, hargs, Option.bind_eq_bind, Option.bind_some]
  have hseg : (Callout.segment ⟨(i.moduleName, i.name), [.i32 0, .i32 2], memOf (some 0) s⟩
      (0 : BitVec 32).toNat (4 * (2 : BitVec 32).toNat)) =
      some ((Memory.encodeLE 4 r₁.toNat).data.toList ++ (Memory.encodeLE 4 r₂.toNat).data.toList) := by
    unfold Callout.segment
    rw [hmem]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [show (0 : BitVec 32).toNat = 0 from rfl, show 4 * (2 : BitVec 32).toNat = 4 + 4 from rfl,
      readBytes_toList (by omega), bytesAt_append, h₀, h₄]
  rw [hseg]
  simp only [Option.bind_some]
  rw [le32s_encode, ← List.append_nil (Memory.encodeLE 4 r₂.toNat).data.toList, le32s_encode]
  rfl

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
