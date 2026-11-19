module

public import Silmaril.Wasm.Interp.CtxInv.Defs
public import Silmaril.Proofs.Wasm.Interp.XNoOutcome

@[expose] public section

/-!
# Invariants for the backward simulations: the witness facts (proofs)

* `CtxInv.steps`: host-free runs keep the invariant;
* **facts read off the witness** (`CtxInv.wit`), each the typed fact on the witness store,
  transferred: the witness changes only tags and exception instances, which none of these facts
  reads, and `call_indirect`'s defined-type cast decides alike on both stores.
  - `tyFuncs`: the store's function types are valid;
  - `evalFlat_progress`: native progress of a checked flat instruction (`evalFlat` reads no tag
    and no exception instance, `evalFlat_gst`);
  - `truthy_progress`, `callRef_top`, `returnCallRef_top`, `throwRef_top`, `indirect_res`
    (`indRes_gst_iff`), `typeArity_of_callRef_site`, `tailAnn_typed` (`tailRes_gst_iff`);
  - `TypedEntry`, `entry_of_ref_site`: a call site in the invariant puts its callee's body in the
    invariant (by the step `call_ref-func` and the `frame`/`label` decompositions, no witness);
    `tyTypes_callee`: the callee's instance has valid types (from the witness's `StoreOk`).
-/

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Abstract.CallXT (TyFuncs TyTypes)

variable {H : Type}

/-! ## Store transfer -/

/-- `s` with other tags and exception instances. -/
abbrev wst (s : Store H) (T : List TagInst) (X : List ExnInst) : Store H :=
  { s with tags := T, exns := X }

/-- **`evalFlat` reads no tag and no exception instance.** -/
theorem evalFlat_gst (s : Store H) (T : List TagInst) (X : List ExnInst) (f : Frame)
    (stk : List Val) (i : Instr) :
    Binaryen.evalFlat (wst s T X) f stk i =
      (Binaryen.evalFlat s f stk i).map fun r => (wst r.1 T X, r.2) := by
  have hm : ∀ x, (wst s T X).mem? f x = s.mem? f x := fun _ => rfl
  cases i
  case intLoad t p x arg =>
    rcases p with _ | p
    · rcases stk with _ | ⟨v, r⟩
      · rfl
      · simp only [Binaryen.evalFlat, hm]
        cases Binaryen.addrNat? v <;> rcases s.mem? f x with _ | ⟨ma, mi⟩ <;> try rfl
        dsimp only
        cases Execution.Memory.load mi.bytes _ _ <;> rfl
    · rfl
  case intStore t p x arg =>
    rcases p with _ | p
    · rcases stk with _ | ⟨w, _ | ⟨v, r⟩⟩
      · rfl
      · rfl
      · simp only [Binaryen.evalFlat, hm]
        cases Binaryen.addrNat? v <;> cases Binaryen.asInt t w <;>
          rcases s.mem? f x with _ | ⟨ma, mi⟩ <;> try rfl
        dsimp only
        cases Execution.Memory.store mi.bytes _ _ <;> rfl
    · rfl
  case intBinOp t op =>
    rcases stk with _ | ⟨y, _ | ⟨x, r⟩⟩
    · rfl
    · rfl
    · simp only [Binaryen.evalFlat]
      cases Binaryen.asInt t x <;> cases Binaryen.asInt t y <;> try rfl
      rename_i a b
      dsimp only [bind, Option.bind]
      cases Numerics.intBinOp t op a b <;> rfl
  case intRelOp t op =>
    rcases stk with _ | ⟨y, _ | ⟨x, r⟩⟩
    · rfl
    · rfl
    · simp only [Binaryen.evalFlat]
      cases Binaryen.asInt t x <;> cases Binaryen.asInt t y <;> rfl
  all_goals rcases stk with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩ <;> simp only [Binaryen.evalFlat] <;>
    (try rfl) <;> (simp only [Option.map_map]; rfl)

/-- **`call_indirect`'s resolution reads no tag and no exception instance**, when the
defined-type casts decide alike. -/
theorem indRes_wst {s : Store H} {T : List TagInst} {X : List ExnInst}
    (href : ∀ (m : ModuleInst) (r : Ref) (b : Bool) (y : TypeIdx),
      RefOk (wst s T X) r (m.instRef ⟨b, .typeIdx y⟩) ↔ RefOk s r (m.instRef ⟨b, .typeIdx y⟩))
    {f : Frame} {x : TableIdx} {y : TypeIdx} {ad : AddrType} {j : BitVec ad.intType.width}
    {o : Option Nat} :
    Abstract.CallRes.IndRes (wst s T X) f x y ad j o ↔ Abstract.CallRes.IndRes s f x y ad j o := by
  constructor
  · intro h
    cases h with
    | oob ht h => exact .oob ht h
    | castFail ht hr hc => exact .castFail ht hr fun h' => hc ((href f.module _ true y).2 h')
    | null ht hr hc => exact .null ht hr ((href f.module _ true y).1 hc)
    | func ht hr hc => exact .func ht hr ((href f.module _ true y).1 hc)
  · intro h
    cases h with
    | oob ht h => exact .oob ht h
    | castFail ht hr hc => exact .castFail ht hr fun h' => hc ((href f.module _ true y).1 h')
    | null ht hr hc => exact .null ht hr ((href f.module _ true y).2 hc)
    | func ht hr hc => exact .func ht hr ((href f.module _ true y).2 hc)

/-- Tail-call resolution reads no tag and no exception instance, when the defined-type casts
decide alike. -/
theorem tailRes_wst {s : Store H} {T : List TagInst} {X : List ExnInst}
    (href : ∀ (m : ModuleInst) (r : Ref) (b : Bool) (y : TypeIdx),
      RefOk (wst s T X) r (m.instRef ⟨b, .typeIdx y⟩) ↔ RefOk s r (m.instRef ⟨b, .typeIdx y⟩))
    {f : Frame} {i : Instr} {stk : List Val} {o : Option (Nat × List Val)} :
    Abstract.CallX.TailRes (wst s T X) f i stk o ↔ Abstract.CallX.TailRes s f i stk o := by
  constructor
  · intro h
    cases h with
    | direct hfi => exact .direct hfi
    | indirect hres => exact .indirect ((indRes_wst href).1 hres)
    | indirectTrap hres => exact .indirectTrap ((indRes_wst href).1 hres)
    | ref => exact .ref
    | refNull => exact .refNull
  · intro h
    cases h with
    | direct hfi => exact .direct hfi
    | indirect hres => exact .indirect ((indRes_wst href).2 hres)
    | indirectTrap hres => exact .indirectTrap ((indRes_wst href).2 hres)
    | ref => exact .ref
    | refNull => exact .refNull

/-! ## Generic facts -/

namespace CtxInv

variable (K : CtxInv H)

/-- **Host-free runs keep the invariant.** -/
theorem steps {P : Numerics.Profile} {c c' : Config H} (h : K.CT c)
    (hs : Steps P (fun _ _ _ _ => False) c c') : K.CT c' := by
  induction hs with
  | refl => exact h
  | tail _ hs ih => exact K.step ih hs

/-- The witness of a configuration given by its components. -/
theorem wit' {s : Store H} {f : Frame} {code : List Admin} (h : K.CT ⟨s, f, code⟩) :
    ∃ (T : List TagInst) (X : List ExnInst), s.tags <+: T ∧
      (∀ (m : ModuleInst) (r : Ref) (b : Bool) (y : TypeIdx),
        RefOk (wst s T X) r (m.instRef ⟨b, .typeIdx y⟩) ↔ RefOk s r (m.instRef ⟨b, .typeIdx y⟩)) ∧
      Sim.ContextTyped ⟨wst s T X, f, code⟩ :=
  K.wit h

/-- The store of a configuration in the invariant has valid function types. -/
theorem tyFuncs {s : Store H} {f : Frame} {c : List Admin} (h : K.CT ⟨s, f, c⟩) : TyFuncs s := by
  obtain ⟨T, X, -, -, hw⟩ := K.wit' h
  obtain ⟨-, -, -, hsok, -, -, -⟩ := Sim.ContextTyped.fragment_types hw
  exact fun a fi hfi => PC.StoreOk.func_tyOk hsok hfi

/-- **The callee instances of the store have valid types.** -/
theorem tyTypes_callee {s : Store H} {f : Frame} {c : List Admin} (h : K.CT ⟨s, f, c⟩) {a : Nat}
    {fi : FuncInst H} {fn : Func} (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn) :
    TyTypes fi.module := by
  obtain ⟨T, X, -, -, hw⟩ := K.wit' h
  obtain ⟨-, -, -, hsok, -, -, -⟩ := Sim.ContextTyped.fragment_types hw
  exact tyTypes_of_storeOkX hsok hfi hcode

variable {s : Store H} {f : Frame} {stk : List Val} {rest : List Admin}

/-- **Native progress at a checked flat instruction** in the invariant. -/
theorem evalFlat_progress {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
    {labels : List Nat} {o' : Option Nat} {i : Instr}
    (hc : flatChk F mi nl ret labels stk.length i = some o') (hi : ∀ x, i ≠ .call x)
    (ht : K.CT ⟨s, f, vals stk.reverse ++ .plain i :: rest⟩) :
    ∃ r, Binaryen.evalFlat s f stk i = some r := by
  obtain ⟨T, X, -, -, hw⟩ := K.wit' ht
  obtain ⟨r, hr⟩ := evalFlat_progressH hc hi hw
  rw [evalFlat_gst] at hr
  cases h : Binaryen.evalFlat s f stk i with
  | none => rw [h] at hr; cases hr
  | some r' => exact ⟨r', rfl⟩

/-- The condition of an `if` in the invariant is an `i32`. -/
theorem truthy_progress {bt : BlockType} {b₁ b₂ : List Instr}
    (ht : K.CT ⟨s, f, vals stk.reverse ++ .plain (.if_ bt b₁ b₂) :: rest⟩) :
    ∃ cv r b, stk = cv :: r ∧ Binaryen.truthy cv = some b := by
  obtain ⟨T, X, -, -, hw⟩ := K.wit' ht
  exact truthy_progressH hw

/-- The operand of a `call_ref y` in the invariant. -/
theorem callRef_top {y : TypeIdx}
    (ht : K.CT ⟨s, f, vals stk.reverse ++ .plain (.callRef y) :: rest⟩) (hm : TyTypes f.module) :
    ∃ (r : Ref) (stk' : List Val), stk = .ref r :: stk' ∧
      (r = .null ∨ ∃ (a : Nat) (fi : FuncInst H), r = .func a ∧ s.funcs[a]? = some fi) := by
  obtain ⟨T, X, -, -, hw⟩ := K.wit' ht
  have h := Interp.callRef_top hw hm
  exact h

/-- The operand of a `return_call_ref y` in the invariant. -/
theorem returnCallRef_top {y : TypeIdx}
    (ht : K.CT ⟨s, f, vals stk.reverse ++ .plain (.returnCallRef y) :: rest⟩)
    (hm : TyTypes f.module) :
    ∃ (r : Ref) (stk' : List Val), stk = .ref r :: stk' ∧
      (r = .null ∨ ∃ (a : Nat) (fi : FuncInst H), r = .func a ∧ s.funcs[a]? = some fi) := by
  obtain ⟨T, X, -, -, hw⟩ := K.wit' ht
  have h := Interp.returnCallRef_top hw hm
  exact h

/-- The index of a `call_indirect` or `return_call_indirect` in the invariant resolves. -/
theorem indirect_res {x : TableIdx} {y : TypeIdx} {i : Instr}
    (hi : i = .callIndirect x y ∨ i = .returnCallIndirect x y)
    (ht : K.CT ⟨s, f, vals stk.reverse ++ .plain i :: rest⟩) :
    ∃ (ad : AddrType) (j : BitVec ad.intType.width) (stk' : List Val) (o : Option Nat),
      stk = .num ⟨.int ad.intType, j⟩ :: stk' ∧ Abstract.CallRes.IndRes s f x y ad j o := by
  obtain ⟨T, X, -, href, hw⟩ := K.wit' ht
  obtain ⟨ad, j, stk', o, h1, h2⟩ := Interp.indirect_res hi hw
  exact ⟨ad, j, stk', o, h1, (indRes_wst href).1 h2⟩

/-- The `call_ref` premise at a site in the invariant. -/
theorem typeArity_of_callRef_site {fa : Nat} {y : TypeIdx} {fi : FuncInst H}
    {ps rs : List CValType}
    (ht : K.CT ⟨s, f, vals (.ref (.func fa) :: stk).reverse ++ .plain (.callRef y) :: rest⟩)
    (hm : TyTypes f.module) (hfi : s.funcs[fa]? = some fi)
    (hty : DefType.funcType? fi.type = some (ps, rs)) (hfiok : TyOk {} fi.type) :
    Abstract.CallXT.typeArity f.module y = some (ps.length, rs.length) := by
  obtain ⟨T, X, -, -, hw⟩ := K.wit' ht
  exact Abstract.CallXT.typeArity_of_callRef_site hw hm hfi hty hfiok

/-- The type annotation of a resolved tail call in the invariant. -/
theorem tailAnn_typed {i : Instr} {fa : Nat} {fi : FuncInst H} {ps rs : List CValType}
    {labels : List Nat} {ret : Nat} {o : Option Nat}
    (hres : Abstract.CallX.TailRes s f i stk (some (fa, stk.drop (Abstract.CallX.tailPop i))))
    (hsite : K.CT ⟨s, f, vals stk.reverse ++ .plain i :: rest⟩)
    (hfi : s.funcs[fa]? = some fi) (hty : DefType.funcType? fi.type = some (ps, rs))
    (hTF : TyFuncs s) (hTM : TyTypes f.module)
    (hf : flatChkE tExt s.funcs f.module f.locals.length ret labels stk.length i = some o) :
    ∀ y, Abstract.CallXT.tailAnn i = some y →
      Abstract.CallXT.typeArity f.module y = some (ps.length, rs.length) := by
  obtain ⟨T, X, -, href, hw⟩ := K.wit' hsite
  exact Interp.tailAnn_typed ((tailRes_wst href).2 hres) hw hfi hty hTF hTM hf

/-! ### Callee entry -/

/-- **A callee body in the invariant**: every Wasm function at `a` runs its body on `us` in the
invariant. -/
def TypedEntry (s : Store H) (a : Nat) (us : List Val) : Prop :=
  ∀ (fi : FuncInst H) (fn : Func), s.funcs[a]? = some fi → fi.code = .wasm fn →
    K.CT ⟨s, Frame.forCall fi.module us fn.locals, expression fn.body⟩

/-- **A call site in the invariant puts its callee's body in the invariant** (`call_ref-func`,
then the frame and label decompositions). -/
theorem entry_of_ref_site {P : Numerics.Profile} {a : Nat} {c : Admin} {fi : FuncInst H}
    {ps rs : List CValType}
    (ht : K.CT ⟨s, f, vals stk.reverse ++ [.ref (.func a), c] ++ rest⟩)
    (hc : c.IsCallRef) (hfi : s.funcs[a]? = some fi)
    (hty : DefType.funcType? fi.type = some (ps, rs)) (hp : ps.length ≤ stk.length) :
    K.TypedEntry s a (stk.take ps.length).reverse := by
  intro fi' fn hfi' hcode
  rw [hfi] at hfi'; cases hfi'
  obtain ⟨ps', rs', he, hpl, -⟩ := expand_of_funcType hty
  have hpp : ps.length = ps'.length := by rw [← hpl]
  have hn : (stk.take ps.length).reverse.length = ps'.length := by
    rw [← hpp]; simp only [List.length_reverse, List.length_take]; omega
  have e : vals stk.reverse ++ [.ref (.func a), c] ++ rest =
      vals (stk.drop ps.length).reverse ++
        (vals (stk.take ps.length).reverse ++ [.ref (.func a), c]) ++ rest := by
    rw [rev_take_drop stk ps.length]; simp
  rw [e] at ht
  have hst := Step.ctx (P := P) (host := noHostX) (stk.drop ps.length).reverse rest
    (Step.callRefFunc (s := s) (f := f) hc hfi he hn hcode)
  exact K.label (vs := []) (rest := []) (by simpa [vals] using K.frame (K.step ht hst))

end CtxInv

end Silmaril.Wasm.Interp
