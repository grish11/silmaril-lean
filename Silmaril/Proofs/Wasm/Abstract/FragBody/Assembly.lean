module

public import Silmaril.Proofs.Wasm.Abstract.FragBody.Validation

/-!
# Validation gives the fragment typing: the recursive assembly

Core validation of the lowering of a recognised, native-arity-checked fragment
tree, operand list or body, in a Core context `D` that fits the fragment
contexts (`Fit D Γ ρ Λ`), gives the fragment typing (`Ty`, `ArgsTy`, `SeqTy`).

The induction carries, for every tree whose native check completes with a value
arity, its fragment result type `t` and the **principal typing** of its lowering
at `t` (in every fitting context: `Principal D b.lower (t.toList.map numInt)`),
which pins the stack the operator above it consumes. Principal typing is proved
directly here, operator by operator, so `select` (whose result type is read off
its operands, not its context, and which `Binaryen.principal_tree` therefore does
not cover) is included: `Principal.snoc_num` only needs the operator's results
once its parameters are the (numeric) operand types. Never-completing trees
(`unreachable`, `br`, `return`) get every type, so dead code after them is typed
by `SeqTy.bot`.

Main results: `tree_ok`, `args_ok`, `seq_ok` (mutual), and
`funcTyped_of_instrsOk` for function bodies.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.FragBody

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Validation
open Silmaril.Wasm.Abstract.FragBody (Ty ArgsTy SeqTy OpSig funcTyped)

/-! ## Numeric types -/

theorem numInt_inj {a b : IntType} (h : numInt a = numInt b) : a = b := by
  cases h; rfl

theorem map_numInt_inj {as bs : List IntType} (h : as.map numInt = bs.map numInt) : as = bs :=
  List.map_injective_iff.mpr (fun _ _ => numInt_inj) h

theorem toList_numInt_inj {a b : Option IntType}
    (h : a.toList.map numInt = b.toList.map numInt) : a = b := by
  cases a <;> cases b <;> simp_all

theorem nums_numInt (τs : List IntType) : ∀ v ∈ τs.map numInt, ∃ n, v = .num n := by
  intro v hv
  simp only [List.mem_map] at hv
  obtain ⟨t, -, rfl⟩ := hv
  exact ⟨_, rfl⟩

theorem resultOk_numInt (Δ : TypeCtx) (τs : List IntType) : ResultOk Δ (τs.map numInt) := by
  intro v hv
  simp only [List.mem_map] at hv
  obtain ⟨t, -, rfl⟩ := hv
  exact TyOk.num _

theorem wf_withLabel_numInt {D : Context} (hD : D.Wf) (lt : Option IntType) :
    (D.withLabel (lt.toList.map numInt)).Wf := by
  refine ⟨hD.types, hD.tags, hD.globals, hD.tables, hD.funcs, hD.locals, ?_, hD.return_, hD.elems⟩
  intro l hl
  simp only [Context.withLabel, List.mem_cons] at hl
  rcases hl with rfl | hl
  exacts [resultOk_numInt _ _, hD.labels _ hl]

theorem arOf_none {t : Option IntType} (h : SSA.arOf t = .none) : t = none := by
  cases t <;> simp_all [SSA.arOf]

theorem arOf_one {t : Option IntType} (h : SSA.arOf t = .one) : ∃ τ, t = some τ := by
  cases t <;> simp_all [SSA.arOf]

theorem toList_length_arOf (t : Option IntType) : t.toList.length = arLen (SSA.arOf t) := by
  cases t <;> rfl

/-! ## Principal typing of an operator node -/

/-- `Principal.snoc` for numeric operands: the operator's results need only be
known once its parameters are the operand types. -/
theorem Principal.snoc_num {D : Context} (hD : D.Wf) {args : List Instr} {j : Instr}
    {vs r : List CValType} (hargs : Principal D args vs) (hvs : ∀ v ∈ vs, ∃ n, v = .num n)
    (hj : ∀ ya it₀, InstrOk (D.initLocals ya) j it₀ →
      it₀.params.length = vs.length ∧ (it₀.params = vs → it₀.results = r)) :
    Principal D (args ++ [j]) r := by
  intro ps xs rs h
  obtain ⟨m, ya, yb, ha, hb, hL⟩ := InstrsOk.split hD h rfl
  obtain ⟨s1, ya', ha', hL1⟩ := hargs ps ya m ha
  have hDa := hD.initLocals ya
  obtain ⟨fr, it₀, hfr, hi, hsub⟩ := single_inv_ok hDa hb
  obtain ⟨hlen, hres'⟩ := hj ya it₀ hi
  have rm : ResultOk D.toTypeCtx m := (InstrsOk.regular hD ha).2.1
  have rvs : ResultOk D.toTypeCtx vs := (InstrsOk.regular hD ha').2.1
  have ri := hi.regular hDa
  obtain ⟨sp, sr, sx⟩ := hsub
  simp only [Context.initLocals_toTypeCtx] at sp sr hfr
  have s2 : ResultSub D.toTypeCtx (ps ++ vs) (fr ++ it₀.params) :=
    ResultSub.trans hD.types rm s1 sp
  obtain ⟨sps, svs⟩ := resultSub_append_split hlen.symm s2
  have hres := hres' (resultSub_nums svs hvs)
  have rr : ResultOk D.toTypeCtx r := by rw [← hres]; simpa using ri.2.1
  refine ⟨?_, ya' ++ it₀.inits, ?_, ?_⟩
  · rw [hres] at sr
    exact ResultSub.trans hD.types (ResultOk.append hfr rr)
      (ResultSub.append sps (ResultSub.refl _ _)) sr
  · have hj1 : InstrsOk (D.initLocals ya) [j] ⟨vs, it₀.inits, r⟩ :=
      .sub (.instr hi)
        ⟨by simpa using svs, by rw [hres]; exact ResultSub.refl _ _, fun _ h hn => absurd h hn⟩
        ⟨by simpa using rvs, by simpa using rr, ri.2.2⟩
    exact InstrsOk.append ha' (InstrsOk.regular hD ha').2.2 (hj1.initLocals_relocal hL1)
  · rw [Context.initLocals_append] at hL ⊢
    have h3 : LocalsLe ((D.initLocals ya).initLocals yb).locals
        ((D.initLocals ya).initLocals it₀.inits).locals :=
      LocalsLe.initLocals_of_sub (C := D.initLocals ya) sx
    exact LocalsLe.trans hL (LocalsLe.trans h3 (LocalsLe.initLocals hL1 _))

/-- Operands with principal results `vs`, followed by an instruction, in a valid
sequence: the operands are typed, and the instruction is typed with parameters
whose suffix the operand stack fills. -/
theorem operands_sub {D : Context} (hD : D.Wf) {args : List Instr} {i : Instr}
    {vs ps rs : List CValType} {xs : List Nat}
    (hp : Principal D args vs) (h : InstrsOk D (args ++ [i]) ⟨ps, xs, rs⟩) :
    ∃ ya m fr it₀, InstrsOk D args ⟨ps, ya, m⟩ ∧ InstrOk (D.initLocals ya) i it₀ ∧
      ResultSub D.toTypeCtx (ps ++ vs) (fr ++ it₀.params) := by
  obtain ⟨m, ya, yb, ha, hb, -⟩ := InstrsOk.split hD h rfl
  obtain ⟨s1, -⟩ := hp ps ya m ha
  obtain ⟨fr, it₀, hi, hsub⟩ := InstrsOk.single_inv (hD.initLocals ya) hb
  have rm : ResultOk D.toTypeCtx m := (InstrsOk.regular hD ha).2.1
  exact ⟨ya, m, fr, it₀, ha, hi, ResultSub.trans hD.types rm s1 (by simpa using hsub.1)⟩

/-- The suffix of the parameters that the numeric operands fill is the operands' types. -/
theorem sub_suffix {Δ : TypeCtx} {ps vs fr p₁ p₂ : List CValType}
    (h : ResultSub Δ (ps ++ vs) (fr ++ (p₁ ++ p₂))) (hl : p₂.length = vs.length)
    (hn : ∀ v ∈ vs, ∃ n, v = .num n) : p₂ = vs := by
  rw [← List.append_assoc] at h
  exact resultSub_nums (resultSub_append_split hl.symm h).2 hn

/-! ## Instruction inversions -/

theorem instrOk_localGet_inv {D : Context} {x : LocalIdx} {it : InstrType}
    (h : InstrOk D (.localGet x) it) :
    ∃ t, D.locals[x.toNat]? = some ⟨.set, t⟩ ∧ it = .plain [] [t] := by
  cases h
  all_goals (rename_i h; cases h)
  exact ⟨_, by assumption, rfl⟩

theorem instrOk_localSet_inv {D : Context} {x : LocalIdx} {it : InstrType}
    (h : InstrOk D (.localSet x) it) :
    ∃ i t, D.locals[x.toNat]? = some ⟨i, t⟩ ∧ it = ⟨[t], [x.toNat], []⟩ := by
  cases h
  all_goals (rename_i h; cases h)
  exact ⟨_, _, by assumption, rfl⟩

theorem instrOk_localTee_inv {D : Context} {x : LocalIdx} {it : InstrType}
    (h : InstrOk D (.localTee x) it) :
    ∃ i t, D.locals[x.toNat]? = some ⟨i, t⟩ ∧ it = ⟨[t], [x.toNat], [t]⟩ := by
  cases h
  all_goals (rename_i h; cases h)
  exact ⟨_, _, by assumption, rfl⟩

theorem instrOk_drop_inv {D : Context} {it : InstrType} (h : InstrOk D .drop it) :
    ∃ t, it = .plain [t] [] := by
  cases h
  all_goals (rename_i h; cases h)
  exact ⟨_, rfl⟩

theorem instrOk_br_inv {D : Context} {l : LabelIdx} {it : InstrType} (h : InstrOk D (.br l) it) :
    ∃ ts t₁ t₂, D.labels[l.toNat]? = some ts ∧ it = .plain (t₁ ++ ts) t₂ := by
  cases h
  all_goals first | exact ⟨_, _, _, by assumption, rfl⟩ | (rename_i h; cases h)

theorem instrOk_brIf_inv {D : Context} {l : LabelIdx} {it : InstrType} (h : InstrOk D (.brIf l) it) :
    ∃ ts, D.labels[l.toNat]? = some ts ∧ it = .plain (ts ++ [numInt .i32]) ts := by
  cases h
  all_goals first | exact ⟨_, by assumption, rfl⟩ | (rename_i h; cases h)

theorem instrOk_return_inv {D : Context} {it : InstrType} (h : InstrOk D .return_ it) :
    ∃ ts t₁ t₂, D.return_ = some ts ∧ it = .plain (t₁ ++ ts) t₂ := by
  cases h
  all_goals first | exact ⟨_, _, _, by assumption, rfl⟩ | (rename_i h; cases h)

/-- The block types of the fragment, inverted. -/
theorem blockTypeOk_frag {D : Context} {bt : BlockType} {ty : Option IntType}
    {t₁ t₂ : List CValType} (h : SSA.ofBlockType? bt = some ty) (hb : BlockTypeOk D bt t₁ t₂) :
    t₁ = [] ∧ t₂ = ty.toList.map numInt := by
  obtain ⟨h1, h2⟩ := blockType_inv (C := D) rfl hb
  obtain ⟨hp, hr⟩ := blockType_frag D h
  rw [hp] at h2; rw [hr] at h1
  refine ⟨List.eq_nil_of_length_eq_zero (Option.some.inj h2).symm, ?_⟩
  rw [← Option.some.inj h1]
  cases ty <;> rfl

/-- Operator signatures are functional. -/
theorem opSig_det {o : SSA.Op} {ts : List IntType} {t t' : IntType}
    (h : Abstract.FragBody.OpSig o ts t) (h' : Abstract.FragBody.OpSig o ts t') : t = t' := by
  cases h <;> cases h' <;> rfl

/-- The result type of a recognised native operator on operands of types `τs`. -/
theorem op_res {i : Instr} {es args : List SSA.Expr} {o : SSA.Op}
    (hofi : SSA.ofInstr? i es = some (.op o args)) (hnat : o.native = true) (τs : List IntType) :
    ∃ t, ∀ D it₀, InstrOk D i it₀ → it₀.params = τs.map numInt →
      Abstract.FragBody.OpSig o τs t ∧ it₀.results = [numInt t] := by
  by_cases hex : ∃ D it₀, InstrOk D i it₀ ∧ it₀.params = τs.map numInt
  · obtain ⟨D, it₀, hi, hp⟩ := hex
    obtain ⟨t, hs, -⟩ := opSig_of_instr hofi hi hp hnat
    refine ⟨t, fun D' it₁ hi' hp' => ?_⟩
    obtain ⟨t', hs', hr'⟩ := opSig_of_instr hofi hi' hp' hnat
    obtain rfl := opSig_det hs hs'
    exact ⟨hs, hr'⟩
  · exact ⟨.i32, fun D it₀ hi hp => absurd ⟨D, it₀, hi, hp⟩ hex⟩

theorem sub_suffix0 {Δ : TypeCtx} {ps vs fr p : List CValType}
    (h : ResultSub Δ (ps ++ vs) (fr ++ p)) (hl : p.length = vs.length)
    (hn : ∀ v ∈ vs, ∃ n, v = .num n) : p = vs :=
  sub_suffix (p₁ := []) h hl hn

/-! ## The induction invariants -/

/-- What the assembly proves of a tree `b` recognised as `e` with native check `r`:
a never-completing tree has every type; a completing one has a result type `t`
of its arity, at which its lowering is principal in every fitting context, and is
typed at `t` whenever its lowering is valid. -/
def TreeOk (Γ : List IntType) (ρ : Option IntType) (Λ : List (Option IntType)) (b : BExpr)
    (e : SSA.Expr) (r : Option SSA.Ar) : Prop :=
  (r = none → ∀ D, D.Wf → Fit D Γ ρ Λ → ∀ it, InstrsOk D b.lower it → ∀ r', Ty Γ ρ Λ e r') ∧
  ∀ a, r = some a → ∃ t : Option IntType, SSA.arOf t = a ∧
    (∀ D, D.Wf → Fit D Γ ρ Λ → Principal D b.lower (t.toList.map numInt)) ∧
    (∀ D, D.Wf → Fit D Γ ρ Λ → ∀ it, InstrsOk D b.lower it → Ty Γ ρ Λ e t)

/-- What the assembly proves of an operand list: its types, principal and typed. -/
structure ArgsOk (Γ : List IntType) (ρ : Option IntType) (Λ : List (Option IntType))
    (bs : List BExpr) (es : List SSA.Expr) (τs : List IntType) : Prop where
  len : τs.length = es.length
  principal : ∀ D, D.Wf → Fit D Γ ρ Λ → Principal D (BExpr.lowerList bs) (τs.map numInt)
  typed : ∀ D, D.Wf → Fit D Γ ρ Λ → ∀ it, InstrsOk D (BExpr.lowerList bs) it → ArgsTy Γ ρ Λ es τs

/-- What the assembly proves of a body of type `ty` (typed at results below `ty`). -/
def SeqGoal (Γ : List IntType) (ρ : Option IntType) (Λ : List (Option IntType))
    (bs : List BExpr) (es : List SSA.Expr) (ty : Option IntType) : Prop :=
  ∀ D, D.Wf → Fit D Γ ρ Λ → ∀ xs T, ResultSub D.toTypeCtx T (ty.toList.map numInt) →
    InstrsOk D (BExpr.lowerList bs) ⟨[], xs, T⟩ → SeqTy Γ ρ Λ es ty

section
variable {Γ : List IntType} {ρ : Option IntType} {Λ : List (Option IntType)}

theorem TreeOk.val {b : BExpr} {e : SSA.Expr} {a : SSA.Ar} (t : Option IntType)
    (ha : SSA.arOf t = a)
    (hP : ∀ D, D.Wf → Fit D Γ ρ Λ → Principal D b.lower (t.toList.map numInt))
    (hT : ∀ D, D.Wf → Fit D Γ ρ Λ → ∀ it, InstrsOk D b.lower it → Ty Γ ρ Λ e t) :
    TreeOk Γ ρ Λ b e (some a) :=
  ⟨fun h => absurd h (by simp), fun _ h => by cases h; exact ⟨t, ha, hP, hT⟩⟩

theorem TreeOk.bot {b : BExpr} {e : SSA.Expr}
    (hT : ∀ D, D.Wf → Fit D Γ ρ Λ → ∀ it, InstrsOk D b.lower it → ∀ r', Ty Γ ρ Λ e r') :
    TreeOk Γ ρ Λ b e none :=
  ⟨fun _ => hT, fun _ h => absurd h (by simp)⟩

/-! ## Nodes -/

theorem ite_some {c : Prop} [Decidable c] {α : Type} {a b : α}
    (h : (if c then some a else none) = some b) : c ∧ a = b := by
  split at h <;> simp_all


/-- Labels of the native check, read in `Λ`. -/
theorem label_of_map {l : Nat} {a : SSA.Ar} (h : (Λ.map SSA.arOf)[l]? = some a) :
    ∃ lt, Λ[l]? = some lt ∧ SSA.arOf lt = a := by
  rw [List.getElem?_map] at h
  rcases hg : Λ[l]? with _ | lt
  · rw [hg] at h; cases h
  · rw [hg] at h; exact ⟨lt, rfl, Option.some.inj h⟩

theorem node_op {i : Instr} {args : List BExpr} {es : List SSA.Expr} {o : SSA.Op}
    {r : Option SSA.Ar} {τs : List IntType}
    (hofi : SSA.ofInstr? i es = some (.op o es))
    (hty : SSA.tyE (Λ.map SSA.arOf) (SSA.arOf ρ) Γ.length (.op o es) = some r)
    (hA : ArgsOk Γ ρ Λ args es τs) : TreeOk Γ ρ Λ (.op i args) (.op o es) r := by
  rw [SSA.tyE] at hty
  split at hty
  · rename_i hc
    cases hty
    have hnat : o.native = true := by simp only [Bool.and_eq_true] at hc; exact hc.1.1
    obtain ⟨t, ht⟩ := op_res hofi hnat τs
    have hpl := ofInstr_params_len hofi hnat
    refine TreeOk.val (some t) rfl (fun D hD hF => ?_) (fun D hD hF it hit => ?_)
    · simp only [BExpr.lower_op]
      refine Principal.snoc_num hD (hA.principal D hD hF) (nums_numInt τs)
        fun ya it₀ hi => ⟨?_, fun hp => (ht _ _ hi hp).2⟩
      rw [hpl _ _ hi, List.length_map, hA.len]
    · obtain ⟨ps, xs, rs⟩ := it
      simp only [BExpr.lower_op] at hit
      obtain ⟨ya, m, fr, it₀, ha, hi, hsub⟩ := operands_sub hD (hA.principal D hD hF) hit
      have hp : it₀.params = τs.map numInt :=
        sub_suffix0 hsub (by rw [hpl _ _ hi, List.length_map, hA.len]) (nums_numInt τs)
      exact .op (ht _ _ hi hp).1 (hA.typed D hD hF _ ha)
  · cases hty

theorem node_localGet {x : LocalIdx} {args : List BExpr} {r : Option SSA.Ar} {τs : List IntType}
    (hty : SSA.tyE (Λ.map SSA.arOf) (SSA.arOf ρ) Γ.length (.localGet x.toNat) = some r)
    (hA : ArgsOk Γ ρ Λ args [] τs) :
    TreeOk Γ ρ Λ (.op (.localGet x) args) (.localGet x.toNat) r := by
  rw [SSA.tyE] at hty
  split at hty
  · rename_i hx
    cases hty
    obtain rfl : τs = [] := List.eq_nil_of_length_eq_zero hA.len
    refine TreeOk.val (some Γ[x.toNat]) rfl (fun D hD hF => ?_)
      (fun _ _ _ _ _ => .localGet (List.getElem?_eq_getElem hx))
    simp only [BExpr.lower_op]
    refine Principal.snoc_num hD (hA.principal D hD hF) (nums_numInt []) fun ya it₀ hi => ?_
    obtain ⟨t', hl, rfl⟩ := instrOk_localGet_inv hi
    obtain ⟨t, hg, ht⟩ := (hF.initLocals ya).local_type hl
    rw [List.getElem?_eq_getElem hx] at hg
    obtain rfl := Option.some.inj hg
    have ht' : t' = numInt Γ[x.toNat] := by simpa using ht
    subst ht'
    exact ⟨rfl, fun _ => rfl⟩
  · cases hty

theorem node_localSet {x : LocalIdx} {a : SSA.Expr} {args : List BExpr} {r : Option SSA.Ar}
    {τs : List IntType}
    (hty : SSA.tyE (Λ.map SSA.arOf) (SSA.arOf ρ) Γ.length (.localSet x.toNat a) = some r)
    (hA : ArgsOk Γ ρ Λ args [a] τs) :
    TreeOk Γ ρ Λ (.op (.localSet x) args) (.localSet x.toNat a) r := by
  rw [SSA.tyE] at hty
  split at hty
  · cases hty
    obtain ⟨τ, rfl⟩ : ∃ τ, τs = [τ] := by
      match τs, hA.len with
      | [τ], _ => exact ⟨τ, rfl⟩
    refine TreeOk.val none rfl (fun D hD hF => ?_) (fun D hD hF it hit => ?_)
    · simp only [BExpr.lower_op]
      refine Principal.snoc_num hD (hA.principal D hD hF) (nums_numInt _) fun ya it₀ hi => ?_
      obtain ⟨_, t', _, rfl⟩ := instrOk_localSet_inv hi
      exact ⟨rfl, fun _ => rfl⟩
    · obtain ⟨ps, xs, rs⟩ := it
      simp only [BExpr.lower_op] at hit
      obtain ⟨ya, m, fr, it₀, ha, hi, hsub⟩ := operands_sub hD (hA.principal D hD hF) hit
      obtain ⟨_, t', hl, rfl⟩ := instrOk_localSet_inv hi
      have hp := sub_suffix0 hsub rfl (nums_numInt _)
      obtain ⟨t, hg, ht⟩ := (hF.initLocals ya).local_type hl
      have h1 : t' = numInt τ := by simpa using hp
      have h2 : t' = numInt t := by simpa using ht
      obtain rfl := numInt_inj (h1.symm.trans h2)
      cases hA.typed D hD hF _ ha with
      | cons h₁ _ => exact .localSet hg h₁
  · cases hty

theorem node_localTee {x : LocalIdx} {a : SSA.Expr} {args : List BExpr} {r : Option SSA.Ar}
    {τs : List IntType}
    (hty : SSA.tyE (Λ.map SSA.arOf) (SSA.arOf ρ) Γ.length (.localTee x.toNat a) = some r)
    (hA : ArgsOk Γ ρ Λ args [a] τs) :
    TreeOk Γ ρ Λ (.op (.localTee x) args) (.localTee x.toNat a) r := by
  rw [SSA.tyE] at hty
  split at hty
  · rename_i hc
    cases hty
    have hx : x.toNat < Γ.length := by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc; exact hc.1
    obtain ⟨τ, rfl⟩ : ∃ τ, τs = [τ] := by
      match τs, hA.len with
      | [τ], _ => exact ⟨τ, rfl⟩
    refine TreeOk.val (some Γ[x.toNat]) rfl (fun D hD hF => ?_) (fun D hD hF it hit => ?_)
    · simp only [BExpr.lower_op]
      refine Principal.snoc_num hD (hA.principal D hD hF) (nums_numInt _) fun ya it₀ hi => ?_
      obtain ⟨_, t', hl, rfl⟩ := instrOk_localTee_inv hi
      obtain ⟨t, hg, ht⟩ := (hF.initLocals ya).local_type hl
      rw [List.getElem?_eq_getElem hx] at hg
      obtain rfl := Option.some.inj hg
      have ht' : t' = numInt Γ[x.toNat] := by simpa using ht
      subst ht'
      exact ⟨rfl, fun _ => rfl⟩
    · obtain ⟨ps, xs, rs⟩ := it
      simp only [BExpr.lower_op] at hit
      obtain ⟨ya, m, fr, it₀, ha, hi, hsub⟩ := operands_sub hD (hA.principal D hD hF) hit
      obtain ⟨_, t', hl, rfl⟩ := instrOk_localTee_inv hi
      have hp := sub_suffix0 hsub rfl (nums_numInt _)
      obtain ⟨t, hg, ht⟩ := (hF.initLocals ya).local_type hl
      have h1 : t' = numInt τ := by simpa using hp
      have h2 : t' = numInt t := by simpa using ht
      obtain rfl := numInt_inj (h1.symm.trans h2)
      rw [List.getElem?_eq_getElem hx] at hg
      obtain rfl := Option.some.inj hg
      cases hA.typed D hD hF _ ha with
      | cons h₁ _ => exact .localTee (List.getElem?_eq_getElem hx) h₁
  · cases hty

theorem node_drop {a : SSA.Expr} {args : List BExpr} {r : Option SSA.Ar} {τs : List IntType}
    (hty : SSA.tyE (Λ.map SSA.arOf) (SSA.arOf ρ) Γ.length (.drop a) = some r)
    (hA : ArgsOk Γ ρ Λ args [a] τs) :
    TreeOk Γ ρ Λ (.op .drop args) (.drop a) r := by
  rw [SSA.tyE] at hty
  split at hty
  · cases hty
    obtain ⟨τ, rfl⟩ : ∃ τ, τs = [τ] := by
      match τs, hA.len with
      | [τ], _ => exact ⟨τ, rfl⟩
    refine TreeOk.val none rfl (fun D hD hF => ?_) (fun D hD hF it hit => ?_)
    · simp only [BExpr.lower_op]
      refine Principal.snoc_num hD (hA.principal D hD hF) (nums_numInt _) fun ya it₀ hi => ?_
      obtain ⟨t', rfl⟩ := instrOk_drop_inv hi
      exact ⟨rfl, fun _ => rfl⟩
    · obtain ⟨ps, xs, rs⟩ := it
      simp only [BExpr.lower_op] at hit
      obtain ⟨ya, m, fr, it₀, ha, hi, hsub⟩ := operands_sub hD (hA.principal D hD hF) hit
      cases hA.typed D hD hF _ ha with
      | cons h₁ _ => exact .drop h₁
  · cases hty

theorem node_nop {args : List BExpr} {r : Option SSA.Ar} {τs : List IntType}
    (hty : SSA.tyE (Λ.map SSA.arOf) (SSA.arOf ρ) Γ.length .nop = some r)
    (hA : ArgsOk Γ ρ Λ args [] τs) :
    TreeOk Γ ρ Λ (.op .nop args) .nop r := by
  rw [SSA.tyE] at hty
  cases hty
  obtain rfl : τs = [] := List.eq_nil_of_length_eq_zero hA.len
  refine TreeOk.val none rfl (fun D hD hF => ?_) (fun _ _ _ _ _ => .nop)
  simp only [BExpr.lower_op]
  refine Principal.snoc_num hD (hA.principal D hD hF) (nums_numInt []) fun ya it₀ hi => ?_
  rw [instrOk_nop_inv hi]
  exact ⟨rfl, fun _ => rfl⟩

theorem node_unreachable {args : List BExpr} {r : Option SSA.Ar}
    (hty : SSA.tyE (Λ.map SSA.arOf) (SSA.arOf ρ) Γ.length .unreachable = some r) :
    TreeOk Γ ρ Λ (.op .unreachable args) .unreachable r := by
  rw [SSA.tyE] at hty
  cases hty
  exact TreeOk.bot fun _ _ _ _ _ _ => .unreachable

theorem node_br {l : LabelIdx} {args : List BExpr} {es : List SSA.Expr} {r : Option SSA.Ar}
    {τs : List IntType}
    (hty : SSA.tyE (Λ.map SSA.arOf) (SSA.arOf ρ) Γ.length (.br l.toNat es) = some r)
    (hA : ArgsOk Γ ρ Λ args es τs) :
    TreeOk Γ ρ Λ (.op (.br l) args) (.br l.toNat es) r := by
  rw [SSA.tyE] at hty
  obtain ⟨hc, rfl⟩ := ite_some hty
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨-, hL⟩, hle⟩ := hc
  obtain ⟨lt, hΛ, hlt⟩ := label_of_map hL
  have hlen : lt.toList.length = es.length := by
    rw [toList_length_arOf, hlt]
    split <;> simp_all [arLen]; omega
  refine TreeOk.bot fun D hD hF it hit r' => ?_
  obtain ⟨ps, xs, rs⟩ := it
  simp only [BExpr.lower_op] at hit
  obtain ⟨ya, m, fr, it₀, ha, hi, hsub⟩ := operands_sub hD (hA.principal D hD hF) hit
  obtain ⟨ts, t₁, t₂, hl, rfl⟩ := instrOk_br_inv hi
  obtain ⟨lt', hΛ', hsl⟩ := (hF.initLocals ya).label hl
  rw [hΛ] at hΛ'
  obtain rfl := Option.some.inj hΛ'
  have hp := sub_suffix hsub (by rw [hsl.length_eq, List.length_map, List.length_map, hlen, hA.len])
    (nums_numInt τs)
  subst hp
  have hA' := hA.typed D hD hF _ ha
  rw [← map_numInt_inj (resultSub_nums hsl (nums_numInt τs))] at hA'
  exact .br hΛ hA'

theorem node_brIf {l : LabelIdx} {args : List BExpr} {es : List SSA.Expr} {r : Option SSA.Ar}
    {τs : List IntType}
    (hty : SSA.tyE (Λ.map SSA.arOf) (SSA.arOf ρ) Γ.length (.brIf l.toNat es) = some r)
    (hA : ArgsOk Γ ρ Λ args es τs) :
    TreeOk Γ ρ Λ (.op (.brIf l) args) (.brIf l.toNat es) r := by
  rw [SSA.tyE] at hty
  obtain ⟨hc, rfl⟩ := ite_some hty
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hc
  obtain ⟨⟨-, h12⟩, hL⟩ := hc
  obtain ⟨lt, hΛ, hlt⟩ := label_of_map hL
  have hlen : lt.toList.length + 1 = es.length := by
    rw [toList_length_arOf, hlt]
    split <;> simp_all [arLen]
  refine TreeOk.val lt (by simp [hlt]) (fun D hD hF => ?_) (fun D hD hF it hit => ?_)
  · simp only [BExpr.lower_op]
    refine Principal.snoc_num hD (hA.principal D hD hF) (nums_numInt _) fun ya it₀ hi => ?_
    obtain ⟨ts, hl, rfl⟩ := instrOk_brIf_inv hi
    obtain ⟨lt', hΛ', hsl⟩ := (hF.initLocals ya).label hl
    rw [hΛ] at hΛ'
    obtain rfl := Option.some.inj hΛ'
    refine ⟨?_, fun hp => (resultSub_nums hsl fun v hv =>
      nums_numInt τs v (hp ▸ List.mem_append_left _ hv)).symm⟩
    simp [hsl.length_eq, hA.len, ← hlen]
  · obtain ⟨ps, xs, rs⟩ := it
    simp only [BExpr.lower_op] at hit
    obtain ⟨ya, m, fr, it₀, ha, hi, hsub⟩ := operands_sub hD (hA.principal D hD hF) hit
    obtain ⟨ts, hl, rfl⟩ := instrOk_brIf_inv hi
    obtain ⟨lt', hΛ', hsl⟩ := (hF.initLocals ya).label hl
    rw [hΛ] at hΛ'
    obtain rfl := Option.some.inj hΛ'
    have hp : ts ++ [numInt .i32] = τs.map numInt :=
      sub_suffix0 hsub (by simp [hsl.length_eq, hA.len, ← hlen]) (nums_numInt τs)
    have hts := resultSub_nums hsl fun v hv => nums_numInt τs v (hp ▸ List.mem_append_left _ hv)
    rw [← hts] at hp
    have hτ : τs = lt.toList ++ [.i32] :=
      (map_numInt_inj (by rw [← hp, List.map_append]; rfl)).symm
    subst hτ
    exact .brIf hΛ (hA.typed D hD hF _ ha)

theorem node_return {args : List BExpr} {es : List SSA.Expr} {r : Option SSA.Ar}
    {τs : List IntType}
    (hty : SSA.tyE (Λ.map SSA.arOf) (SSA.arOf ρ) Γ.length (.return_ es) = some r)
    (hA : ArgsOk Γ ρ Λ args es τs) :
    TreeOk Γ ρ Λ (.op .return_ args) (.return_ es) r := by
  rw [SSA.tyE] at hty
  obtain ⟨hc, rfl⟩ := ite_some hty
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨-, hle⟩, hR⟩ := hc
  have hlen : ρ.toList.length = es.length := by
    rw [toList_length_arOf, hR]
    split <;> simp_all [arLen]; omega
  refine TreeOk.bot fun D hD hF it hit r' => ?_
  obtain ⟨ps, xs, rs⟩ := it
  simp only [BExpr.lower_op] at hit
  obtain ⟨ya, m, fr, it₀, ha, hi, hsub⟩ := operands_sub hD (hA.principal D hD hF) hit
  obtain ⟨ts, t₁, t₂, hr, rfl⟩ := instrOk_return_inv hi
  obtain ⟨ts', hret, hsr⟩ := hF.ret
  rw [Context.initLocals_return, hret] at hr
  obtain rfl := Option.some.inj hr
  have hp := sub_suffix hsub (by rw [hsr.length_eq, List.length_map, List.length_map, hlen, hA.len])
    (nums_numInt τs)
  subst hp
  have hτ := map_numInt_inj (resultSub_nums hsr (nums_numInt τs))
  subst hτ
  exact .return_ (hA.typed D hD hF _ ha)

theorem node_instr {i : Instr} {args : List BExpr} {es : List SSA.Expr} {e : SSA.Expr}
    {r : Option SSA.Ar} {τs : List IntType} (h : SSA.ofInstr? i es = some e)
    (hty : SSA.tyE (Λ.map SSA.arOf) (SSA.arOf ρ) Γ.length e = some r)
    (hA : ArgsOk Γ ρ Λ args es τs) : TreeOk Γ ρ Λ (.op i args) e r := by
  unfold SSA.ofInstr? at h
  split at h <;> (try split at h) <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
  all_goals first
    | exact node_op (by first | rfl | simp [SSA.ofInstr?, *]) hty hA
    | exact node_localGet hty hA
    | exact node_localSet hty hA
    | exact node_localTee hty hA
    | exact node_drop hty hA
    | exact node_nop hty hA
    | exact node_unreachable hty
    | exact node_br hty hA
    | exact node_brIf hty hA
    | exact node_return hty hA

theorem node_block {bt : BlockType} {body : List BExpr} {ty : Option IntType}
    {body' : List SSA.Expr} {r : Option SSA.Ar} (hbt : SSA.ofBlockType? bt = some ty)
    (hty : SSA.tyE (Λ.map SSA.arOf) (SSA.arOf ρ) Γ.length (.block ty body') = some r)
    (hS : SeqGoal Γ ρ (ty :: Λ) body body' ty) :
    TreeOk Γ ρ Λ (.block bt body) (.block ty body') r := by
  rw [SSA.tyE] at hty
  obtain ⟨-, rfl⟩ := ite_some hty
  refine TreeOk.val ty rfl (fun D hD hF => ?_) (fun D hD hF it hit => ?_)
  · show Principal D ([] ++ [_]) _
    refine Principal.snoc_num hD (Principal.nil hD) (by simp) fun ya it₀ hi => ?_
    obtain ⟨t₁, t₂, hb, rfl⟩ := instrOk_block_inv hi
    obtain ⟨rfl, rfl⟩ := blockTypeOk_frag hbt hb
    exact ⟨rfl, fun _ => rfl⟩
  · have hit : InstrsOk D [.block bt (BExpr.lowerList body)] it := hit
    obtain ⟨_, it₀, hi, -⟩ := InstrsOk.single_inv hD hit
    obtain ⟨t₁, t₂, xs, hb, hbody, -⟩ := instrOk_block_body hi
    obtain ⟨rfl, rfl⟩ := blockTypeOk_frag hbt hb
    exact .block (hS _ (wf_withLabel_numInt hD ty) (hF.withLabel ty) xs _ (ResultSub.refl _ _) hbody)

theorem node_loop {bt : BlockType} {body : List BExpr} {ty : Option IntType}
    {body' : List SSA.Expr} {r : Option SSA.Ar} (hbt : SSA.ofBlockType? bt = some ty)
    (hty : SSA.tyE (Λ.map SSA.arOf) (SSA.arOf ρ) Γ.length (.loop ty body') = some r)
    (hS : SeqGoal Γ ρ (none :: Λ) body body' ty) :
    TreeOk Γ ρ Λ (.loop bt body) (.loop ty body') r := by
  rw [SSA.tyE] at hty
  obtain ⟨-, rfl⟩ := ite_some hty
  refine TreeOk.val ty rfl (fun D hD hF => ?_) (fun D hD hF it hit => ?_)
  · show Principal D ([] ++ [_]) _
    refine Principal.snoc_num hD (Principal.nil hD) (by simp) fun ya it₀ hi => ?_
    obtain ⟨t₁, t₂, hb, rfl⟩ := instrOk_loop_inv hi
    obtain ⟨rfl, rfl⟩ := blockTypeOk_frag hbt hb
    exact ⟨rfl, fun _ => rfl⟩
  · have hit : InstrsOk D [.loop bt (BExpr.lowerList body)] it := hit
    obtain ⟨_, it₀, hi, -⟩ := InstrsOk.single_inv hD hit
    obtain ⟨t₁, t₂, xs, hb, hbody, -⟩ := instrOk_loop_body hi
    obtain ⟨rfl, rfl⟩ := blockTypeOk_frag hbt hb
    exact .loop (hS (D.withLabel ((none : Option IntType).toList.map numInt))
      (wf_withLabel_numInt hD none) (hF.withLabel none) xs _ (ResultSub.refl _ _) hbody)

theorem node_if {bt : BlockType} {c : BExpr} {t el : List BExpr} {ty : Option IntType}
    {c' : SSA.Expr} {t' e' : List SSA.Expr} {r : Option SSA.Ar}
    (hbt : SSA.ofBlockType? bt = some ty)
    (hty : SSA.tyE (Λ.map SSA.arOf) (SSA.arOf ρ) Γ.length (.if_ ty c' t' e') = some r)
    (hC : TreeOk Γ ρ Λ c c' (some .one))
    (hS₁ : SeqGoal Γ ρ (ty :: Λ) t t' ty) (hS₂ : SeqGoal Γ ρ (ty :: Λ) el e' ty) :
    TreeOk Γ ρ Λ (.if_ bt [c] t el) (.if_ ty c' t' e') r := by
  rw [SSA.tyE] at hty
  obtain ⟨-, rfl⟩ := ite_some hty
  obtain ⟨tc, htc, hPc, hTc⟩ := hC.2 .one rfl
  obtain ⟨τ, rfl⟩ := arOf_one htc
  have hPc' : ∀ D, D.Wf → Fit D Γ ρ Λ → Principal D (BExpr.lowerList [c]) [numInt τ] := by
    intro D hD hF; rw [BExpr.lowerList_singleton]; exact hPc D hD hF
  refine TreeOk.val ty rfl (fun D hD hF => ?_) (fun D hD hF it hit => ?_)
  · show Principal D (BExpr.lowerList [c] ++ [_]) _
    refine Principal.snoc_num hD (hPc' D hD hF) (nums_numInt [τ]) fun ya it₀ hi => ?_
    obtain ⟨t₁, t₂, hb, rfl⟩ := instrOk_if_inv hi
    obtain ⟨rfl, rfl⟩ := blockTypeOk_frag hbt hb
    exact ⟨rfl, fun _ => rfl⟩
  · obtain ⟨ps, xs, rs⟩ := it
    have hit : InstrsOk D (BExpr.lowerList [c] ++
        [.if_ bt (BExpr.lowerList t) (BExpr.lowerList el)]) ⟨ps, xs, rs⟩ := hit
    obtain ⟨ya, m, fr, it₀, ha, hi, hsub⟩ := operands_sub hD (hPc' D hD hF) hit
    obtain ⟨t₁, t₂, xs₁, xs₂, hb, hb₁, hb₂, rfl⟩ := instrOk_if_body hi
    obtain ⟨rfl, rfl⟩ := blockTypeOk_frag hbt hb
    have hp := sub_suffix0 hsub rfl (nums_numInt [τ])
    obtain rfl : τ = .i32 := (numInt_inj (List.cons.inj hp).1).symm
    rw [BExpr.lowerList_singleton] at ha
    exact .if_ (hTc D hD hF _ ha)
      (hS₁ _ (wf_withLabel_numInt (hD.initLocals ya) ty) ((hF.initLocals ya).withLabel ty) xs₁ _
        (ResultSub.refl _ _) hb₁)
      (hS₂ _ (wf_withLabel_numInt (hD.initLocals ya) ty) ((hF.initLocals ya).withLabel ty) xs₂ _
        (ResultSub.refl _ _) hb₂)

/-! ## Lists -/

theorem ofBExprs_nil {bs : List BExpr} (h : SSA.ofBExprs? bs = some []) : bs = [] := by
  cases bs with
  | nil => rfl
  | cons b bs =>
    cases hb : SSA.ofBExpr? b <;> cases hbs : SSA.ofBExprs? bs <;>
      simp [SSA.ofBExprs?, hb, hbs] at h

theorem ofBExprs_cons {b : BExpr} {bs : List BExpr} {es : List SSA.Expr}
    (h : SSA.ofBExprs? (b :: bs) = some es) :
    ∃ e es', SSA.ofBExpr? b = some e ∧ SSA.ofBExprs? bs = some es' ∧ es = e :: es' := by
  cases hb : SSA.ofBExpr? b <;> cases hbs : SSA.ofBExprs? bs <;>
    simp [SSA.ofBExprs?, hb, hbs] at h
  exact ⟨_, _, rfl, rfl, h.symm⟩

theorem arFits_some {a : SSA.Ar} {o : Option (Option SSA.Ar)} (h : SSA.arFits a o = true) :
    ∃ x, o = some x ∧ SSA.arFits a (some x) = true := by
  cases o with
  | none => simp [SSA.arFits] at h
  | some x => exact ⟨x, rfl, h⟩

theorem arFits_none {a : SSA.Ar} (h : SSA.arFits a (some (some .none)) = true) : a = .none := by
  cases a <;> simp_all [SSA.arFits]

theorem arFits_one {a : SSA.Ar} (h : SSA.arFits a (some (some .one)) = true) : a = .one := by
  cases a <;> simp_all [SSA.arFits]

end

/-! ## The assembly -/

section
variable {Γ : List IntType} {ρ : Option IntType}

set_option linter.unusedSectionVars false in
mutual

/-- **Trees.** -/
theorem tree_ok : ∀ (b : BExpr) (e : SSA.Expr) (Λ : List (Option IntType)) (r : Option SSA.Ar),
    SSA.ofBExpr? b = some e → SSA.tyE (Λ.map SSA.arOf) (SSA.arOf ρ) Γ.length e = some r →
    TreeOk Γ ρ Λ b e r
  | .op i args, e, Λ, r, h, hty => by
    cases hes : SSA.ofBExprs? args with
    | none => simp [SSA.ofBExpr?, hes] at h
    | some es =>
      simp only [SSA.ofBExpr?, hes] at h
      obtain ⟨τs, hA⟩ := args_ok args es Λ hes (ofInstr_tyArgs h hty)
      exact node_instr h hty hA
  | .block bt body, e, Λ, r, h, hty => by
    cases hty' : SSA.ofBlockType? bt with
    | none => simp [SSA.ofBExpr?, hty'] at h
    | some ty =>
    cases hb : SSA.ofBExprs? body with
    | none => simp [SSA.ofBExpr?, hty', hb] at h
    | some body' =>
    simp [SSA.ofBExpr?, hty', hb] at h
    subst h
    have hc := hty
    rw [SSA.tyE] at hc
    obtain ⟨x, hx, hf⟩ := arFits_some (ite_some hc).1
    exact node_block hty' hty (seq_ok body body' (ty :: Λ) ty x hb hx hf)
  | .loop bt body, e, Λ, r, h, hty => by
    cases hty' : SSA.ofBlockType? bt with
    | none => simp [SSA.ofBExpr?, hty'] at h
    | some ty =>
    cases hb : SSA.ofBExprs? body with
    | none => simp [SSA.ofBExpr?, hty', hb] at h
    | some body' =>
    simp [SSA.ofBExpr?, hty', hb] at h
    subst h
    have hc := hty
    rw [SSA.tyE] at hc
    obtain ⟨x, hx, hf⟩ := arFits_some (ite_some hc).1
    exact node_loop hty' hty (seq_ok body body' (none :: Λ) ty x hb hx hf)
  | .if_ bt cond t el, e, Λ, r, h, hty => by
    rcases cond with _ | ⟨c, _ | ⟨c₂, cs⟩⟩
    · simp [SSA.ofBExpr?] at h
    swap
    · simp [SSA.ofBExpr?] at h
    cases hty' : SSA.ofBlockType? bt with
    | none => simp [SSA.ofBExpr?, hty'] at h
    | some ty =>
    cases hc : SSA.ofBExpr? c with
    | none => simp [SSA.ofBExpr?, hty', hc] at h
    | some c' =>
    cases ht : SSA.ofBExprs? t with
    | none => simp [SSA.ofBExpr?, hty', hc, ht] at h
    | some t' =>
    cases he : SSA.ofBExprs? el with
    | none => simp [SSA.ofBExpr?, hty', hc, ht, he] at h
    | some e' =>
    simp [SSA.ofBExpr?, hty', hc, ht, he] at h
    subst h
    have hk := hty
    rw [SSA.tyE] at hk
    have hk' := (ite_some hk).1
    simp only [Bool.and_eq_true, beq_iff_eq] at hk'
    obtain ⟨⟨hcty, h₁⟩, h₂⟩ := hk'
    obtain ⟨x₁, hx₁, hf₁⟩ := arFits_some h₁
    obtain ⟨x₂, hx₂, hf₂⟩ := arFits_some h₂
    exact node_if hty' hty (tree_ok c c' Λ _ hc hcty)
      (seq_ok t t' (ty :: Λ) ty x₁ ht hx₁ hf₁) (seq_ok el e' (ty :: Λ) ty x₂ he hx₂ hf₂)
  | .tryTable .., e, Λ, r, h, hty => by simp [SSA.ofBExpr?] at h

/-- **Operand lists.** -/
theorem args_ok : ∀ (bs : List BExpr) (es : List SSA.Expr) (Λ : List (Option IntType)),
    SSA.ofBExprs? bs = some es → SSA.tyArgs (Λ.map SSA.arOf) (SSA.arOf ρ) Γ.length es = true →
    ∃ τs, ArgsOk Γ ρ Λ bs es τs
  | [], es, Λ, h, _ => by
    simp [SSA.ofBExprs?] at h
    subst h
    exact ⟨[], ⟨rfl, fun D hD _ => Principal.nil hD, fun _ _ _ _ _ => .nil⟩⟩
  | b :: bs, es, Λ, h, ht => by
    obtain ⟨e, es', hb, hbs, rfl⟩ := ofBExprs_cons h
    simp only [SSA.tyArgs, Bool.and_eq_true, beq_iff_eq] at ht
    obtain ⟨t, ht1, hP, hT⟩ := (tree_ok b e Λ _ hb ht.1).2 .one rfl
    obtain ⟨τ, rfl⟩ := arOf_one ht1
    obtain ⟨τs, hA⟩ := args_ok bs es' Λ hbs ht.2
    refine ⟨τ :: τs, ⟨by simp [hA.len], fun D hD hF => ?_, fun D hD hF it hit => ?_⟩⟩
    · rw [BExpr.lowerList_cons]
      exact Principal.append (a := [numInt τ]) hD (hP D hD hF)
        fun ya => hA.principal _ (hD.initLocals ya) (hF.initLocals ya)
    · obtain ⟨ps, xs, rs⟩ := it
      rw [BExpr.lowerList_cons] at hit
      obtain ⟨m, ya, yb, ha, hb', -⟩ := InstrsOk.split hD hit rfl
      exact .cons (hT D hD hF _ ha) (hA.typed _ (hD.initLocals ya) (hF.initLocals ya) _ hb')

/-- **Bodies.** -/
theorem seq_ok : ∀ (bs : List BExpr) (es : List SSA.Expr) (Λ : List (Option IntType))
    (ty : Option IntType) (x : Option SSA.Ar),
    SSA.ofBExprs? bs = some es → SSA.tySeq (Λ.map SSA.arOf) (SSA.arOf ρ) Γ.length es = some x →
    SSA.arFits (SSA.arOf ty) (some x) = true → SeqGoal Γ ρ Λ bs es ty
  | [], es, Λ, ty, x, h, hx, hf => by
    simp [SSA.ofBExprs?] at h
    subst h
    rw [SSA.tySeq] at hx
    cases hx
    obtain rfl := arOf_none (arFits_none hf)
    exact fun _ _ _ _ _ _ _ => .nil
  | b :: bs, es, Λ, ty, x, h, hx, hf => by
    obtain ⟨e, es', hb, hbs, rfl⟩ := ofBExprs_cons h
    intro D hD hF xs T hT hit
    rw [BExpr.lowerList_cons] at hit
    obtain ⟨m, ya, yb, ha, hb', -⟩ := InstrsOk.split hD hit rfl
    rw [SSA.tySeq] at hx
    cases hte : SSA.tyE (Λ.map SSA.arOf) (SSA.arOf ρ) Γ.length e with
    | none => rw [hte] at hx; cases hx
    | some r =>
      rw [hte] at hx
      have hTr := tree_ok b e Λ r hb hte
      cases r with
      | none => exact .bot (hTr.1 rfl D hD hF _ ha)
      | some a =>
        obtain ⟨t, hta, hP, hTy⟩ := hTr.2 a rfl
        have hty := hTy D hD hF _ ha
        cases a with
        | none =>
          obtain rfl := arOf_none hta
          obtain ⟨s1, -⟩ := hP D hD hF [] ya m ha
          have hm : m = [] := by
            rcases m with _ | ⟨_, _⟩
            · rfl
            · cases s1
          subst hm
          cases es' with
          | nil =>
            rw [SSA.tySeq] at hx
            cases hx
            obtain rfl := arOf_none (arFits_none hf)
            exact .one hty
          | cons e' es'' =>
            exact .cons hty (seq_ok bs (e' :: es'') Λ ty x hbs hx hf _ (hD.initLocals ya)
              (hF.initLocals ya) yb T (by simpa using hT) hb')
        | one =>
          obtain ⟨τ, rfl⟩ := arOf_one hta
          cases es' with
          | cons _ _ => simp at hx
          | nil =>
            obtain rfl := ofBExprs_nil hbs
            have hit' : InstrsOk D b.lower ⟨[], xs, T⟩ := by simpa using hit
            obtain ⟨s1, -⟩ := hP D hD hF [] xs _ hit'
            have hT' := resultSub_nums s1 (nums_numInt [τ])
            subst hT'
            obtain rfl := toList_numInt_inj (a := ty) (b := some τ)
              (resultSub_nums hT (nums_numInt [τ]))
            exact .one hty

end

end

/-! ## Function bodies -/

/-- **A validated function body is typed.** A recognised, native-arity-checked
fragment function whose body's lowering is valid (at results below its result
type) in a well-formed Core context fitting its parameters, locals and result is
`funcTyped`. -/
theorem funcTyped_of_instrsOk {D : Context} {bf : BFunc} {f : SSA.FragFunc} (hD : D.Wf)
    (hF : Fit D (f.params ++ f.locals) f.result [f.result])
    (hb : SSA.ofBExprs? bf.body = some f.body) (hnat : f.native = true) {xs : List Nat}
    {T : List CValType} (hT : ResultSub D.toTypeCtx T (f.result.toList.map numInt))
    (hok : InstrsOk D (BExpr.lowerList bf.body) ⟨[], xs, T⟩) : funcTyped f := by
  unfold SSA.FragFunc.native at hnat
  obtain ⟨x, hx, hf⟩ := arFits_some hnat
  exact seq_ok (Γ := f.params ++ f.locals) (ρ := f.result) bf.body f.body [f.result] f.result x
    hb (by rw [List.length_append]; exact hx) hf D hD hF xs T hT hok

end Silmaril.Proofs.Wasm.Abstract.FragBody
