module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Prims.Blocktype
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Swap.Ops2
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Swap.NxTypes
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxSites.Value
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseAll.WithInst

/-!
# Round 9, RE: `$blocktype_` across erasure

`$blocktype_(z, bt)` is outside the evaluator-level erasure (`EraseAll.excluded`) because its
primitive fallback reads `MODULE.TYPES` out of `z`. At round 4's primitives it still commutes with
erasure of the state, for a block type that erasure fixes:

* `blocktype_shape`: a call that denotes something has `bt = _RESULT t?` or `bt = _IDX x`.
* `_RESULT t?` is answered by the clause, which does not read `z`.
* `_IDX x` is answered by the primitive (`Prims.blocktypeCall`), whose reads (`MODULE`, `TYPES`,
  an element that is the image of a defined type) erasure keeps; the clause still definitely
  fails on the erased state, since `$type(z, x)` still evaluates there.

`applies_blocktype_erase` is the result.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.BadRules

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies TryClausesUndef not_tryClauses_and_undef)
open Silmaril.SpecTec.Equiv.ExecBuiltins (matchExp_caseE_undef_of_ne matchExp_caseE_undef_of_notCase)
open Silmaril.SpecTec.Equiv.Validation (tyV)
open Silmaril.Wasm.SpecTec.Sim.Prims
open Silmaril.Wasm.SpecTec.Sim.Round7 (utf8Env findDef?_utf8Env_of_ne)
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (eraseV eraseVs_eq_map nxB)

/-! ## Matching, read back -/

theorem matchArg_expA_inv {env : Env} {ρ ρ' : VarEnv} {e : Exp} {v : Value}
    (h : MatchArg env ρ (.expA e) (.val v) ρ') : MatchExp env ρ e v ρ' := by
  obtain ⟨n, h⟩ := h
  rcases n with _ | n
  · simp [matchArg] at h
  · simp only [matchArg] at h
    split at h
    · exact ⟨n, h⟩
    · cases h

theorem matchArgs_cons_inv {env : Env} {ρ ρ' : VarEnv} {a : Arg} {l : List Arg} {w : ArgV}
    {ws : List ArgV} (h : MatchArgs env ρ (a :: l) (w :: ws) ρ') :
    ∃ ρ₁, MatchArg env ρ a w ρ₁ ∧ MatchArgs env ρ₁ l ws ρ' := by
  obtain ⟨n, h⟩ := h
  rcases n with _ | n
  · simp [matchArgs] at h
  · simp only [matchArgs, Bind.bind, Except.bind] at h
    cases h₁ : matchArg n env ρ a w with
    | error => rw [h₁] at h; cases h
    | ok ρ₁ =>
      rw [h₁] at h
      exact ⟨ρ₁, ⟨n, h₁⟩, ⟨n, h⟩⟩

theorem matchArgs_nil_inv {env : Env} {ρ ρ' : VarEnv} (h : MatchArgs env ρ [] [] ρ') : ρ' = ρ := by
  obtain ⟨n, h⟩ := h
  rcases n with _ | n
  · simp [matchArgs] at h
  · simp only [matchArgs] at h
    cases h
    rfl

/-- Two expression arguments matched against two values, read back. -/
theorem matchArgs2_inv {env : Env} {ρ ρ' : VarEnv} {e₁ e₂ : Exp} {a b : Value}
    (h : MatchArgs env ρ [.expA e₁, .expA e₂] [.val a, .val b] ρ') :
    ∃ ρ₁, MatchExp env ρ e₁ a ρ₁ ∧ MatchExp env ρ₁ e₂ b ρ' := by
  obtain ⟨ρ₁, h₁, h⟩ := matchArgs_cons_inv h
  obtain ⟨ρ₂, h₂, h⟩ := matchArgs_cons_inv h
  obtain rfl := matchArgs_nil_inv h
  exact ⟨ρ₁, matchArg_expA_inv h₁, matchArg_expA_inv h₂⟩

/-- A constructor pattern matched against a value, read back. -/
theorem matchExp_caseE_inv {env : Env} {ρ ρ' : VarEnv} {op : MixopS} {e : Exp} {v : Value}
    (h : MatchExp env ρ (.caseE op e) v ρ') : ∃ w, v = .case op w ∧ MatchExp env ρ e w ρ' := by
  obtain ⟨n, h⟩ := h
  rcases n with _ | n
  · simp [matchExp] at h
  · cases v with
    | case op' w =>
      simp only [matchExp, Value.asCase?, Res.ofOption_some, Bind.bind, Except.bind,
        Res.assert] at h
      split at h
      · rename_i hop
        exact ⟨w, by rw [hop], ⟨n, h⟩⟩
      · simp at h
    | _ => simp [matchExp, Value.asCase?, Res.ofOption, Bind.bind, Except.bind] at h

/-! ## The shapes of a block type a call accepts -/

variable {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
  (host : Silmaril.Wasm.Execution.Core.HostSemantics H)

/-- `$blocktype_` and `$type` in the round-7 environment. -/
theorem blocktypeDefs_utf8Env (B : Builtins) : BlocktypeDefs (utf8Env B) := by
  have D := blocktypeDefs_simEnv B
  obtain ⟨ps, t, q₁, body₁, q₂, hd⟩ := D.blocktype
  exact ⟨⟨ps, t, q₁, body₁, q₂, by rw [findDef?_utf8Env_of_ne B (by decide), hd]⟩,
    Round7.EraseAll.hasClause1_utf8Env (by decide) D.type⟩

/-- The primitive of `$blocktype_` in the round-7 environment, at round 4's primitives. -/
theorem call_blocktype_utf8 (ws : List ArgV) :
    (utf8Env (Round4Int.BI P hn host)).builtins.call "blocktype_" ws =
      Prims.call P hn host "blocktype_" ws := by
  show (if "blocktype_" = "utf8" then Round6.MemSimd.utf8Call ws else _) = _
  rw [ite_eq_right_iff.2 (fun h => absurd h (by decide))]
  rfl

/-- The primitive of `$blocktype_` at `_IDX x`. -/
theorem call_blocktype_idx_utf8 (z w : Value) :
    (utf8Env (Round4Int.BI P hn host)).builtins.call "blocktype_" [.val z, .val (.case "_IDX" w)] =
      blocktypeCall z w := by
  rw [call_blocktype_utf8]
  simp [Prims.call, IntNumeric.intCall, Floats.floatCall, Floats.floatNames]

/-- The primitive of `$blocktype_` answers only at `_IDX x`, by `blocktypeCall`. -/
theorem call_blocktype_inv {Z W v : Value}
    (h : Prims.call P hn host "blocktype_" [.val Z, .val W] = some v) :
    ∃ w, W = .case "_IDX" w ∧ blocktypeCall Z w = some v := by
  have hf : Floats.floatCall P "blocktype_" [.val Z, .val W] = none := by
    simp [Floats.floatCall, Floats.floatNames]
  have hi : IntNumeric.intCall "blocktype_" [.val Z, .val W] = none := by
    simp [IntNumeric.intCall]
  cases W with
  | case op w =>
    by_cases hop : op = "_IDX"
    · subst hop
      exact ⟨w, rfl, by simpa [Prims.call, hf, hi] using h⟩
    · simp [Prims.call, hf, hi, hop] at h
  | _ => simp [Prims.call, hf, hi] at h

/-- **A call of `$blocktype_` that denotes something is at `_RESULT t?` or `_IDX x`.** -/
theorem blocktype_shape {Z W v : Value}
    (h : Applies (utf8Env (Round4Int.BI P hn host)) "blocktype_" [.val Z, .val W] v) :
    (∃ o, W = .case "_RESULT" (.opt o)) ∨ (∃ w, W = .case "_IDX" w) := by
  obtain ⟨ps', t', q₁, body₁, q₂, hd'⟩ := (blocktypeDefs_utf8Env (Round4Int.BI P hn host)).blocktype
  obtain ⟨ps, t, cs, hd, hc⟩ := h
  rw [hd'] at hd
  obtain ⟨-, -, rfl⟩ : ps' = ps ∧ t' = t ∧ _ = cs := by simpa using hd
  rcases hc with ⟨n, hn'⟩ | ⟨-, hb⟩
  · rcases tryClauses_cons_elim hn' with ⟨ρ₀, ρ₁, hm, -, -⟩ | ⟨n₂, hn₂⟩
    · obtain ⟨ρ₂, -, hm₂⟩ := matchArgs2_inv hm
      obtain ⟨w, rfl, -⟩ := matchExp_caseE_inv hm₂
      exact .inr ⟨w, rfl⟩
    · rcases tryClauses_cons_elim hn₂ with ⟨ρ₀, ρ₁, hm, -, -⟩ | ⟨n₃, hn₃⟩
      · obtain ⟨ρ₂, -, hm₂⟩ := matchArgs2_inv hm
        obtain ⟨w, rfl, hw⟩ := matchExp_caseE_inv hm₂
        rcases Silmaril.SpecTec.Equiv.Execution.matchExp_iterE_opt_iff.1 hw with
          ⟨rfl, -⟩ | ⟨u, -, -, rfl, -⟩
        · exact .inl ⟨none, rfl⟩
        · exact .inl ⟨some u, rfl⟩
      · cases n₃ <;> simp [tryClauses] at hn₃
  · rw [call_blocktype_utf8] at hb
    obtain ⟨w, rfl, -⟩ := call_blocktype_inv P hn host hb
    exact .inr ⟨w, rfl⟩

/-! ## Erasure -/

theorem eraseV_instrTypeV (a b : List Value) :
    eraseV (Exn.instrTypeV a b) = Exn.instrTypeV (a.map eraseV) (b.map eraseV) := by
  simp [Exn.instrTypeV, eraseV, eraseVs_eq_map]

theorem eraseV_tyV {k : Validation.TKind} (t : Validation.Ty k) : eraseV (tyV t) = tyV t :=
  Round7.Swap.eraseV_of_nxB _ (Round7.Swap.nxB_tyV t)

theorem map_eraseV_tyV {k : Validation.TKind} (l : List (Validation.Ty k)) :
    (l.map tyV).map eraseV = l.map tyV := by
  simp [eraseV_tyV]

/-- `mapM tyInv` succeeds only on a list of images. -/
theorem mapM_tyInv_eq_some {k : Validation.TKind} :
    ∀ {Ts : List Value} {ds : List (Validation.Ty k)}, Ts.mapM (tyInv k) = some ds →
      Ts = ds.map tyV
  | [], ds, h => by simp at h; subst h; rfl
  | T :: Ts, ds, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨d, hd, ds', hds', rfl⟩ := h
    rw [List.map_cons, tyInv_eq_some hd, mapM_tyInv_eq_some hds']

/-- What `blocktypeCall` reads. -/
theorem blocktypeCall_inv {Z w v : Value} (h : blocktypeCall Z w = some v) :
    ∃ (S F M : Value) (ds : List Silmaril.Wasm.Validation.DefType) (x : Silmaril.Wasm.TypeIdx)
      (d : Silmaril.Wasm.Validation.DefType)
      (p : List Silmaril.Wasm.Validation.CValType × List Silmaril.Wasm.Validation.CValType),
      Z = stV S F ∧
      F.field? "MODULE" = some M ∧ M.field? "TYPES" = some (.list (ds.map tyV)) ∧
      w = Encode.toValue x ∧ ds[x.toNat]? = some d ∧ Validation.DefType.funcType? d = some p ∧
      v = Exn.instrTypeV (p.1.map tyV) (p.2.map tyV) := by
  unfold blocktypeCall at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨Ts, hT, ds, hds, x, hx, d, hd, p, hp, rfl⟩ := h
  have hTs := mapM_tyInv_eq_some hds
  subst hTs
  unfold moduleTypesV? at hT
  split at hT
  · rename_i S F
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hT
    obtain ⟨M, hM, T, hT', hl⟩ := hT
    have hTl : T = .list (ds.map tyV) := by
      cases T <;> simp_all [Value.asList?]
    subst hTl
    exact ⟨S, F, M, ds, x, d, p, rfl, hM, hT', (Encode.toValue_ofValue _ _ hx).symm, hd, hp, rfl⟩
  · cases hT

/-- `$type(z, x)` at a state whose frame's module lists the type images `ds`. -/
theorem evalExp_type_gen {env : Env} (D : BlocktypeDefs env) (S : State.StateDefs env)
    {Sv F M : Value} {ds : List Validation.DefType} {x : Wasm.TypeIdx} {d : Validation.DefType}
    (hF : F.field? "MODULE" = some M) (hM : M.field? "TYPES" = some (.list (ds.map tyV)))
    (hx : ds[x.toNat]? = some d) :
    EvalExp env ((VarEnv.empty.bindVal "z" (stV Sv F)).bindVal "x" (Encode.toValue x))
      (.callE "type" [.expA (.varE "z"), .expA (.varE "x")]) (tyV d) :=
  State.evalExp_call1 D.type rfl (Equiv.evalArgs_cons (evalExp_var rfl)
      (Equiv.evalArgs_cons (evalExp_var rfl) Equiv.evalArgs_nil)) State.matchArgs_zxPat
    (evalExp_idxE_iff.2 ⟨_, x.toNat, evalExp_dotE_iff.2 ⟨_, evalExp_dotE_iff.2 ⟨_,
      State.evalExp_fof S rfl (evalExp_var rfl), hF⟩, hM⟩, State.evalExp_idxPayload rfl,
      by simp [Value.idx?, hx]⟩)

/-- `$blocktype_(z, _IDX x)`'s clauses definitely fail once `$type(z, x)` evaluates. -/
theorem blocktype_idx_undef_gen {env : Env} (D : BlocktypeDefs env) {Z w u : Value}
    (ht : EvalExp env ((VarEnv.empty.bindVal "z" Z).bindVal "x" w)
      (.callE "type" [.expA (.varE "z"), .expA (.varE "x")]) u) :
    ∃ ps t cs, env.findDef? "blocktype_" = some (ps, t, cs) ∧
      TryClausesUndef env cs [.val Z, .val (.case "_IDX" w)] := by
  obtain ⟨ps, t, q₁, body₁, q₂, hd⟩ := D.blocktype
  refine ⟨ps, t, _, hd, IntNumeric.tryClausesUndef_skip_prem
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons (matchArg_expA
      (matchExp_caseE (matchExp_varE rfl))) matchArgs_nil)) ?_
    (IntNumeric.tryClausesUndef_skip_match matchArgsUndef_result IntNumeric.tryClausesUndef_nil)⟩
  exact premsUndef_rule (ws := []) Equiv.evalArgs_nil (evalExpUndef_tup (pre := [_]) (post := [])
    (evalExps_cons ht evalExps_nil)
    (evalExpUndef_case (evalExpUndef_tup (pre := []) evalExps_nil (evalExpUndef_case
      (evalExpUndef_tup (pre := []) (post := []) evalExps_nil
        (evalExpUndef_iterList (evalExpUndef_var rfl)))))))

/-- **`$blocktype_` commutes with erasure of the state**, at a block type that erasure fixes. -/
theorem applies_blocktype_erase {Z W v : Value} (hW : eraseV W = W)
    (h : Applies (utf8Env (Round4Int.BI P hn host)) "blocktype_" [.val Z, .val W] v) :
    Applies (utf8Env (Round4Int.BI P hn host)) "blocktype_" [.val (eraseV Z), .val W]
      (eraseV v) := by
  have D := blocktypeDefs_utf8Env (Round4Int.BI P hn host)
  rcases blocktype_shape P hn host h with ⟨o, rfl⟩ | ⟨w, rfl⟩
  · have hv := Applies.unique h (applies_blocktypeResult D Z o)
    subst hv
    have ho : o.map eraseV = o := by
      cases o with
      | none => rfl
      | some u =>
        simp only [eraseV, Value.case.injEq, Value.opt.injEq, true_and] at hW
        simp [hW]
    have he : eraseV (Exn.instrTypeV [] o.toList) = Exn.instrTypeV [] o.toList := by
      rw [eraseV_instrTypeV]
      cases o with
      | none => rfl
      | some u =>
        simp only [Option.map_some, Option.some.injEq] at ho
        simp [ho]
    rw [he]
    exact applies_blocktypeResult D _ o
  · obtain ⟨ps', t', cs', hd', hn'⟩ := not_tryClauses_blocktypeIdx D (Z := Z) (w := w) (v := v)
    obtain ⟨ps, t, cs, hd, hc⟩ := h
    rw [hd'] at hd
    obtain ⟨rfl, rfl, rfl⟩ : ps' = ps ∧ t' = t ∧ cs' = cs := by simpa using hd
    have hb : Prims.call P hn host "blocktype_" [.val Z, .val (.case "_IDX" w)] = some v := by
      rcases hc with hc | ⟨-, hb⟩
      · exact absurd hc hn'
      · rwa [call_blocktype_utf8] at hb
    obtain ⟨w', hw', hbc⟩ := call_blocktype_inv P hn host hb
    obtain rfl : w = w' := by simpa using hw'
    obtain ⟨S, F, M, ds, x, d, p, rfl, hF, hM, rfl, hx, hp, rfl⟩ := blocktypeCall_inv hbc
    have hv : eraseV (Exn.instrTypeV (p.1.map tyV) (p.2.map tyV)) =
        Exn.instrTypeV (p.1.map tyV) (p.2.map tyV) := by
      rw [eraseV_instrTypeV, map_eraseV_tyV, map_eraseV_tyV]
    rw [hv]
    have hZ : eraseV (stV S F) = stV (eraseV S) (eraseV F) := by
      simp [stV, eraseV, eraseVs_eq_map]
    have hF' : (eraseV F).field? "MODULE" = some (eraseV M) := by
      rw [Round7.Swap.field?_eraseV (by decide), hF]; rfl
    have hM' : (eraseV M).field? "TYPES" = some (.list (ds.map tyV)) := by
      rw [Round7.Swap.field?_eraseV (by decide), hM]
      simp [eraseV, eraseVs_eq_map, eraseV_tyV]
    obtain ⟨ps₂, t₂, cs₂, hd₂, hu⟩ := blocktype_idx_undef_gen D
      (evalExp_type_gen D (Round7.EraseAll.stateDefs_utf8Env _) hF' hM' hx)
    rw [hd'] at hd₂
    obtain ⟨rfl, rfl, rfl⟩ : ps' = ps₂ ∧ t' = t₂ ∧ cs' = cs₂ := by simpa using hd₂
    refine ⟨ps', t', cs', hd', Or.inr ⟨hZ ▸ hu, ?_⟩⟩
    rw [hZ, call_blocktype_idx_utf8]
    simp only [blocktypeCall, moduleTypesV?, Option.bind_eq_bind, hF']
    rw [Option.bind_some, hM']
    simp only [Value.asList?, Option.bind_some, Prims.mapM_tyInv, Encode.ofValue_toValue, hx, hp]

end Silmaril.Wasm.SpecTec.Sim.Round9.BadRules
