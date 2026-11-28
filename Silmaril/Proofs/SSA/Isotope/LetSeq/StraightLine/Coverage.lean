module

public import Silmaril.SSA.Isotope.LetSeq.StraightLine.Defs
import Silmaril.Proofs.SSA.Isotope.LetSeq.StraightLine.PureAssembly

import Silmaril.Proofs.SSA.Isotope.LetSeq.StraightLine.ProductReflection
import Silmaril.Proofs.SSA.Isotope.LetSeq.StraightLine.Replay

import Silmaril.SSA.Isotope.LetSeq.StraightLine.Binders.Thms

public section

namespace Silmaril.Isotope.LetSeq.StraightLine

open LocallyNameless (Derivation Equiv HasType Pure Tm)

open Binders

set_option backward.isDefEq.respectTransparency false

private def renameAssembly {n m : Nat} {β : BoundCtx Types n} {γ : BoundCtx Types m} {A : Types}
    (ρ : BoundCtx.Renaming β γ) : Assembly β A → Assembly γ A
  | .slot i => .slot ⟨ρ.toFun i.1, (ρ.typed i.1).trans i.2⟩
  | .unit => .unit
  | .pair a b => .pair (renameAssembly ρ a) (renameAssembly ρ b)

private theorem renamedAssembly_term {n m : Nat} {β : BoundCtx Types n} {γ : BoundCtx Types m}
    {A : Types} (ρ : BoundCtx.Renaming β γ) (v : Assembly β A) :
    (renameAssembly ρ v).term = v.term.rename ρ.toFun := by
  induction v with
  | slot | unit => rfl
  | pair _ _ iha ihb => simp only [renameAssembly, Assembly.term, Tm.rename, iha, ihb]

private theorem rename_substituted {n m k : Nat} {source : BoundCtx Types n} {target : BoundCtx Types m}
    {γ : BoundCtx Types k} (σ : AssemblyEnv source target) (ρ : BoundCtx.Renaming target γ)
    (t : Term n) :
    (t.bsubst σ.terms).rename ρ.toFun = t.bsubst (AssemblyEnv.terms (fun i => renameAssembly ρ (σ i))) := by
  rw [Tm.rename_bsubst]
  exact Tm.bsubst_congr (fun i => (renamedAssembly_term ρ (σ i)).symm) t

private theorem normalized_of_equiv {n : Nat} {β : BoundCtx Types n} {t u : Term n} {A : Types}
    (h : Equiv false Γ₀ β t u A) (hu : ProductNormalizes β u A) :
    ProductNormalizes β t A := by
  obtain ⟨v, w, replay⟩ := hu
  exact ⟨v, w, h.trans replay⟩

private def replyRenaming {n : Nat} (β : BoundCtx Types n) :
    BoundCtx.Renaming β ((β.snoc Atom).snoc Atom) :=
  (BoundCtx.Renaming.succ β Atom).comp (BoundCtx.Renaming.succ (β.snoc Atom) Atom)

private theorem up_reply {n : Nat} (β : BoundCtx Types n) (k : Term (n + 1)) :
    k.underBinder.underBinder = k.rename (Tm.up (replyRenaming β).toFun) := by
  rw [Tm.underBinder, Tm.underBinder, Tm.rename_comp]
  exact Tm.rename_congr (Fin.cases rfl (fun _ => rfl)) k

private theorem bind_normalizes {n : Nat} {β : BoundCtx Types n}
    {t : Term n} {k : Term (n + 1)} {A B : Types} (p : ProductCanonical β t A)
    (dk : HasType Request Γ₀ (β.snoc A) k B)
    (cont : ∀ {m : Nat} {γ : BoundCtx Types m} (ρ : BoundCtx.Renaming β γ) (v : Assembly γ A),
      ProductNormalizes γ (Tm.instantiate (k.rename (Tm.up ρ.toFun)) v.term) B) :
    ProductNormalizes β (.let₁ t k) B := by
  induction p with
  | result v =>
    have next := cont (BoundCtx.Renaming.id _) v
    simp only [BoundCtx.Renaming.id, Tm.up_id, Tm.rename_id] at next
    exact normalized_of_equiv (Equiv.letBeta (assembly_pure v) v.derivation.toHasType dk) next
  | @step _ β A body f arg rest ih =>
    have moved : ∀ {m : Nat} {γ : BoundCtx Types m}
        (ρ : BoundCtx.Renaming ((β.snoc Atom).snoc Atom) γ) (v : Assembly γ A),
        ProductNormalizes γ
          (Tm.instantiate (k.underBinder.underBinder.rename (Tm.up ρ.toFun)) v.term) B := by
      intro m γ ρ v
      rw [up_reply, Tm.rename_comp, ← Tm.up_comp]
      exact cont ((replyRenaming β).comp ρ) v
    obtain ⟨u, normal, replay⟩ := ih dk.underBinder.underBinder moved
    have request := HasType.op (f := f) arg.derivation.toHasType
    have distribute := Equiv.bindLetPair (pureEff := false) request rest.derivation.toHasType dk
    exact ⟨_, .step f arg normal, distribute.trans (.let₂ (.refl request) replay)⟩

private theorem rename_open_assembly {n m k : Nat} {source : BoundCtx Types n}
    {target : BoundCtx Types m} {γ : BoundCtx Types k}
    (σ : AssemblyEnv source target) (ρ : BoundCtx.Renaming target γ)
    (body : Term (n + 1)) :
    (body.bsubst (Tm.upSub σ.terms)).rename (Tm.up ρ.toFun) =
      body.bsubst (Tm.upSub (AssemblyEnv.terms (fun i => renameAssembly ρ (σ i)))) := by
  rw [rename_open_substitution]
  congr 2
  exact funext fun i => (renamedAssembly_term ρ (σ i)).symm

private theorem rename_open_pair_assembly {n m k : Nat} {source : BoundCtx Types n}
    {target : BoundCtx Types m} {γ : BoundCtx Types k}
    (σ : AssemblyEnv source target) (ρ : BoundCtx.Renaming target γ)
    (body : Term (n + 2)) :
    (body.bsubst (Tm.upSub (Tm.upSub σ.terms))).rename (Tm.up (Tm.up ρ.toFun)) =
      body.bsubst (Tm.upSub (Tm.upSub (AssemblyEnv.terms (fun i => renameAssembly ρ (σ i))))) := by
  rw [rename_open_substitution]
  congr 1
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  simp only [Tm.upSub_succ]
  apply congrArg Tm.lift
  refine Fin.cases rfl (fun j => ?_) j
  simp only [Tm.upSub_succ, Tm.rename_lift]
  exact congrArg Tm.lift (renamedAssembly_term ρ (σ j)).symm

private theorem request_normalizes {n : Nat} {β : BoundCtx Types n} (f : Request) (a : Assembly β Packet) :
    ProductNormalizes β (.op f a.term) Packet := by
  let reply : Assembly ((β.snoc Atom).snoc Atom) Packet :=
    .pair (.slot ⟨1, rfl⟩) (.slot ⟨0, rfl⟩)
  exact ⟨_, .step f a (.result reply), (Equiv.pairEta (HasType.op (f := f) a.derivation.toHasType)).symm⟩

/-- Every exact native derivation normalizes after assigning assemblies to
its input variables. The proof follows the native constructors. -/
theorem normalize_exact_proof {n m : Nat} {source : BoundCtx Types n} {target : BoundCtx Types m}
    {t : Term n} {A : Types} (d : Derivation Request Γ₀ source t A) (σ : AssemblyEnv source target) :
    ProductNormalizes target (t.bsubst σ.terms) A := by
  induction d generalizing m with
  | @fv _ _ x _ _ => exact x.elim
  | bv => exact ⟨_, .result (σ _), .refl (σ _).derivation.toHasType⟩
  | unit => exact ⟨_, .result .unit, .unit⟩
  | @op _ _ f a arg iha =>
    obtain ⟨u, norm, replay⟩ := iha σ
    have k : HasType Request Γ₀ (target.snoc Packet) (.op f (.bv 0)) Packet := .op .bv
    apply normalized_of_equiv (Equiv.op (f := f) replay)
    have split := (Equiv.letEta (pureEff := false) (HasType.op (f := f) norm.derivation.toHasType)).symm.trans
      (Equiv.bindOp norm.derivation.toHasType (HasType.bv (i := 0)))
    apply normalized_of_equiv (split.trans (.let₁ (.refl norm.derivation.toHasType) (Equiv.letEta k)))
    apply bind_normalizes norm k
    intro _ γ ρ v
    exact request_normalizes f v
  | @let₁ _ _ a b A B da db iha ihb =>
    obtain ⟨u, norm, replay⟩ := iha σ
    have body := db.toHasType.bsubst ((terms_typed σ).up A)
    apply normalized_of_equiv (.let₁ replay (.refl body))
    apply bind_normalizes norm body
    intro _ γ ρ v
    rw [rename_open_assembly, instantiate_assembly]
    exact ihb (extend (fun i => renameAssembly ρ (σ i)) v)
  | @let₂ _ _ a b A B C da db iha ihb =>
    obtain ⟨u, norm, replay⟩ := iha σ
    have body := db.toHasType.bsubst (((terms_typed σ).up A).up B)
    have expand := Equiv.bindPair (pureEff := false) norm.derivation.toHasType body
    apply normalized_of_equiv ((Equiv.let₂ replay (.refl body)).trans expand)
    apply bind_normalizes norm (HasType.let₂ .bv body.underTwoBinders)
    intro _ γ ρ v
    cases v with
    | pair left right =>
      rw [open_pack_continuation, rename_open_pair_assembly]
      let env : AssemblyEnv _ γ := fun i => renameAssembly ρ (σ i)
      exact normalized_of_equiv (replay_assembled_pair env left right db.toHasType)
        (ihb (extend (extend env left) right))
  | @pair _ _ a b A B da db iha ihb =>
    obtain ⟨u, norm, replay⟩ := iha σ
    have right := db.toHasType.bsubst (terms_typed σ)
    have pairType : HasType Request Γ₀ ((target.snoc A).snoc B)
        (.pair (.bv 1) (.bv 0)) (.product A B) := .pair .bv .bv
    have steps := (Equiv.pairEta (pureEff := false) (HasType.pair norm.derivation.toHasType right)).symm.trans
      (Equiv.pairBeta norm.derivation.toHasType right pairType)
    apply normalized_of_equiv ((Equiv.pair replay (.refl right)).trans steps)
    apply bind_normalizes norm (HasType.let₁ right.lift pairType)
    intro _ γ ρ v
    rw [open_left_pair]
    obtain ⟨u', norm', replay'⟩ := ihb (fun i => renameAssembly ρ (σ i))
    rw [← rename_substituted σ ρ b] at replay'
    have pairRight : HasType Request Γ₀ (γ.snoc B) (.pair v.term.lift (.bv 0)) (.product A B) :=
      .pair v.derivation.toHasType.lift .bv
    apply normalized_of_equiv (.let₁ replay' (.refl pairRight))
    apply bind_normalizes norm' pairRight
    intro _ _ ρ' w
    rw [open_right_pair, ← renamedAssembly_term ρ' v]
    exact ⟨_, .result (.pair (renameAssembly ρ' v) w), .refl (.pair
      (renameAssembly ρ' v).derivation.toHasType w.derivation.toHasType)⟩

private def packedInput : Assembly ((input.snoc Atom).snoc Atom) Packet :=
  .pair (.slot ⟨1, rfl⟩) (.slot ⟨0, rfl⟩)

private def splitInput : AssemblyEnv input ((input.snoc Atom).snoc Atom) :=
  Fin.cases packedInput (fun i => i.elim0)

private theorem packet_eta {t : Term 1} {A : Types} (d : Derivation Request Γ₀ input t A) :
    Equiv false Γ₀ input t (.let₂ (.bv 0) (t.bsubst splitInput.terms)) A := by
  let intoBinder : Fin 1 → Fin 2 := fun _ => 0
  have kt : HasType Request Γ₀ (input.snoc Packet) (t.rename intoBinder) A :=
    d.toHasType.renameAlong (ρ := intoBinder) (Fin.cases rfl (fun i => i.elim0))
  have packet : HasType Request Γ₀ input (.bv 0) Packet := .bv
  have enter := Equiv.letBeta (pureEff := false) .bv packet kt
  have enter_subst : Tm.instantiate (t.rename intoBinder) (.bv (0 : Fin 1)) = t := by
    rw [Tm.instantiate, Tm.bsubst_rename]
    exact (Tm.bsubst_congr (Fin.cases rfl (fun i => i.elim0)) t).trans (Tm.bsubst_id t)
  rw [enter_subst] at enter
  have destructure := Equiv.let₁ (Equiv.pairEta (pureEff := false) packet).symm (.refl kt)
  have commute := Equiv.bindLetPair (pureEff := false) packet packedInput.derivation.toHasType kt
  have repack := Equiv.letBeta (assembly_pure packedInput) packedInput.derivation.toHasType
    kt.underBinder.underBinder
  have repack_subst : Tm.instantiate (t.rename intoBinder).underBinder.underBinder packedInput.term =
      t.bsubst splitInput.terms := by
    rw [up_reply input, instantiate_renamed, Tm.bsubst_rename]
    exact Tm.bsubst_congr (Fin.cases rfl (fun i => i.elim0)) t
  rw [repack_subst] at repack
  exact enter.symm.trans (destructure.trans (commute.trans (.let₂ (.refl packet) repack)))

/-- Coverage at the same native one-packet boundary as the trace separator. -/
theorem normalize_packet_proof {t : Term 1} {A : Types} (d : Derivation Request Γ₀ input t A) :
    ∃ u : Term 3, ∃ _ : ProductCanonical ((input.snoc Atom).snoc Atom) u A,
      Equiv false Γ₀ input t (.let₂ (.bv 0) u) A := by
  obtain ⟨u, normal, replay⟩ := normalize_exact_proof d splitInput
  exact ⟨u, normal, (packet_eta d).trans (.let₂ (.refl .bv) replay)⟩

theorem packet_program_proof {t : Term 1} {A : Types} (d : Derivation Request Γ₀ input t A) :
    ∃ u : Term 3, ∃ _ : ProductProgram ((input.snoc Atom).snoc Atom) u A,
      Equiv false Γ₀ input t (.let₂ (.bv 0) u) A := by
  obtain ⟨u, p, replay⟩ := normalize_packet_proof d
  exact ⟨u, p.toProgram, replay⟩

theorem packet_run_iff_native_proof {t u : Term 1} {A : Types}
    (d : Derivation Request Γ₀ input t A) (e : Derivation Request Γ₀ input u A) :
    run d (packetEnv (0, 1)) = run e (packetEnv (0, 1)) ↔ Equiv false Γ₀ input t u A := by
  refine ⟨fun equal => ?_, fun h => seq_sound_proof d e h _⟩
  obtain ⟨t', p, hp⟩ := normalize_packet_proof d
  obtain ⟨u', q, hq⟩ := normalize_packet_proof e
  rw [seq_sound_proof d (entry p.derivation) hp _, seq_sound_proof e (entry q.derivation) hq _] at equal
  have normalEq := (entry_product_run_iff_native_proof p.toProgram q.toProgram
    p.derivation q.derivation).mp equal
  exact hp.trans (normalEq.trans hq.symm)

theorem packet_embed_iff_native_proof {t u : Term 1} {A : Types}
    (d : Derivation Request Γ₀ input t A) (e : Derivation Request Γ₀ input u A) :
    LetCase.LocallyNameless.Equiv false Γ₀ input (Morphism.SeqCase.embed t) (Morphism.SeqCase.embed u) A ↔
      Equiv false Γ₀ input t u A := by
  refine ⟨fun h => (packet_run_iff_native_proof d e).mp ?_, Morphism.SeqCase.embed_equiv⟩
  simpa only [run, Morphism.SeqCase.denote_derivation] using
    case_sound_proof (Morphism.SeqCase.derivation d) (Morphism.SeqCase.derivation e) h (packetEnv (0, 1))

end Silmaril.Isotope.LetSeq.StraightLine
