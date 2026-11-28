module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Version.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.RoundTrip.Defs
public import Silmaril.SSA.LambdaRTL.Version.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Version.Flat
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Lexical
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Correctness
import Silmaril.Proofs.SSA.LambdaRTL.Version

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.CyclicVersion

open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG
open Silmaril.SSA.LambdaRTL.CFG.Cyclic Silmaril.SSA.LambdaRTL.CFG.Cyclic.Versioning
open Silmaril.Elgot

universe v w
variable {V K : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}
  [DecidableEq V] [DecidableEq K]

omit [DecidableEq K] in
theorem slots_subset_iff (graph : CFG V K F) (source destination : Block V K F) :
    slots graph destination ⊆ slots graph source ↔
      source.param ∉ registers graph ∨ source.param = destination.param := by
  constructor
  · intro subset
    by_cases supported : source.param ∈ registers graph
    · right
      by_contra different
      have member : source.param ∈ slots graph destination := by simp [slots, supported, different]
      simpa [slots] using subset member
    · exact Or.inl supported
  · intro allowed reg member
    have present : reg ∈ registers graph := (List.mem_filter.mp member).1
    rcases allowed with absent | same
    · have different : reg ≠ source.param := fun eq => absent (eq ▸ present)
      simp [slots, present, different]
    · simpa [slots, same] using member

private theorem versionBody_readback (body : Body V K F) (labels : K → Option (List V))
    (live : List V) (current : V → Nat) (depth : Nat) :
    (versionBody body labels live current depth).toRegion =
      Version.version labels live current depth body.toRegion :=
  FlatVersion.body_readback _ (Option.some_get _).symm

omit [DecidableEq V] [DecidableEq K] in
private theorem unpackBody_readback (regs : List V) (src : V × Nat) (depth : Nat)
    (body : Body (V × Nat) K F) :
    (unpackBody regs src depth body).toRegion = Version.unpack regs src depth body.toRegion :=
  FlatVersion.body_readback _ (Option.some_get _).symm

omit [DecidableEq K] in
private theorem registers_entry (graph : CFG V K F) (reg : V)
    (free : reg ∈ graph.entry.toRegion.fvList) : reg ∈ registers graph := by
  simp [registers, free]

omit [DecidableEq K] in
private theorem registers_block (graph : CFG V K F) (item : K × Block V K F)
    (member : item ∈ graph.blocks) (reg : V) (free : reg ∈ item.2.body.toRegion.fvList) :
    reg ∈ registers graph := by
  simp only [registers, List.mem_dedup, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨item, member, free⟩

private theorem destinations_supported (graph : CFG V K F) (label : K) (regs : List V)
    (layout : destinations graph label = some regs) (reg : V) (member : reg ∈ regs) :
    reg ∈ registers graph := by
  cases found : graph.blocks.lookup label with
  | none => simp [destinations, destinationsWith, found] at layout
  | some block =>
    simp [destinations, destinationsWith, found] at layout
    subst regs
    exact (List.mem_filter.mp member).1

omit [DecidableEq V] in
private theorem lookup_member (table : List (K × Block V K F)) (label : K) (block : Block V K F)
    (found : table.lookup label = some block) : (label, block) ∈ table := by
  induction table with
  | nil => simp at found
  | cons item rest ih =>
    rcases item with ⟨key, body⟩
    cases same : label == key with
    | false =>
      rw [List.lookup_cons, same] at found
      exact List.mem_cons_of_mem _ (ih found)
    | true =>
      have equal : label = key := beq_iff_eq.mp same
      subst key
      simp at found
      subst body
      exact List.mem_cons_self

omit [DecidableEq V] in
private theorem lookup_mapped (build : Block V K F → Block (V × Nat) K F)
    (table : List (K × Block V K F)) (label : K) :
    (table.map (fun item => (item.1, build item.2))).lookup label = (table.lookup label).map build := by
  induction table with
  | nil => rfl
  | cons item rest ih =>
    rcases item with ⟨key, block⟩
    simp only [List.map_cons, List.lookup_cons]
    split <;> simp_all

private theorem lookup_compile (graph : CFG V K F) (label : K) :
    (compile graph).blocks.lookup label = (graph.blocks.lookup label).map (compileBlock graph) :=
  lookup_mapped (compileBlock graph) graph.blocks label

theorem compile_entry_isSSA (graph : CFG V K F) :
    (compile graph).entry.toRegion.IsSSA ((registers graph).map fun reg => (reg, 0)).toFinset := by
  change (versionBody graph.entry _ _ _ _).toRegion.IsSSA _
  rw [versionBody_readback]
  apply Silmaril.SSA.LambdaRTL.Version.version_isSSA _ _ _ _ _ _ (destinations_supported graph)
  · intro name member
    simp only [List.mem_toFinset, List.mem_map] at member
    obtain ⟨_, _, rfl⟩ := member
    exact Nat.le_refl _
  · intro reg member
    have supported := member.elim (registers_entry graph reg) id
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨reg, supported, rfl⟩)

private theorem compileBlock_isSSA (graph : CFG V K F) (item : K × Block V K F)
    (member : item ∈ graph.blocks) :
    (compileBlock graph item.2).body.toRegion.IsSSA {(compileBlock graph item.2).param} := by
  let block := item.2
  let ctx : Finset (V × Nat) := insert (block.param, 2)
    (insert (block.param, 1) {(block.param, 0)})
  have bounded : ∀ p ∈ ctx, p.2 ≤ 2 := by
    intro p hp
    simp only [ctx, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> simp
  simp only [compileBlock, compileBlockWith, Body.toRegion, Region.IsSSA, Op.fv, Val.fv]
  refine ⟨by simp, by simp, by simp, by simp, ?_⟩
  rw [unpackBody_readback, versionBody_readback]
  change (Silmaril.SSA.LambdaRTL.Version.unpack (slots graph block) (block.param, 2) 2 _).IsSSA ctx
  apply Version.unpack_isSSA _ _ _ _ _ (by simp [ctx]) bounded
  apply Silmaril.SSA.LambdaRTL.Version.version_isSSA _ _ _ _ _ _ (destinations_supported graph)
    (Version.unpackCtx_bound _ _ _ bounded)
  intro reg read
  by_cases same : reg = block.param
  · subst reg
    have absent : block.param ∉ slots graph block := by simp [slots]
    rw [Version.unpackCur_of_not_mem _ _ _ _ absent, Version.setv_self]
    exact Version.subset_unpackCtx _ _ ctx (by simp [ctx])
  · have supported : reg ∈ registers graph := read.elim (registers_block graph item member reg) id
    exact Version.unpackCur_mem _ _ _ _ _ (by simp [slots, supported, same])

theorem compile_blocks_areSSA (graph : CFG V K F) (item : K × Block (V × Nat) K F)
    (member : item ∈ (compile graph).blocks) : item.2.body.toRegion.IsSSA {item.2.param} := by
  obtain ⟨source, present, rfl⟩ := List.mem_map.mp member
  exact compileBlock_isSSA graph source present

variable [Monad M] [LawfulMonad M]

theorem entry_commutes (model : Model F M α) (pairs : model.PairLawful) (graph : CFG V K F)
    (input : V × Nat → α) :
    encode model graph <$> enter model graph (fun reg => input (reg, 0)) =
      (compile graph).entry.evalJump model input := by
  rw [body_evalJump]
  change _ = (versionBody graph.entry (destinations graph) (registers graph) _ _).toRegion.evalSSA
    model input
  rw [versionBody_readback, Version.version_evalSSA model pairs _ _ _ _ _ _ _
    (destinations_supported graph) (fun _ _ => rfl)]
  simp [enter, Body.exec_eq]
  rfl

private theorem block_evalJumpWith (model : Model F M α) (pairs : model.PairLawful)
    (labels : K → Option (List V)) (live regs : List V) (block : Block V K F)
    (supported : ∀ k rs, labels k = some rs → ∀ reg ∈ rs, reg ∈ live)
    (separate : block.param ∉ regs)
    (available : ∀ reg, reg ∈ block.body.toRegion.fvList ∨ reg ∈ live →
      reg = block.param ∨ reg ∈ regs)
    (payload : α) (store : V → α) (input : V × Nat → α) :
    (compileBlockWith labels live regs block).body.evalJump model
      (upd input (block.param, 0) (model.pair payload (Version.packVal model store regs))) =
      block.body.exec model (fun k a next => pure (Version.enc model labels (k, a, next)))
        (upd store block.param payload) := by
  rw [body_evalJump, Body.exec_eq]
  simp only [compileBlockWith, Body.toRegion, unpackBody_readback, versionBody_readback,
    Region.evalSSA, Op.eval, Val.eval]
  rw [show upd input (block.param, 0) (model.pair payload (Version.packVal model store regs)) (block.param, 0) =
    model.pair payload (Version.packVal model store regs) from by simp [upd]]
  simp only [pure_bind, pairs.unpair_pair]
  rw [Version.unpack_evalSSA model pairs store _ _ _ _ _ (by simp [upd])]
  apply Version.version_evalSSA model pairs _ _ _ _ _ _ _ supported
  intro reg read
  by_cases same : reg = block.param
  · subst reg
    rw [Version.unpackCur_of_not_mem _ _ _ _ separate,
      Version.unpackEnv_frame model store _ _ _ _ separate]
    simp [Version.setv, upd]
  · have packed := (available reg read).resolve_left same
    rw [Version.unpackEnv_mem model store _ _ _ _ _ packed]
    simp [upd, same]

private theorem block_evalJump (model : Model F M α) (pairs : model.PairLawful)
    (graph : CFG V K F) (label : K) (block : Block V K F) (member : (label, block) ∈ graph.blocks)
    (payload : α) (store : V → α) (input : V × Nat → α) :
    (compileBlock graph block).body.evalJump model
      (upd input (compileBlock graph block).param
        (model.pair payload (Version.packVal model store (slots graph block)))) =
      block.body.exec model (fun k a next => pure (encode model graph (k, a, next)))
        (upd store block.param payload) := by
  apply block_evalJumpWith model pairs _ _ _ block (destinations_supported graph) (by simp [slots])
  intro reg read
  by_cases same : reg = block.param
  · exact Or.inl same
  · have supported : reg ∈ registers graph := read.elim
      (registers_block graph (label, block) member reg) id
    exact Or.inr (by simp [slots, supported, same])

theorem step_commutes (model : Model F M α) (pairs : model.PairLawful) (graph : CFG V K F)
    (input : V × Nat → α) (transfer : Transfer V K α) :
    Sum.map obs (encode model graph) <$> step model graph.blocks transfer =
      Cyclic.stepSSA model (compile graph).blocks input (encode model graph transfer) := by
  rcases transfer with ⟨label, payload, store⟩
  have key : (encode model graph (label, payload, store)).1 = label := Version.enc_fst _ _ _
  cases found : graph.blocks.lookup label with
  | none => simp [step, Cyclic.stepSSA, lookup_compile, found, encode, Version.enc, destinations, destinationsWith, obs]
  | some block =>
    have packet : (encode model graph (label, payload, store)).2 =
        model.pair payload (Version.packVal model store (slots graph block)) := by
      simp [encode, Version.enc, destinations, destinationsWith, found]
    simp only [step, Cyclic.stepSSA, key, lookup_compile, found, Option.map_some]
    rw [packet, block_evalJump model pairs graph label block (lookup_member _ _ _ found)]
    simp only [← Body.exec_map, map_pure, Sum.map_inr]

omit [DecidableEq V] in
private theorem empty_destinations_supported (graph : CFG V K F) (label : K) (regs : List V)
    (layout : destinationsWith graph (fun _ => []) label = some regs) (reg : V) (member : reg ∈ regs) :
    reg ∈ ([] : List V) := by
  cases found : graph.blocks.lookup label <;> simp_all [destinationsWith]

theorem entryPacketLocal_commutes (model : Model F M α) (pairs : model.PairLawful) (graph : CFG V K F)
    (input : V × Nat → α) :
    encodePacketLocal model graph <$> enter model graph (fun reg => input (reg, 0)) =
      (compilePacketLocal graph).entry.evalJump model input := by
  rw [body_evalJump]
  change _ = (versionBody graph.entry (destinationsWith graph (fun _ => [])) [] _ _).toRegion.evalSSA model input
  rw [versionBody_readback, Version.version_evalSSA model pairs _ _ _ _ _ _ _
    (empty_destinations_supported graph) (fun _ _ => rfl)]
  simp [enter, Body.exec_eq]
  rfl

theorem stepPacketLocal_commutes (model : Model F M α) (pairs : model.PairLawful) (graph : CFG V K F)
    (closed : RoundTrip.PacketClosed graph) (input : V × Nat → α) (transfer : Transfer V K α) :
    Sum.map obs (encodePacketLocal model graph) <$> step model graph.blocks transfer =
      Cyclic.stepSSA model (compilePacketLocal graph).blocks input (encodePacketLocal model graph transfer) := by
  rcases transfer with ⟨label, payload, store⟩
  let labels := destinationsWith graph (fun _ => [])
  let build := compileBlockWith (F := F) labels [] []
  have lookup : (compilePacketLocal graph).blocks.lookup label =
      (graph.blocks.lookup label).map build :=
    lookup_mapped build graph.blocks label
  have key : (encodePacketLocal model graph (label, payload, store)).1 = label := Version.enc_fst _ _ _
  cases found : graph.blocks.lookup label with
  | none => simp [step, Cyclic.stepSSA, lookup, found, encodePacketLocal, Version.enc, destinationsWith, obs]
  | some block =>
    have packet : (encodePacketLocal model graph (label, payload, store)).2 = model.pair payload model.unit := by
      simp [encodePacketLocal, Version.enc, destinationsWith, found, Version.packVal]
    have scope (reg : V) (read : reg ∈ block.body.toRegion.fvList ∨ reg ∈ ([] : List V)) :
        reg = block.param ∨ reg ∈ ([] : List V) := by
      rcases read with direct | impossible
      · exact Or.inl (Finset.mem_singleton.mp
          (closed _ (lookup_member _ _ _ found) ((Version.mem_fvList_iff _ _).mp direct)))
      · cases impossible
    have eval := block_evalJumpWith model pairs labels [] [] block (empty_destinations_supported graph)
      (by simp) scope payload store input
    simp only [step, Cyclic.stepSSA, key, lookup, found, Option.map_some]
    rw [packet, show (build block).body.evalJump model
      (upd input (build block).param (model.pair payload model.unit)) = _ from eval]
    simp only [← Body.exec_map, map_pure, Sum.map_inr, encodePacketLocal, labels]

variable [Iterate M] [LawfulElgotMonad M]

private theorem run_commutesFrom (model : Model F M α) (source : CFG V K F)
    (target : CFG (V × Nat) K F) (encoding : Transfer V K α → K × α) (input : V × Nat → α)
    (entry : encoding <$> enter model source (fun reg => input (reg, 0)) = target.entry.evalJump model input)
    (steps : ∀ transfer, Sum.map obs encoding <$> step model source.blocks transfer =
      Cyclic.stepSSA model target.blocks input (encoding transfer)) :
    obs <$> Cyclic.run model source (fun reg => input (reg, 0)) = Cyclic.runSSA model target input := by
  have run_entry : Cyclic.run model source (fun reg => input (reg, 0)) =
      enter model source (fun reg => input (reg, 0)) >>= iter (step model source.blocks) := by
    simp [Cyclic.run, enter, Body.exec_eq]
  rw [run_entry, Cyclic.runSSA, ← entry]
  simp only [map_bind, bind_map_left]
  apply bind_congr
  intro transfer
  exact iter_obs_of_step_encoding model source.blocks encoding _ steps transfer

theorem run_commutes (model : Model F M α) (pairs : model.PairLawful) (graph : CFG V K F)
    (input : V × Nat → α) :
    obs <$> Cyclic.run model graph (fun reg => input (reg, 0)) =
      Cyclic.runSSA model (compile graph) input :=
  run_commutesFrom model graph (compile graph) (encode model graph) input
    (entry_commutes model pairs graph input) (step_commutes model pairs graph input)

theorem runPacketLocal_commutes (model : Model F M α) (pairs : model.PairLawful) (graph : CFG V K F)
    (closed : RoundTrip.PacketClosed graph) (input : V × Nat → α) :
    obs <$> Cyclic.run model graph (fun reg => input (reg, 0)) =
      Cyclic.runSSA model (compilePacketLocal graph) input :=
  run_commutesFrom model graph (compilePacketLocal graph) (encodePacketLocal model graph) input
    (entryPacketLocal_commutes model pairs graph input) (stepPacketLocal_commutes model pairs graph closed input)

end Silmaril.Proofs.SSA.LambdaRTL.CFG.CyclicVersion
