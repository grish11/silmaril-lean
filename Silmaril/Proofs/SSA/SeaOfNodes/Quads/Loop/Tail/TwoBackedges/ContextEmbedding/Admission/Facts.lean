module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms

/-! Fact intersection follows the actual transport, including an empty intersection. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Proofs

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Port)
open Identification (BankMap PortMap merge collectFacts pushFacts)
open Composition (thenMap)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (EntryFacts Admitted)
open Reindex (Registers push)
open Reindex.Guarded.Institution (AdmittedAt)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {old middle new : List (ValueSort Width)} {fresh : ValueSort Width}
variable {S T U : EntrySignature}

private theorem facts_ext {left right : EntryFacts new}
    (reads : ∀ {t} (port : Port (dataPorts new) t), left.get port = right.get port) : left = right :=
  (tabulate_get_eq left).symm.trans
    ((congrArg (tabulate _) (funext fun _ => funext reads)).trans (tabulate_get_eq right))

private theorem push_get (order : Registers middle new) (facts : EntryFacts middle)
    {t : SeaOfNodes.Diamond.Ty Width} (port : Port (dataPorts middle) t) :
    (push order facts).get (order t port) = facts.get port :=
  (get_tabulate _ _).trans (congrArg (fun p => facts.get p) ((order t).symm_apply_apply port))

private theorem push_write (order : Registers middle new) (facts : EntryFacts middle)
    {t : SeaOfNodes.Diamond.Ty Width} (dest : Port (dataPorts middle) t) (fact : Fact Word t) :
    push order (write dest fact facts) = write (order t dest) fact (push order facts) := by
  apply facts_ext
  intro sort target
  obtain ⟨port, rfl⟩ := (order sort).surjective target
  rw [push_get]
  by_cases same : slot port = slot dest
  · obtain ⟨rfl, atDest⟩ := Sigma.mk.inj_iff.mp (Reindex.slot_eq _ _ same)
    obtain rfl := eq_of_heq atDest
    rw [get_write_same, get_write_same]
  · have distinct : slot (order sort port) ≠ slot (order t dest) := by
      intro shared
      obtain ⟨rfl, image⟩ := Sigma.mk.inj_iff.mp (Reindex.slot_eq _ _ shared)
      exact same (congrArg slot ((order _).injective (eq_of_heq image)))
    rw [get_write_other _ _ _ _ same, get_write_other _ _ _ _ distinct, push_get]

private theorem push_overdefined (order : Registers middle new) :
    push order (tabulate (F := Fact Word) _ fun _ => .overdefined) =
      tabulate (F := Fact Word) _ fun _ => .overdefined := by
  apply facts_ext
  intro sort port
  obtain ⟨old, rfl⟩ := (order sort).surjective port
  rw [push_get, get_tabulate, get_tabulate]

private theorem collect_permute (order : Registers middle new) (map : BankMap old middle)
    (facts : EntryFacts old) (acc : EntryFacts middle) :
    collectFacts facts (thenMap map (fun t => order t)) (push order acc) =
      (collectFacts facts map acc).map (push order) := by
  induction old generalizing acc with
  | nil => cases facts; rfl
  | cons sort rest ih =>
    cases facts with
    | cons head tail =>
      simp only [collectFacts, thenMap, push_get]
      cases merged : merge sort head (acc.get (map _ .head)) with
      | none => rfl
      | some next =>
        change collectFacts tail _ (write (order _ (map _ .head)) next (push order acc)) =
          (collectFacts tail _ (write (map _ .head) next acc)).map (push order)
        rw [← push_write order acc (map _ .head) next]
        exact ih (fun t p => map t (.tail p)) tail (write (map _ .head) next acc)

private theorem collect_weaken (map : BankMap old middle) (facts : EntryFacts old)
    (acc : EntryFacts middle) (headFact : Fact Word (.value fresh)) :
    collectFacts (new := fresh :: middle) facts (thenMap map (fun _ p => .tail p)) (.cons headFact acc) =
      (collectFacts facts map acc).map (fun compressed => .cons headFact compressed) := by
  induction old generalizing acc with
  | nil => cases facts; rfl
  | cons sort rest ih =>
    cases facts with
    | cons head tail =>
      simp only [collectFacts, thenMap, RVSDG.Tuple.get]
      cases merged : merge sort head (acc.get (map _ .head)) with
      | none => rfl
      | some next => exact ih (fun t p => map t (.tail p)) tail (write (map _ .head) next acc)

private theorem push_permute (order : Registers middle new) (map : BankMap old middle)
    (facts : EntryFacts old) :
    pushFacts (thenMap map (fun t => order t)) facts = (pushFacts map facts).map (push order) := by
  unfold pushFacts
  rw [← push_overdefined order, collect_permute]

private theorem push_weaken (map : BankMap old middle) (facts : EntryFacts old) :
    pushFacts (new := fresh :: middle) (thenMap map (fun _ p => .tail p)) facts =
      (pushFacts map facts).map (Weakening.facts fresh) :=
  collect_weaken map facts _ _

set_option backward.isDefEq.respectTransparency false in
theorem pushFacts_embedding (first : PortMap S T) (path : Embedding T U) (facts : EntryFacts S.regs) :
    pushFacts (thenMap first path.portMap) facts = (pushFacts first facts).map (embedFacts path) := by
  induction path with
  | id =>
    change pushFacts first facts = (pushFacts first facts).map id
    exact Option.map_id_apply.symm
  | permute order rest ih =>
    rw [show thenMap first (Embedding.permute order rest).portMap =
      thenMap (thenMap first (fun t => order t)) rest.portMap from rfl, ih, push_permute]
    exact Option.map_map _ _ _
  | weaken fresh rest ih =>
    rw [show thenMap first (Embedding.weaken fresh rest).portMap =
      thenMap (thenMap (new := (Weakening.Guarded.extend _ fresh).regs) first (fun _ p => .tail p))
        rest.portMap from rfl, ih, push_weaken]
    exact Option.map_map _ _ _

private theorem push_id (facts : EntryFacts old)
    (nonbottom : ∀ t (port : Port (dataPorts old) t), facts.get port ≠ .bottom) :
    pushFacts (fun _ port => port) facts = some facts := by
  induction old with
  | nil => cases facts; rfl
  | cons sort rest ih =>
    cases facts with
    | cons head tail =>
      have headNonbottom : head ≠ .bottom := nonbottom (.value sort) .head
      have mergeHead : merge sort head .overdefined = some head := by
        cases head <;> simp_all [merge]
      change ((merge sort head .overdefined).bind fun fact =>
        collectFacts tail (thenMap (new := sort :: rest) (fun _ p => p) (fun _ p => .tail p))
          (.cons fact (tabulate (dataPorts rest) fun _ => .overdefined))) = some (.cons head tail)
      rw [mergeHead]
      change collectFacts (new := sort :: rest) tail _ (.cons head _) = _
      rw [collect_weaken]
      exact congrArg (Option.map (fun bank : EntryFacts rest => RVSDG.Tuple.cons head bank)) (ih tail (fun t p => nonbottom t (.tail p)))

theorem push_id_of_push (map : BankMap old new) (facts : EntryFacts old) (output : EntryFacts new)
    (pushed : pushFacts map facts = some output) :
    pushFacts (fun _ port => port) output = some output :=
  push_id output fun _ port => Identification.pushFacts_nonbottom map facts output pushed port

theorem mapped_facts (path : Embedding T U) {result : Width} (p : AdmittedAt T result) :
    @Admitted.facts _ _ U.bankEq (path.mapAdmitted p) = embedFacts path (@Admitted.facts _ _ T.bankEq p) := by
  induction path with
  | id => rfl
  | permute _ _ ih => exact ih _
  | weaken _ _ ih => exact ih _

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Proofs
