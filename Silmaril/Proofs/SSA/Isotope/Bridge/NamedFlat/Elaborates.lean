module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Elaborates.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Version.Flat.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Version.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Forward.Closure.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Thms

public section

namespace Silmaril.Isotope.Bridge.NamedFlat

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG (Body Term)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic (Versioning.compile)

universe v w

/-! ## Elaboration of a body

A body elaborates when its operands are in the fragment, the names in
scope have every register it reads freely, and its labels are indexed. -/

section Body

variable {V K : Type w} {F : Type v} {labels : Nat}

/-- A value elaborates when the names have its registers. -/
theorem value_isSome_proof {n : Nat} (names : Names V n) : (v : Val V) →
    (∀ z ∈ v.fvList, (names z).isSome = true) → (value (F := F) names v).isSome = true
  | .var reg, named => by
    have here := named reg (by simp [Val.fvList])
    simp only [value, Option.isSome_map, here]
  | .unit, _ => rfl
  | .pair a b, named => by
    have first : (value (F := F) names a).isSome = true :=
      value_isSome_proof names a fun z member => named z (by simp [Val.fvList, member])
    have second : (value (F := F) names b).isSome = true :=
      value_isSome_proof names b fun z member => named z (by simp [Val.fvList, member])
    obtain ⟨left, hl⟩ := Option.isSome_iff_exists.mp first
    obtain ⟨right, hr⟩ := Option.isSome_iff_exists.mp second
    simp [value, hl, hr]

/-- An operand of the fragment elaborates when the names have its
registers. -/
theorem operand_isSome_proof {n : Nat} (names : Names V n) (op : Op V F)
    (fragment : plainOp op = true) (named : ∀ z ∈ op.fvList, (names z).isSome = true) :
    (operand names op).isSome = true := by
  cases op with
  | val a => exact value_isSome_proof names a named
  | app f a =>
    obtain ⟨arg, ha⟩ := Option.isSome_iff_exists.mp (value_isSome_proof (F := F) names a named)
    simp [operand, ha]
  | inl a => simp [plainOp] at fragment
  | inr a => simp [plainOp] at fragment
  | abort a => simp [plainOp] at fragment

variable [DecidableEq V]

omit [DecidableEq V] in
/-- The names after a binder have the binder and the earlier names. -/
theorem bindName_isSome_proof [DecidableEq V] {n : Nat} (names : Names V n) (x z : V)
    (known : z = x ∨ (names z).isSome = true) : (bindName names x z).isSome = true := by
  simp only [bindName]
  split
  · rfl
  · rename_i other
    simpa using known.resolve_left other

/-- A terminator elaborates. -/
theorem term_isSome_proof (index : K → Option (Fin labels)) :
    {n : Nat} → (names : Names V n) → (tail : Term V K F) →
    plainRegion tail.toRegion = true → (∀ z ∈ tail.toRegion.fvList, (names z).isSome = true) →
    (∀ label ∈ tail.targets, (index label).isSome = true) →
    (term index names tail).isSome = true
  | _, names, .br label arg, _, named, indexed => by
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (indexed label (by simp [Term.targets]))
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (value_isSome_proof (F := F) names arg named)
    simp [term, hi, ha]
  | _, names, .case op x left y right, fragment, named, indexed => by
    simp only [Term.toRegion, plainRegion, Bool.and_eq_true] at fragment
    simp only [Term.toRegion, Region.fvList, List.mem_append, List.mem_filter,
      decide_eq_true_eq] at named
    obtain ⟨discr, hd⟩ := Option.isSome_iff_exists.mp (operand_isSome_proof names op fragment.1.1
      fun z member => named z (.inl (.inl member)))
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp (term_isSome_proof index (bindName names x) left
      fragment.1.2 (fun z member => bindName_isSome_proof names x z (by
        by_cases same : z = x
        · exact .inl same
        · exact .inr (named z (.inl (.inr ⟨member, same⟩)))))
      fun label member => indexed label (by simp [Term.targets, member]))
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (term_isSome_proof index (bindName names y) right
      fragment.2 (fun z member => bindName_isSome_proof names y z (by
        by_cases same : z = y
        · exact .inl same
        · exact .inr (named z (.inr ⟨member, same⟩))))
      fun label member => indexed label (by simp [Term.targets, member]))
    simp [term, hd, hl, hr]

/-- A body elaborates when its operands are in the fragment, the names
have every register it reads freely, and its labels are indexed. -/
theorem body_isSome_proof (index : K → Option (Fin labels)) :
    {n : Nat} → (names : Names V n) → (source : Body V K F) →
    plainRegion source.toRegion = true →
    (∀ z ∈ source.toRegion.fvList, (names z).isSome = true) →
    (∀ label ∈ source.targets, (index label).isSome = true) →
    (body index names source).isSome = true
  | _, names, .term tail, fragment, named, indexed =>
    term_isSome_proof index names tail fragment named indexed
  | _, names, .let1 x op rest, fragment, named, indexed => by
    simp only [Body.toRegion, plainRegion, Bool.and_eq_true] at fragment
    simp only [Body.toRegion, Region.fvList, List.mem_append, List.mem_filter,
      decide_eq_true_eq] at named
    obtain ⟨arg, ha⟩ := Option.isSome_iff_exists.mp (operand_isSome_proof names op fragment.1
      fun z member => named z (.inl member))
    obtain ⟨tail, ht⟩ := Option.isSome_iff_exists.mp (body_isSome_proof index (bindName names x)
      rest fragment.2 (fun z member => bindName_isSome_proof names x z (by
        by_cases same : z = x
        · exact .inl same
        · exact .inr (named z (.inr ⟨member, same⟩)))) indexed)
    simp [body, ha, ht]
  | _, names, .let2 x y op rest, fragment, named, indexed => by
    simp only [Body.toRegion, plainRegion, Bool.and_eq_true] at fragment
    simp only [Body.toRegion, Region.fvList, List.mem_append, List.mem_filter,
      decide_eq_true_eq] at named
    obtain ⟨arg, ha⟩ := Option.isSome_iff_exists.mp (operand_isSome_proof names op fragment.1
      fun z member => named z (.inl member))
    obtain ⟨tail, ht⟩ := Option.isSome_iff_exists.mp (body_isSome_proof index
      (bindName (bindName names x) y) rest fragment.2
      (fun z member => bindName_isSome_proof _ y z (by
        by_cases sameY : z = y
        · exact .inl sameY
        · refine .inr (bindName_isSome_proof names x z ?_)
          by_cases sameX : z = x
          · exact .inl sameX
          · exact .inr (named z (.inr ⟨member, sameX, sameY⟩)))) indexed)
    simp [body, ha, ht]

end Body

/-! ## The versioned bodies

Versioning keeps the fragment and the labels of a body. A register that a
versioned body reads freely is a register that the body reads freely, or
one in the record of a label it jumps to, at its current version. -/

section Versioned

variable {V L : Type w} {F : Type v}

/-- The labels that a region jumps to. -/
def regionJumps : Region V L F → List L
  | .br label _ => [label]
  | .let1 _ _ rest => regionJumps rest
  | .let2 _ _ _ rest => regionJumps rest
  | .case _ _ left _ right => regionJumps left ++ regionJumps right
  | .join body _ _ handler => regionJumps body ++ regionJumps handler

theorem term_jumps_proof : (tail : Term V L F) → regionJumps tail.toRegion = tail.targets
  | .br _ _ => rfl
  | .case _ _ left _ right => by
    simp only [Term.toRegion, regionJumps, Term.targets, term_jumps_proof left,
      term_jumps_proof right]

theorem body_jumps_proof : (source : Body V L F) → regionJumps source.toRegion = source.targets
  | .term tail => term_jumps_proof tail
  | .let1 _ _ rest => body_jumps_proof rest
  | .let2 _ _ _ rest => body_jumps_proof rest

/-- A body that is recognized in a region reads back to the region. -/
theorem region_of_body_proof (region : Region V L F) (source : Body V L F)
    (found : Body.ofRegion? region = some source) : source.toRegion = region := by
  have whole : CFG.ofRegion? region = some ⟨source, []⟩ := by
    cases region with
    | join => simp [Body.ofRegion?, Term.ofRegion?] at found
    | br => simp [CFG.ofRegion?, CFG.ofRegion?.collect, found]
    | let1 => simp [CFG.ofRegion?, CFG.ofRegion?.collect, found]
    | let2 => simp [CFG.ofRegion?, CFG.ofRegion?.collect, found]
    | case => simp [CFG.ofRegion?, CFG.ofRegion?.collect, found]
  exact (CFG.ofRegion?_eq_some_iff region ⟨source, []⟩).1 whole

theorem rn_fv_proof (cur : V → Nat) : (v : Val V) →
    (Version.rn cur v).fvList = v.fvList.map fun z => (z, cur z)
  | .var _ => rfl
  | .unit => rfl
  | .pair a b => by
    simp only [Version.rn, Val.fvList, List.map_append, rn_fv_proof cur a, rn_fv_proof cur b]

theorem rnOp_fv_proof (cur : V → Nat) (op : Op V F) :
    (Version.rnOp cur op).fvList = op.fvList.map fun z => (z, cur z) := by
  cases op <;> simp only [Version.rnOp, Op.fvList, rn_fv_proof]

theorem pack_fv_proof (cur : V → Nat) : (registers : List V) →
    (Version.pack cur registers).fvList = registers.map fun z => (z, cur z)
  | [] => rfl
  | y :: rest => by
    simp only [Version.pack, Val.fvList, List.map_cons, pack_fv_proof cur rest]
    rfl

theorem rnOp_plain_proof (cur : V → Nat) (op : Op V F) :
    plainOp (Version.rnOp cur op) = plainOp op := by
  cases op <;> rfl

variable [DecidableEq V]

/-- A register outside an unpacked record keeps its version. -/
theorem unpackCur_absent_proof (z : V) : (regs : List V) → (cur : V → Nat) → (d : Nat) →
    z ∉ regs → Version.unpackCur regs cur d z = cur z
  | [], _, _, _ => rfl
  | y :: ys, cur, d, absent => by
    simp only [List.mem_cons, not_or] at absent
    rw [Version.unpackCur, unpackCur_absent_proof z ys _ _ absent.2]
    simp [Version.setv, absent.1]

omit [DecidableEq V] in
/-- Unpacking a record keeps the fragment and the labels. -/
theorem unpack_shape_proof : (regs : List V) → (src : V × Nat) → (d : Nat) →
    (inner : Region (V × Nat) L F) →
    plainRegion (Version.unpack regs src d inner) = plainRegion inner ∧
      regionJumps (Version.unpack regs src d inner) = regionJumps inner
  | [], _, _, _ => ⟨rfl, rfl⟩
  | y :: ys, src, d, inner => by
    have rest := unpack_shape_proof ys (y, d + 2) (d + 2) inner
    exact ⟨by simp only [Version.unpack, plainRegion, plainOp, Bool.true_and, rest.1],
      by simp only [Version.unpack, regionJumps, rest.2]⟩

/-- A free read of an unpacked body is the record, or a free read of the
body that is not the current version of a register of the record. -/
theorem unpack_names_proof : (regs : List V) → (src : V × Nat) → (d : Nat) → (cur : V → Nat) →
    (inner : Region (V × Nat) L F) → ∀ name ∈ (Version.unpack regs src d inner).fvList,
    name = src ∨ (name ∈ inner.fvList ∧
      ∀ z, name = (z, Version.unpackCur regs cur d z) → z ∉ regs)
  | [], _, _, _, _, name, member => .inr ⟨member, fun _ _ => by simp⟩
  | y :: ys, src, d, cur, inner, name, member => by
    simp only [Version.unpack, Region.fvList, Op.fvList, Val.fvList, List.mem_append,
      List.mem_singleton, List.mem_filter, decide_eq_true_eq] at member
    rcases member with here | ⟨free, other⟩
    · exact .inl here
    · rcases unpack_names_proof ys (y, d + 2) (d + 2) (Version.setv cur y (d + 1)) inner name
        free with same | ⟨read, fresh⟩
      · exact absurd same other.2
      · refine .inr ⟨read, fun z eq listed => ?_⟩
        have absent := fresh z eq
        rcases List.mem_cons.mp listed with isHead | inTail
        · subst isHead
          have value : Version.unpackCur ys (Version.setv cur z (d + 1)) (d + 2) z = d + 1 := by
            rw [unpackCur_absent_proof z ys _ _ absent]
            simp [Version.setv]
          exact other.1 (eq.trans (by simp only [Version.unpackCur, value]))
        · exact absent inTail

variable [DecidableEq L]

/-- Versioning keeps the fragment and the labels of a terminator. -/
theorem version_term_shape_proof (lenv : L → Option (List V)) (live : List V) :
    (tail : Term V L F) → (cur : V → Nat) → (d : Nat) →
    plainRegion (Version.version lenv live cur d tail.toRegion) = plainRegion tail.toRegion ∧
      regionJumps (Version.version lenv live cur d tail.toRegion) = regionJumps tail.toRegion
  | .br label _, _, _ => by
    simp only [Term.toRegion, Version.version]
    cases lenv label <;> exact ⟨rfl, rfl⟩
  | .case op x left y right, cur, d => by
    have inLeft := version_term_shape_proof lenv live left (Version.setv cur x (d + 1)) (d + 1)
    have inRight := version_term_shape_proof lenv live right (Version.setv cur y (d + 1)) (d + 1)
    exact ⟨by simp only [Term.toRegion, Version.version, plainRegion, rnOp_plain_proof, inLeft.1,
        inRight.1],
      by simp only [Term.toRegion, Version.version, regionJumps, inLeft.2, inRight.2]⟩

/-- Versioning keeps the fragment and the labels of a body. -/
theorem version_body_shape_proof (lenv : L → Option (List V)) (live : List V) :
    (source : Body V L F) → (cur : V → Nat) → (d : Nat) →
    plainRegion (Version.version lenv live cur d source.toRegion) = plainRegion source.toRegion ∧
      regionJumps (Version.version lenv live cur d source.toRegion) =
        regionJumps source.toRegion
  | .term tail, cur, d => version_term_shape_proof lenv live tail cur d
  | .let1 x op rest, cur, d => by
    have inRest := version_body_shape_proof lenv live rest (Version.setv cur x (d + 1)) (d + 1)
    exact ⟨by simp only [Body.toRegion, Version.version, plainRegion, rnOp_plain_proof, inRest.1],
      by simp only [Body.toRegion, Version.version, regionJumps, inRest.2]⟩
  | .let2 x y op rest, cur, d => by
    have inRest := version_body_shape_proof lenv live rest
      (Version.setv (Version.setv cur x (d + 1)) y (d + 2)) (d + 2)
    exact ⟨by simp only [Body.toRegion, Version.version, plainRegion, rnOp_plain_proof, inRest.1],
      by simp only [Body.toRegion, Version.version, regionJumps, inRest.2]⟩

/-- A free read of a versioned terminator. -/
theorem version_term_names_proof (lenv : L → Option (List V)) (live : List V) :
    (tail : Term V L F) → (cur : V → Nat) → (d : Nat) →
    ∀ name ∈ (Version.version lenv live cur d tail.toRegion).fvList,
      ∃ z, name = (z, cur z) ∧ (z ∈ tail.toRegion.fvList ∨
        ∃ label ys, label ∈ tail.targets ∧ lenv label = some ys ∧ z ∈ ys)
  | .br label value, cur, d => by
    intro name member
    simp only [Term.toRegion, Version.version] at member
    cases found : lenv label with
    | none =>
      rw [found] at member
      simp only [Region.fvList, rn_fv_proof, List.mem_map] at member
      obtain ⟨z, read, rfl⟩ := member
      exact ⟨z, rfl, .inl read⟩
    | some ys =>
      rw [found] at member
      simp only [Region.fvList, Val.fvList, rn_fv_proof, pack_fv_proof, List.mem_append,
        List.mem_map] at member
      rcases member with ⟨z, read, rfl⟩ | ⟨z, carried, rfl⟩
      · exact ⟨z, rfl, .inl read⟩
      · exact ⟨z, rfl, .inr ⟨label, ys, by simp [Term.targets], found, carried⟩⟩
  | .case op x left y right, cur, d => by
    intro name member
    simp only [Term.toRegion, Version.version, Region.fvList, rnOp_fv_proof, List.mem_append,
      List.mem_map, List.mem_filter, decide_eq_true_eq] at member
    rcases member with (⟨z, read, rfl⟩ | ⟨free, other⟩) | ⟨free, other⟩
    · exact ⟨z, rfl, .inl (by simp [Term.toRegion, Region.fvList, read])⟩
    · obtain ⟨z, rfl, source⟩ := version_term_names_proof lenv live left _ _ name free
      have differs : z ≠ x := fun same => other (by simp [Version.setv, same])
      refine ⟨z, by simp [Version.setv, differs], ?_⟩
      rcases source with read | ⟨label, ys, target, found, carried⟩
      · exact .inl (by simp [Term.toRegion, Region.fvList, read, differs])
      · exact .inr ⟨label, ys, by simp [Term.targets, target], found, carried⟩
    · obtain ⟨z, rfl, source⟩ := version_term_names_proof lenv live right _ _ name free
      have differs : z ≠ y := fun same => other (by simp [Version.setv, same])
      refine ⟨z, by simp [Version.setv, differs], ?_⟩
      rcases source with read | ⟨label, ys, target, found, carried⟩
      · exact .inl (by simp [Term.toRegion, Region.fvList, read, differs])
      · exact .inr ⟨label, ys, by simp [Term.targets, target], found, carried⟩

/-- A free read of a versioned body is a free read of the body, or a
register in the record of a label it jumps to, at its current version. -/
theorem version_body_names_proof (lenv : L → Option (List V)) (live : List V) :
    (source : Body V L F) → (cur : V → Nat) → (d : Nat) →
    ∀ name ∈ (Version.version lenv live cur d source.toRegion).fvList,
      ∃ z, name = (z, cur z) ∧ (z ∈ source.toRegion.fvList ∨
        ∃ label ys, label ∈ source.targets ∧ lenv label = some ys ∧ z ∈ ys)
  | .term tail, cur, d => version_term_names_proof lenv live tail cur d
  | .let1 x op rest, cur, d => by
    intro name member
    simp only [Body.toRegion, Version.version, Region.fvList, rnOp_fv_proof, List.mem_append,
      List.mem_map, List.mem_filter, decide_eq_true_eq] at member
    rcases member with ⟨z, read, rfl⟩ | ⟨free, other⟩
    · exact ⟨z, rfl, .inl (by simp [Body.toRegion, Region.fvList, read])⟩
    · obtain ⟨z, rfl, source⟩ := version_body_names_proof lenv live rest _ _ name free
      have differs : z ≠ x := fun same => other (by simp [Version.setv, same])
      refine ⟨z, by simp [Version.setv, differs], ?_⟩
      rcases source with read | ⟨label, ys, target, found, carried⟩
      · exact .inl (by simp [Body.toRegion, Region.fvList, read, differs])
      · exact .inr ⟨label, ys, target, found, carried⟩
  | .let2 x y op rest, cur, d => by
    intro name member
    simp only [Body.toRegion, Version.version, Region.fvList, rnOp_fv_proof, List.mem_append,
      List.mem_map, List.mem_filter, decide_eq_true_eq] at member
    rcases member with ⟨z, read, rfl⟩ | ⟨free, other⟩
    · exact ⟨z, rfl, .inl (by simp [Body.toRegion, Region.fvList, read])⟩
    · obtain ⟨z, rfl, source⟩ := version_body_names_proof lenv live rest _ _ name free
      have differsY : z ≠ y := fun same => other.2 (by simp [Version.setv, same])
      have differsX : z ≠ x := fun same => other.1 (by
        subst same
        simp [Version.setv, differsY])
      refine ⟨z, by simp [Version.setv, differsX, differsY], ?_⟩
      rcases source with read | ⟨label, ys, target, found, carried⟩
      · exact .inl (by simp [Body.toRegion, Region.fvList, read, differsX, differsY])
      · exact .inr ⟨label, ys, target, found, carried⟩

end Versioned

/-! ## The versioned graph -/

section Compiled

open Silmaril.SSA.LambdaRTL.CFG.Cyclic

variable {V K : Type w} {F : Type v} [DecidableEq V] [DecidableEq K]

/-- The versioned body reads back to the versioned region of the body. -/
theorem versionBody_region_proof (source : Body V K F) (labels : K → Option (List V))
    (live : List V) (current : V → Nat) (depth : Nat) :
    (Versioning.versionBody source labels live current depth).toRegion =
      Version.version labels live current depth source.toRegion :=
  region_of_body_proof _ _ (Option.some_get _).symm

omit [DecidableEq V] [DecidableEq K] in
/-- The unpacked body reads back to the unpacked region of the body. -/
theorem unpackBody_region_proof (regs : List V) (src : V × Nat) (depth : Nat)
    (source : Body (V × Nat) K F) :
    (Versioning.unpackBody regs src depth source).toRegion =
      Version.unpack regs src depth source.toRegion :=
  region_of_body_proof _ _ (Option.some_get _).symm

/-- The region of a versioned block: it takes its packet apart, unpacks
its record, and runs the versioned body. -/
theorem compileBlock_region_proof (graph : CFG V K F) (block : CFG.Block V K F) :
    (Versioning.compileBlock graph block).body.toRegion =
      .let2 (block.param, 1) (block.param, 2) (.val (.var (block.param, 0)))
        (Version.unpack (Versioning.slots graph block) (block.param, 2) 2
          (Version.version (Versioning.destinations graph) (Versioning.registers graph)
            (Version.unpackCur (Versioning.slots graph block)
              (Version.setv (fun _ => 0) block.param 1) 2)
            (2 + 2 * (Versioning.slots graph block).length) block.body.toRegion)) := by
  show Body.toRegion (.let2 _ _ _ (Versioning.unpackBody _ _ _ (Versioning.versionBody _ _ _ _ _))) =
    _
  rw [Body.toRegion, unpackBody_region_proof, versionBody_region_proof]

/-- A versioned block reads only its parameter freely. Its record holds
every register that some body reads, without its parameter, and the
block unpacks all of it. -/
theorem compileBlock_names_proof (graph : CFG V K F) (item : K × CFG.Block V K F)
    (member : item ∈ graph.blocks) :
    ∀ name ∈ (Versioning.compileBlock graph item.2).body.toRegion.fvList,
      name = (item.2.param, 0) := by
  intro name listed
  rw [compileBlock_region_proof] at listed
  simp only [Region.fvList, Op.fvList, Val.fvList, List.mem_append, List.mem_singleton,
    List.mem_filter, decide_eq_true_eq] at listed
  rcases listed with here | ⟨free, other⟩
  · exact here
  · rcases unpack_names_proof (Versioning.slots graph item.2) (item.2.param, 2) 2
      (Version.setv (fun _ => 0) item.2.param 1) _ name free with same | ⟨read, fresh⟩
    · exact absurd same other.2
    · obtain ⟨z, rfl, source⟩ := version_body_names_proof _ _ item.2.body _ _ name read
      have absent := fresh z rfl
      have registered : z ∈ Versioning.registers graph := by
        rcases source with inBody | ⟨label, ys, _, found, carried⟩
        · simp only [Versioning.registers, List.mem_dedup, List.mem_append, List.mem_flatMap]
          exact .inr ⟨item, member, inBody⟩
        · simp only [Versioning.destinations, Versioning.destinationsWith,
            Option.map_eq_some_iff] at found
          obtain ⟨target, _, rfl⟩ := found
          exact (List.mem_filter.mp carried).1
      have isParam : z = item.2.param := by
        by_contra different
        exact absent (by simp [Versioning.slots, registered, different])
      subst isParam
      have value : Version.unpackCur (Versioning.slots graph item.2)
          (Version.setv (fun _ => 0) item.2.param 1) 2 item.2.param = 1 := by
        rw [unpackCur_absent_proof _ _ _ _ absent]
        simp [Version.setv]
      exact absurd (by rw [value]) other.1

/-- A versioned block keeps the fragment and the labels of the block. -/
theorem compileBlock_shape_proof (graph : CFG V K F) (block : CFG.Block V K F) :
    plainRegion (Versioning.compileBlock graph block).body.toRegion =
        plainRegion block.body.toRegion ∧
      (Versioning.compileBlock graph block).body.targets = block.body.targets := by
  have unpacked := unpack_shape_proof (L := K) (F := F) (Versioning.slots graph block)
    (block.param, 2) 2
    (Version.version (Versioning.destinations graph) (Versioning.registers graph)
      (Version.unpackCur (Versioning.slots graph block)
        (Version.setv (fun _ => 0) block.param 1) 2)
      (2 + 2 * (Versioning.slots graph block).length) block.body.toRegion)
  have versioned := version_body_shape_proof (Versioning.destinations graph)
    (Versioning.registers graph) block.body
    (Version.unpackCur (Versioning.slots graph block) (Version.setv (fun _ => 0) block.param 1) 2)
    (2 + 2 * (Versioning.slots graph block).length)
  refine ⟨?_, ?_⟩
  · rw [compileBlock_region_proof]
    simp only [plainRegion, plainOp, Bool.true_and, unpacked.1, versioned.1]
  · rw [← body_jumps_proof, compileBlock_region_proof, ← body_jumps_proof]
    simp only [regionJumps, unpacked.2, versioned.2]

/-- The versioned entry keeps the fragment and the labels of the entry. -/
theorem compile_entry_shape_proof (graph : CFG V K F) :
    plainRegion (Versioning.compile graph).entry.toRegion = plainRegion graph.entry.toRegion ∧
      (Versioning.compile graph).entry.targets = graph.entry.targets := by
  have versioned := version_body_shape_proof (Versioning.destinations graph)
    (Versioning.registers graph) graph.entry (fun _ => 0) 0
  have region : (Versioning.compile graph).entry.toRegion =
      Version.version (Versioning.destinations graph) (Versioning.registers graph) (fun _ => 0) 0
        graph.entry.toRegion := versionBody_region_proof _ _ _ _ _
  refine ⟨by rw [region, versioned.1], ?_⟩
  rw [← body_jumps_proof, region, versioned.2, body_jumps_proof]

end Compiled

/-! ## Elaboration of a graph -/

section Graph

open Silmaril.SSA.LambdaRTL.CFG.Cyclic

variable {V K : Type w} {F : Type v} [DecidableEq V] [DecidableEq K] {n : Nat}

omit [DecidableEq V] [DecidableEq K] in
/-- A table has every row when every row is defined. -/
theorem tabulate_isSome_proof {A : Type v} : (count : Nat) → (f : Fin count → Option A) →
    (∀ i, (f i).isSome = true) → (tabulate count f).isSome = true
  | 0, _, _ => rfl
  | count + 1, f, defined => by
    obtain ⟨head, hh⟩ := Option.isSome_iff_exists.mp (defined 0)
    obtain ⟨rest, hr⟩ := Option.isSome_iff_exists.mp
      (tabulate_isSome_proof count (fun i => f i.succ) fun i => defined i.succ)
    simp [tabulate, hh, hr]

omit [DecidableEq K] in
/-- The first occurrence of a key that occurs. -/
theorem first_isSome_proof (keys : Fin n → V) (key : V) (occurs : ∃ i, keys i = key) :
    (first keys key).isSome = true := by
  obtain ⟨i, here⟩ := occurs
  simp only [first, List.find?_isSome]
  exact ⟨i, List.mem_finRange i, by simpa using here⟩

omit [DecidableEq V] in
/-- A label that is a block or a declared exit has an index. -/
theorem labelIndex_isSome_proof (blocks : List (K × CFG.Block V K F)) (exits : List K) (label : K)
    (known : (blocks.any (fun item => label == item.1) || exits.contains label) = true) :
    (labelIndex blocks exits label).isSome = true := by
  simp only [labelIndex]
  cases found : blocks.findFinIdx? (fun item => label == item.1) with
  | some i => rfl
  | none =>
    have absent : blocks.any (fun item => label == item.1) = false := by
      rw [← List.isSome_findFinIdx?, found]
      rfl
    rw [absent, Bool.false_or] at known
    simp only [Option.isSome_map, List.isSome_findFinIdx?]
    simpa [List.any_eq_true, List.contains_iff_mem] using known

/-- A graph elaborates when its entry and each of its blocks elaborate. -/
theorem elaborate_isSome_proof (graph : CFG V K F) (exits : List K) (captures : Fin n → V)
    (entryOk : (body (labelIndex graph.blocks exits) (first captures) graph.entry).isSome = true)
    (blocksOk : ∀ i : Fin graph.blocks.length,
      (body (labelIndex graph.blocks exits) (blockNames (n := n) graph.blocks[i].2.param)
        graph.blocks[i].2.body).isSome = true) :
    (elaborate graph exits captures).isSome = true := by
  obtain ⟨entry, he⟩ := Option.isSome_iff_exists.mp entryOk
  simp only [elaborate, he, Option.bind_some, Option.isSome_map]
  exact tabulate_isSome_proof _ _ blocksOk

/-- The versioning and the elaboration of a named graph succeed at the
given captures, when its operands are in the fragment, its jumps go to
blocks or declared exits, and the versioned entry reads only captures at
their initial version. -/
theorem compile_isSome_proof (source : CFG V K F) (exits : List K) (captures : Fin n → V)
    (fragment : plain source = true) (known : resolves source exits = true)
    (named : entryNamed source captures = true) :
    (compile source exits captures).isSome = true := by
  simp only [plain, plainBody, Bool.and_eq_true, List.all_eq_true] at fragment
  simp only [resolves, List.all_eq_true, List.mem_append, List.mem_flatMap] at known
  simp only [entryNamed, List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at named
  have labels : ∀ label, (source.blocks.any (fun item => label == item.1) ||
      exits.contains label) = true →
      (labelIndex (Versioning.compile source).blocks exits label).isSome = true := by
    intro label resolved
    apply labelIndex_isSome_proof
    rw [show (Versioning.compile source).blocks =
      source.blocks.map fun item => (item.1, Versioning.compileBlock source item.2) from rfl,
      List.any_map]
    exact resolved
  apply elaborate_isSome_proof
  · have shape := compile_entry_shape_proof source
    refine body_isSome_proof _ _ _ (shape.1.trans fragment.1) (fun name listed => ?_)
      (fun label listed => labels label (known label (.inl (shape.2 ▸ listed))))
    obtain ⟨i, _, here⟩ := named name listed
    exact first_isSome_proof _ _ ⟨i, here⟩
  · intro i
    have listed : (Versioning.compile source).blocks[i] ∈ (Versioning.compile source).blocks :=
      List.getElem_mem _
    obtain ⟨item, member, eq⟩ := List.mem_map.mp listed
    rw [← eq]
    have shape := compileBlock_shape_proof source item.2
    refine body_isSome_proof _ _ _ (shape.1.trans (fragment.2 item member)) (fun name read => ?_)
      (fun label target => labels label (known label (.inr ⟨item, member, shape.2 ▸ target⟩)))
    rw [compileBlock_names_proof source item member name read]
    exact bindName_isSome_proof _ _ _ (.inl rfl)

end Graph

/-! ## The lowering of a φ graph -/

section Lowered

open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph Row OrderedExits.lower OrderedExits.lowerBlock
  OrderedExits.branchValue OrderedExits.checkExits OrderedExits.check OrderedExits.lookup liftBody
  liftTerm liftOp decode)

variable {W K : Type w} {F : Type v}

theorem liftOp_plain_proof (op : Op W F) : plainOp (liftOp op) = plainOp op := by
  cases op <;> rfl

/-- Lifting keeps the fragment and the labels of a terminator. -/
theorem liftTerm_shape_proof (branch : Option K → Val W → Val (Option W)) :
    (tail : Term W (Option K) F) →
    plainRegion (liftTerm branch tail).toRegion = plainRegion tail.toRegion ∧
      (liftTerm branch tail).targets = tail.targets
  | .br _ _ => ⟨rfl, rfl⟩
  | .case op x left y right => by
    have inLeft := liftTerm_shape_proof branch left
    have inRight := liftTerm_shape_proof branch right
    exact ⟨by simp only [liftTerm, Term.toRegion, plainRegion, liftOp_plain_proof, inLeft.1,
        inRight.1],
      by simp only [liftTerm, Term.targets, inLeft.2, inRight.2]⟩

/-- Lifting keeps the fragment and the labels of a body. -/
theorem liftBody_shape_proof (branch : Option K → Val W → Val (Option W)) :
    (source : Body W (Option K) F) →
    plainRegion (liftBody branch source).toRegion = plainRegion source.toRegion ∧
      (liftBody branch source).targets = source.targets
  | .term tail => liftTerm_shape_proof branch tail
  | .let1 x op rest => by
    have inRest := liftBody_shape_proof branch rest
    exact ⟨by simp only [liftBody, Body.toRegion, plainRegion, liftOp_plain_proof, inRest.1],
      inRest.2⟩
  | .let2 x y op rest => by
    have inRest := liftBody_shape_proof branch rest
    exact ⟨by simp only [liftBody, Body.toRegion, plainRegion, liftOp_plain_proof, inRest.1],
      inRest.2⟩

/-- Decoding the φ operands keeps the fragment and the labels. -/
theorem decode_shape_proof (source : Body (Option W) (Option K) F) : (rows : List (Row W K)) →
    plainRegion (decode rows source).toRegion = plainRegion source.toRegion ∧
      (decode rows source).targets = source.targets
  | [] => ⟨rfl, rfl⟩
  | first :: rest => by
    have inRest := decode_shape_proof source rest
    exact ⟨by simp only [decode, Body.toRegion, plainRegion, plainOp, Bool.true_and, inRest.1],
      inRest.2⟩

variable [DecidableEq K]

omit [DecidableEq K] in
/-- A found entry of an association list is a member of the list. -/
theorem lookup_some_mem_proof [DecidableEq K] {B : Type*} : (entries : List (K × B)) → {key : K} →
    {value : B} → entries.lookup key = some value → (key, value) ∈ entries
  | [], _, _, found => by cases found
  | (k, b) :: rest, key, value, found => by
    simp only [List.lookup] at found
    split at found
    · rename_i same
      cases found
      rw [eq_of_beq same]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_some_mem_proof rest found)

/-- The lowering of a φ graph in the fragment is in the fragment. -/
theorem lower_plain_proof (graph : Graph W K F) (fragment : Phi.plain graph = true) :
    plain (OrderedExits.lower graph) = true := by
  simp only [Phi.plain, plainBody, Bool.and_eq_true, List.all_eq_true] at fragment
  simp only [plain, plainBody, Bool.and_eq_true, List.all_eq_true]
  refine ⟨(liftBody_shape_proof _ graph.entry).1.trans fragment.1, fun item member => ?_⟩
  obtain ⟨source, original, rfl⟩ := List.mem_map.mp member
  exact ((decode_shape_proof _ source.2.rows).1.trans (liftBody_shape_proof _ source.2.body).1).trans
    (fragment.2 source original)

/-- The jumps of the lowering of a φ graph go to blocks or declared exits,
when those of the φ graph do. -/
theorem lower_resolves_proof (graph : Graph W K F) (exits : List (Option K))
    (partition : OrderedExits.checkExits graph exits = true) :
    resolves (OrderedExits.lower graph) exits = true := by
  simp only [OrderedExits.checkExits, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    List.mem_append, List.mem_flatMap, List.contains_iff_mem] at partition
  have known := partition.2
  have block : ∀ target, (OrderedExits.lookup graph target).isSome = true →
      ∃ item ∈ (OrderedExits.lower graph).blocks, target = item.1 := by
    intro target present
    cases target with
    | none => simp [OrderedExits.lookup] at present
    | some key =>
      obtain ⟨found, looked⟩ := Option.isSome_iff_exists.mp present
      have member := lookup_some_mem_proof graph.blocks (key := key) looked
      exact ⟨(some key, OrderedExits.lowerBlock graph key found),
        List.mem_map.mpr ⟨(key, found), member, rfl⟩, rfl⟩
  simp only [resolves, List.all_eq_true, List.mem_append, List.mem_flatMap, Bool.or_eq_true,
    List.any_eq_true, beq_iff_eq, List.contains_iff_mem]
  rintro label (inEntry | ⟨item, member, inBlock⟩)
  · rw [show (OrderedExits.lower graph).entry = liftBody (OrderedExits.branchValue graph none)
      graph.entry from rfl, (liftBody_shape_proof _ graph.entry).2] at inEntry
    exact (known label (.inl inEntry)).imp (block label) id
  · obtain ⟨source, original, rfl⟩ := List.mem_map.mp member
    have inSource : label ∈ source.2.body.targets := by
      have shape := (decode_shape_proof (liftBody (OrderedExits.branchValue graph (some source.1))
        source.2.body) source.2.rows).2.trans (liftBody_shape_proof _ source.2.body).2
      exact shape ▸ inBlock
    exact (known label (.inr ⟨source, original, inSource⟩)).imp (block label) id

variable [DecidableEq W] {n : Nat}

/-- The lowering of a φ graph elaborates at the given captures, when its
operands are in the fragment, its jumps go to blocks or declared exits,
and the versioned entry reads only captures at their initial version. -/
theorem lower_compile_proof (graph : Graph W K F) (exits : List (Option K))
    (captures : Fin n → Option W) (partition : OrderedExits.checkExits graph exits = true)
    (fragment : Phi.plain graph = true)
    (named : entryNamed (OrderedExits.lower graph) captures = true) :
    (compile (OrderedExits.lower graph) exits captures).isSome = true :=
  compile_isSome_proof _ exits captures (lower_plain_proof graph fragment)
    (lower_resolves_proof graph exits partition) named

/-- The lowering of a φ graph elaborates at captures that cover the given
registers, when the existing check accepts the graph with every block
arriving with those registers only and its operands are in the
fragment. -/
theorem checked_compile_proof (graph : Graph W K F) (exits : List (Option K)) (inputs : List W)
    (captures : Fin n → Option W)
    (ok : OrderedExits.check graph exits inputs
      (graph.blocks.map fun (key, _) => (key, inputs)) = true)
    (fragment : Phi.plain graph = true) (covered : ∀ z ∈ inputs, ∃ i, captures i = some z) :
    (compile (OrderedExits.lower graph) exits captures).isSome = true := by
  have partition : OrderedExits.checkExits graph exits = true := by
    simp only [OrderedExits.check, Bool.and_eq_true] at ok
    exact ok.1
  refine lower_compile_proof graph exits captures partition fragment ?_
  simp only [entryNamed, List.all_eq_true, List.any_eq_true, decide_eq_true_eq]
  intro name listed
  obtain ⟨z, input, rfl⟩ := (Phi.Forward.lowered_entry graph exits inputs ok).2 name listed
  obtain ⟨i, here⟩ := covered z input
  exact ⟨i, List.mem_finRange i, by rw [here]⟩

end Lowered

/-! ## The normalized graph -/

section Forwarded

open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph OrderedExits.lower OrderedExits.checkExits
  OrderedExits.check Forward.Name Forward.Table Forward.forward Forward.closed Forward.entryKept
  Forward.inputArrivals)

variable {V K : Type w} {F : Type v}

theorem rename_plain_proof {W : Type w} (read : V → W) (op : Op V F) :
    plainOp (op.rename read) = plainOp op := by
  cases op <;> rfl

/-- Renaming the reads of a terminator keeps the fragment. -/
theorem forward_term_plain_proof (read : V → Forward.Name V K) : (tail : Term V (Option K) F) →
    plainRegion (Phi.Forward.term read tail).toRegion = plainRegion tail.toRegion
  | .br _ _ => rfl
  | .case op x left y right => by
    simp only [Phi.Forward.term, Term.toRegion, plainRegion, rename_plain_proof,
      forward_term_plain_proof read left, forward_term_plain_proof read right]

/-- Renaming the reads of a body keeps the fragment. -/
theorem forward_body_plain_proof (read : V → Forward.Name V K) : (source : Body V (Option K) F) →
    plainRegion (Phi.Forward.body read source).toRegion = plainRegion source.toRegion
  | .term tail => forward_term_plain_proof read tail
  | .let1 x op rest => by
    simp only [Phi.Forward.body, Body.toRegion, plainRegion, rename_plain_proof,
      forward_body_plain_proof read rest]
  | .let2 x y op rest => by
    simp only [Phi.Forward.body, Body.toRegion, plainRegion, rename_plain_proof,
      forward_body_plain_proof read rest]

variable [DecidableEq V] [DecidableEq K] {n : Nat}

/-- The normalized graph of a φ graph in the fragment is in the
fragment. -/
theorem forward_plain_proof (graph : Graph V K F) (table : Forward.Table V K)
    (fragment : Phi.plain graph = true) : Phi.plain (Forward.forward graph table) = true := by
  simp only [Phi.plain, plainBody, Bool.and_eq_true, List.all_eq_true] at fragment ⊢
  refine ⟨(forward_body_plain_proof _ graph.entry).trans fragment.1, fun item member => ?_⟩
  obtain ⟨source, original, rfl⟩ := List.mem_map.mp member
  exact (forward_body_plain_proof _ source.2.body).trans (fragment.2 source original)

/-- The lowering of the normalized graph of a closed table elaborates at
captures that cover the declared inputs. -/
theorem closed_compile_proof (graph : Graph V K F) (table : Forward.Table V K)
    (exits : List (Option K)) (inputs : List V) (captures : Fin n → Option (Forward.Name V K))
    (isClosed : Forward.closed graph table exits inputs = true)
    (fragment : Phi.plain graph = true)
    (covered : ∀ z ∈ inputs, ∃ i, captures i = some (Sum.inl z)) :
    (compile (OrderedExits.lower (Forward.forward graph table)) exits captures).isSome = true := by
  have arrivals : Forward.inputArrivals graph inputs =
      (Forward.forward graph table).blocks.map fun (key, _) => (key, inputs.map Sum.inl) := by
    simp [Forward.inputArrivals, Forward.forward, List.map_map, Function.comp_def]
  simp only [Forward.closed, arrivals] at isClosed
  refine checked_compile_proof _ exits (inputs.map Sum.inl) captures isClosed
    (forward_plain_proof graph table fragment) fun z listed => ?_
  obtain ⟨a, input, rfl⟩ := List.mem_map.mp listed
  exact covered a input

/-- The lowering of the normalized graph elaborates at captures that
cover the declared inputs, for a table that keeps the entry. -/
theorem kept_compile_proof (graph : Graph V K F) (table : Forward.Table V K)
    (exits : List (Option K)) (inputs : List V) (captures : Fin n → Option (Forward.Name V K))
    (partition : OrderedExits.checkExits graph exits = true)
    (kept : Forward.entryKept graph table inputs = true) (fragment : Phi.plain graph = true)
    (covered : ∀ z ∈ inputs, ∃ i, captures i = some (Sum.inl z)) :
    (compile (OrderedExits.lower (Forward.forward graph table)) exits captures).isSome = true := by
  refine lower_compile_proof _ exits captures
    ((Phi.Forward.checkExits_forward graph table exits).trans partition)
    (forward_plain_proof graph table fragment) ?_
  simp only [Forward.entryKept, List.all_eq_true, List.contains_iff_mem, List.mem_map] at kept
  simp only [entryNamed, List.all_eq_true, List.any_eq_true, decide_eq_true_eq]
  intro name listed
  obtain ⟨z, input, rfl⟩ := kept name listed
  obtain ⟨i, here⟩ := covered z input
  exact ⟨i, List.mem_finRange i, by rw [here]⟩

end Forwarded

end Silmaril.Isotope.Bridge.NamedFlat
