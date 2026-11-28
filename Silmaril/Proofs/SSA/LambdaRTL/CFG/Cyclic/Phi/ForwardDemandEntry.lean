module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Forward.Demand.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.OrderedExits.Split.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Version.Flat.Thms
public import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Phi.ForwardDemand
public import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Phi.Forward

public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Forward

open Silmaril.SSA.LambdaRTL (Val Op Region)
open Silmaril.SSA.LambdaRTL.CFG (Body Term)

universe v w

/-! ## Reads in scope

A body is inScope over a list of registers when, on every path, each read
is of a listed register or of an earlier definition on the path, and each
record that a jump carries holds listed registers only. -/

section Scoped

variable {V L : Type w} {F : Type v}

/-- A terminator whose reads and carried records are in scope. -/
def TermScoped (records : L → Option (List V)) : List V → Term V L F → Prop
  | avail, .br label value =>
    (∀ z ∈ value.fvList, z ∈ avail) ∧ ∀ ys, records label = some ys → ∀ z ∈ ys, z ∈ avail
  | avail, .case operand x left y right =>
    (∀ z ∈ operand.fvList, z ∈ avail) ∧ TermScoped records (avail ++ [x]) left ∧
      TermScoped records (avail ++ [y]) right

/-- A body whose reads and carried records are in scope. -/
def BodyScoped (records : L → Option (List V)) : List V → Body V L F → Prop
  | avail, .let1 x operand rest =>
    (∀ z ∈ operand.fvList, z ∈ avail) ∧ BodyScoped records (avail ++ [x]) rest
  | avail, .let2 x y operand rest =>
    (∀ z ∈ operand.fvList, z ∈ avail) ∧ BodyScoped records (avail ++ [x, y]) rest
  | avail, .term tail => TermScoped records avail tail

variable [DecidableEq V]

/-- The free reads of a inScope terminator are listed. -/
theorem term_fv_proof (records : L → Option (List V)) :
    (tail : Term V L F) → (avail : List V) → TermScoped records avail tail →
    ∀ z ∈ tail.toRegion.fvList, z ∈ avail
  | .br _ _, _, inScope => inScope.1
  | .case operand x left y right, avail, inScope => by
    intro z member
    simp only [Term.toRegion, Region.fvList, List.mem_append, List.mem_filter,
      decide_eq_true_eq] at member
    rcases member with (member | ⟨member, other⟩) | ⟨member, other⟩
    · exact inScope.1 z member
    · have := term_fv_proof records left _ inScope.2.1 z member
      simpa [other] using this
    · have := term_fv_proof records right _ inScope.2.2 z member
      simpa [other] using this

/-- The free reads of a inScope body are listed. -/
theorem body_fv_proof (records : L → Option (List V)) :
    (source : Body V L F) → (avail : List V) → BodyScoped records avail source →
    ∀ z ∈ source.toRegion.fvList, z ∈ avail
  | .term tail, avail, inScope => term_fv_proof records tail avail inScope
  | .let1 x operand rest, avail, inScope => by
    intro z member
    simp only [Body.toRegion, Region.fvList, List.mem_append, List.mem_filter,
      decide_eq_true_eq] at member
    rcases member with member | ⟨member, other⟩
    · exact inScope.1 z member
    · have := body_fv_proof records rest _ inScope.2 z member
      simpa [other] using this
  | .let2 x y operand rest, avail, inScope => by
    intro z member
    simp only [Body.toRegion, Region.fvList, List.mem_append, List.mem_filter,
      decide_eq_true_eq] at member
    rcases member with member | ⟨member, other⟩
    · exact inScope.1 z member
    · have := body_fv_proof records rest _ inScope.2 z member
      simpa [other.1, other.2] using this

omit [DecidableEq V] in
/-- A value read at the current versions. -/
theorem rn_fv_proof (cur : V → Nat) : (value : Val V) →
    (Version.rn cur value).fvList = value.fvList.map fun z => (z, cur z)
  | .var _ => rfl
  | .unit => rfl
  | .pair a b => by
    simp only [Version.rn, Val.fvList, List.map_append, rn_fv_proof cur a, rn_fv_proof cur b]

omit [DecidableEq V] in
/-- An operand read at the current versions. -/
theorem rnOp_fv_proof (cur : V → Nat) (operand : Op V F) :
    (Version.rnOp cur operand).fvList = operand.fvList.map fun z => (z, cur z) := by
  cases operand <;> simp only [Version.rnOp, Op.fvList, rn_fv_proof]

omit [DecidableEq V] in
/-- A record read at the current versions. -/
theorem pack_fv_proof (cur : V → Nat) : (registers : List V) →
    (Version.pack cur registers).fvList = registers.map fun z => (z, cur z)
  | [] => rfl
  | y :: rest => by
    simp only [Version.pack, Val.fvList, List.map_cons, pack_fv_proof cur rest]
    rfl

variable [DecidableEq L]

/-- The free reads of the versioned region of a inScope terminator are
listed registers at their current versions. -/
theorem version_term_proof (records : L → Option (List V)) (live : List V) :
    (tail : Term V L F) → (avail : List V) → (cur : V → Nat) → (depth : Nat) →
    TermScoped records avail tail →
    ∀ name ∈ (Version.version records live cur depth tail.toRegion).fvList,
      ∃ z ∈ avail, name = (z, cur z)
  | .br label value, avail, cur, depth, inScope => by
    intro name member
    simp only [Term.toRegion, Version.version] at member
    cases found : records label with
    | none =>
      rw [found] at member
      simp only [Region.fvList, rn_fv_proof, List.mem_map] at member
      obtain ⟨z, read, rfl⟩ := member
      exact ⟨z, inScope.1 z read, rfl⟩
    | some ys =>
      rw [found] at member
      simp only [Region.fvList, Val.fvList, rn_fv_proof, pack_fv_proof, List.mem_append,
        List.mem_map] at member
      rcases member with ⟨z, read, rfl⟩ | ⟨z, carried, rfl⟩
      · exact ⟨z, inScope.1 z read, rfl⟩
      · exact ⟨z, inScope.2 ys found z carried, rfl⟩
  | .case operand x left y right, avail, cur, depth, inScope => by
    intro name member
    simp only [Term.toRegion, Version.version, Region.fvList, rnOp_fv_proof, List.mem_append,
      List.mem_map, List.mem_filter, decide_eq_true_eq] at member
    rcases member with (⟨z, read, rfl⟩ | ⟨member, other⟩) | ⟨member, other⟩
    · exact ⟨z, inScope.1 z read, rfl⟩
    · obtain ⟨z, listed, rfl⟩ := version_term_proof records live left _ _ _ inScope.2.1 name member
      by_cases same : z = x
      · subst same
        simp [Version.setv] at other
      · refine ⟨z, by simpa [same] using listed, ?_⟩
        simp [Version.setv, same]
    · obtain ⟨z, listed, rfl⟩ := version_term_proof records live right _ _ _ inScope.2.2 name member
      by_cases same : z = y
      · subst same
        simp [Version.setv] at other
      · refine ⟨z, by simpa [same] using listed, ?_⟩
        simp [Version.setv, same]

/-- The free reads of the versioned region of a inScope body are listed
registers at their current versions. -/
theorem version_body_proof (records : L → Option (List V)) (live : List V) :
    (source : Body V L F) → (avail : List V) → (cur : V → Nat) → (depth : Nat) →
    BodyScoped records avail source →
    ∀ name ∈ (Version.version records live cur depth source.toRegion).fvList,
      ∃ z ∈ avail, name = (z, cur z)
  | .term tail, avail, cur, depth, inScope =>
    version_term_proof records live tail avail cur depth inScope
  | .let1 x operand rest, avail, cur, depth, inScope => by
    intro name member
    simp only [Body.toRegion, Version.version, Region.fvList, rnOp_fv_proof, List.mem_append,
      List.mem_map, List.mem_filter, decide_eq_true_eq] at member
    rcases member with ⟨z, read, rfl⟩ | ⟨member, other⟩
    · exact ⟨z, inScope.1 z read, rfl⟩
    · obtain ⟨z, listed, rfl⟩ := version_body_proof records live rest _ _ _ inScope.2 name member
      by_cases same : z = x
      · subst same
        simp [Version.setv] at other
      · refine ⟨z, by simpa [same] using listed, ?_⟩
        simp [Version.setv, same]
  | .let2 x y operand rest, avail, cur, depth, inScope => by
    intro name member
    simp only [Body.toRegion, Version.version, Region.fvList, rnOp_fv_proof, List.mem_append,
      List.mem_map, List.mem_filter, decide_eq_true_eq] at member
    rcases member with ⟨z, read, rfl⟩ | ⟨member, other⟩
    · exact ⟨z, inScope.1 z read, rfl⟩
    · obtain ⟨z, listed, rfl⟩ := version_body_proof records live rest _ _ _ inScope.2 name member
      by_cases sameY : z = y
      · subst sameY
        simp [Version.setv] at other
      · by_cases sameX : z = x
        · subst sameX
          simp [Version.setv, sameY] at other
        · refine ⟨z, by simpa [sameX, sameY] using listed, ?_⟩
          simp [Version.setv, sameX, sameY]

end Scoped

/-! ## The versioned body -/

section Readback

variable {V L : Type w} {F : Type v}

/-- A body that is recognized in a region reads back to the region. -/
theorem body_ofRegion_proof (region : Region V L F) (source : Body V L F)
    (found : Body.ofRegion? region = some source) : source.toRegion = region := by
  have whole : ofRegion? region = some ⟨source, []⟩ := by
    cases region with
    | join => simp [Body.ofRegion?, Term.ofRegion?] at found
    | br => simp [ofRegion?, ofRegion?.collect, found]
    | let1 => simp [ofRegion?, ofRegion?.collect, found]
    | let2 => simp [ofRegion?, ofRegion?.collect, found]
    | case => simp [ofRegion?, ofRegion?.collect, found]
  exact (ofRegion?_eq_some_iff region ⟨source, []⟩).1 whole

/-- The versioned body reads back to the versioned region of the body. -/
theorem versionBody_region_proof [DecidableEq V] [DecidableEq L] (source : Body V L F)
    (labels : L → Option (List V)) (live : List V) (current : V → Nat) (depth : Nat) :
    (Versioning.versionBody source labels live current depth).toRegion =
      Version.version labels live current depth source.toRegion :=
  body_ofRegion_proof _ _ (Option.some_get _).symm

end Readback

/-! ## Routes that pass the scan -/

section Routes

variable {W K : Type w} {F : Type v}

/-- A terminator of a φ graph whose reads are in scope: the payload of a
return, or the φ operands of the edge of a jump. -/
def PhiTermScoped (edgeReads : K → List W) : List W → Term W (Option K) F → Prop
  | avail, .br none value => ∀ z ∈ value.fvList, z ∈ avail
  | avail, .br (some target) _ => ∀ z ∈ edgeReads target, z ∈ avail
  | avail, .case operand x left y right =>
    (∀ z ∈ operand.fvList, z ∈ avail) ∧ PhiTermScoped edgeReads (avail ++ [x]) left ∧
      PhiTermScoped edgeReads (avail ++ [y]) right

/-- A body of a φ graph whose reads are in scope. -/
def PhiScoped (edgeReads : K → List W) : List W → Body W (Option K) F → Prop
  | avail, .let1 x operand rest =>
    (∀ z ∈ operand.fvList, z ∈ avail) ∧ PhiScoped edgeReads (avail ++ [x]) rest
  | avail, .let2 x y operand rest =>
    (∀ z ∈ operand.fvList, z ∈ avail) ∧ PhiScoped edgeReads (avail ++ [x, y]) rest
  | avail, .term tail => PhiTermScoped edgeReads avail tail

/-- A terminator has a route. -/
theorem termRoutes_ne_nil_proof (edgeReads : K → List W) :
    (tail : Term W (Option K) F) → GlobalSSA.termRoutes edgeReads tail ≠ []
  | .br none _ => by simp [GlobalSSA.termRoutes]
  | .br (some _) _ => by simp [GlobalSSA.termRoutes]
  | .case _ _ left _ _ => by
    have := termRoutes_ne_nil_proof edgeReads left
    simp [GlobalSSA.termRoutes, this]

/-- A body has a route. -/
theorem bodyRoutes_ne_nil_proof (edgeReads : K → List W) :
    (source : Body W (Option K) F) → GlobalSSA.bodyRoutes edgeReads source ≠ []
  | .term tail => termRoutes_ne_nil_proof edgeReads tail
  | .let1 _ _ rest => by
    have := bodyRoutes_ne_nil_proof edgeReads rest
    simp [GlobalSSA.bodyRoutes, this]
  | .let2 _ _ _ rest => by
    have := bodyRoutes_ne_nil_proof edgeReads rest
    simp [GlobalSSA.bodyRoutes, this]

variable [DecidableEq W]

/-- A scan that passes a read has the registers of the read. -/
theorem scan_read_proof (avail names : List W) (rest : List (GlobalSSA.Access W))
    (ok : (GlobalSSA.Access.scan avail (.read names :: rest)).isSome = true) :
    (∀ z ∈ names, z ∈ avail) ∧ (GlobalSSA.Access.scan avail rest).isSome = true := by
  simp only [GlobalSSA.Access.scan] at ok
  split at ok
  · rename_i all
    exact ⟨fun z member => by simpa using List.all_eq_true.mp all z member, ok⟩
  · simp at ok

/-- A terminator whose routes pass the scan has its reads in scope. -/
theorem term_scoped_proof (edgeReads : K → List W) :
    (tail : Term W (Option K) F) → (avail : List W) →
    (∀ route ∈ GlobalSSA.termRoutes edgeReads tail,
      (GlobalSSA.Access.scan avail route.accesses).isSome = true) →
    PhiTermScoped edgeReads avail tail
  | .br none value, avail, ok =>
    (scan_read_proof avail _ _ (ok ⟨none, [.read value.fvList]⟩
      (by simp [GlobalSSA.termRoutes]))).1
  | .br (some target) _, avail, ok =>
    (scan_read_proof avail _ _ (ok ⟨some target, [.read (edgeReads target)]⟩
      (by simp [GlobalSSA.termRoutes]))).1
  | .case operand x left y right, avail, ok => by
    have leftOk : ∀ route ∈ GlobalSSA.termRoutes edgeReads left,
        (GlobalSSA.Access.scan avail
          (.read operand.fvList :: .define [x] :: route.accesses)).isSome = true :=
      fun route member => ok _ (List.mem_append_left _ (List.mem_map.mpr ⟨route, member, rfl⟩))
    have rightOk : ∀ route ∈ GlobalSSA.termRoutes edgeReads right,
        (GlobalSSA.Access.scan avail
          (.read operand.fvList :: .define [y] :: route.accesses)).isSome = true :=
      fun route member => ok _ (List.mem_append_right _ (List.mem_map.mpr ⟨route, member, rfl⟩))
    obtain ⟨first, firstMember⟩ :=
      List.exists_mem_of_ne_nil _ (termRoutes_ne_nil_proof edgeReads left)
    exact ⟨(scan_read_proof avail _ _ (leftOk first firstMember)).1,
      term_scoped_proof edgeReads left _ fun route member =>
        (scan_read_proof avail _ _ (leftOk route member)).2,
      term_scoped_proof edgeReads right _ fun route member =>
        (scan_read_proof avail _ _ (rightOk route member)).2⟩

/-- A body whose routes pass the scan has its reads in scope. -/
theorem body_scoped_proof (edgeReads : K → List W) :
    (source : Body W (Option K) F) → (avail : List W) →
    (∀ route ∈ GlobalSSA.bodyRoutes edgeReads source,
      (GlobalSSA.Access.scan avail route.accesses).isSome = true) →
    PhiScoped edgeReads avail source
  | .term tail, avail, ok => term_scoped_proof edgeReads tail avail ok
  | .let1 x operand rest, avail, ok => by
    have restOk : ∀ route ∈ GlobalSSA.bodyRoutes edgeReads rest,
        (GlobalSSA.Access.scan avail
          (.read operand.fvList :: .define [x] :: route.accesses)).isSome = true :=
      fun route member => ok _ (List.mem_map.mpr ⟨route, member, rfl⟩)
    obtain ⟨first, firstMember⟩ :=
      List.exists_mem_of_ne_nil _ (bodyRoutes_ne_nil_proof edgeReads rest)
    exact ⟨(scan_read_proof avail _ _ (restOk first firstMember)).1,
      body_scoped_proof edgeReads rest _ fun route member =>
        (scan_read_proof avail _ _ (restOk route member)).2⟩
  | .let2 x y operand rest, avail, ok => by
    have restOk : ∀ route ∈ GlobalSSA.bodyRoutes edgeReads rest,
        (GlobalSSA.Access.scan avail
          (.read operand.fvList :: .define [x, y] :: route.accesses)).isSome = true :=
      fun route member => ok _ (List.mem_map.mpr ⟨route, member, rfl⟩)
    obtain ⟨first, firstMember⟩ :=
      List.exists_mem_of_ne_nil _ (bodyRoutes_ne_nil_proof edgeReads rest)
    exact ⟨(scan_read_proof avail _ _ (restOk first firstMember)).1,
      body_scoped_proof edgeReads rest _ fun route member =>
        (scan_read_proof avail _ _ (restOk route member)).2⟩

end Routes

/-! ## From the φ graph to its lowering -/

section Lower

variable {W K : Type w} {F : Type v}

/-- The reads of a lifted value. -/
theorem liftVal_fv_proof : (value : Val W) → (liftVal value).fvList = value.fvList.map some
  | .var _ => rfl
  | .unit => rfl
  | .pair a b => by
    simp only [liftVal, Val.fvList, List.map_append, liftVal_fv_proof a, liftVal_fv_proof b]

/-- The reads of a lifted operand. -/
theorem liftOp_fv_proof (operand : Op W F) : (liftOp operand).fvList = operand.fvList.map some := by
  cases operand <;> simp only [liftOp, Op.fvList, liftVal_fv_proof]

/-- The reads of the packet of an edge. -/
theorem edge_pack_fv_proof : (arguments : List (Val W)) →
    (pack arguments).fvList = (arguments.flatMap Val.fvList).map some
  | [] => rfl
  | first :: rest => by
    simp only [pack, Val.fvList, List.flatMap_cons, List.map_append, liftVal_fv_proof,
      edge_pack_fv_proof rest]

variable [DecidableEq W] [DecidableEq K]

omit [DecidableEq W] in
/-- A lifted terminator is in scope when the terminator of the φ graph,
with its exits collapsed, is in scope, every target is a block or a
declared exit, and no declared exit is a block. -/
theorem lift_term_proof (graph : Graph W K F) (exits : List (Option K)) (pred : Option K)
    (records : Option K → Option (List (Option W))) (base : List W)
    (carried : ∀ label ys, records label = some ys → ∀ z ∈ ys, z ∈ base.map some)
    (apart : ∀ target ∈ exits, OrderedExits.lookup graph target = none) :
    (tail : Term W (Option K) F) → (avail : List W) → (∀ z ∈ base, z ∈ avail) →
    (∀ target ∈ tail.targets,
      (OrderedExits.lookup graph target).isSome = true ∨ target ∈ exits) →
    PhiTermScoped (GlobalSSA.edgeReads graph pred) avail
      (tail.relabel (OrderedExits.scopeLabel exits)) →
    TermScoped records (avail.map some) (liftTerm (OrderedExits.branchValue graph pred) tail)
  | .br target value, avail, grows, known, inScope => by
    refine ⟨fun z read => ?_, fun ys found z member => ?_⟩
    · have here := known target (by simp [Term.targets])
      cases looked : OrderedExits.lookup graph target with
      | none =>
        have declared : target ∈ exits := here.resolve_left (by simp [looked])
        have collapsed : OrderedExits.scopeLabel exits target = none := by
          simp [OrderedExits.scopeLabel, declared]
        simp only [Term.relabel, collapsed, PhiTermScoped] at inScope
        simp only [OrderedExits.branchValue, looked, Option.elim, liftVal_fv_proof,
          List.mem_map] at read
        obtain ⟨a, member, rfl⟩ := read
        exact List.mem_map.mpr ⟨a, inScope a member, rfl⟩
      | some found =>
        cases target with
        | none => simp [OrderedExits.lookup] at looked
        | some key =>
          have internal : some key ∉ exits := fun declared => by
            simp [apart _ declared] at looked
          have kept : OrderedExits.scopeLabel exits (some key) = some key := by
            simp [OrderedExits.scopeLabel, internal]
          have block : graph.blocks.lookup key = some found := looked
          simp only [Term.relabel, kept, PhiTermScoped, GlobalSSA.edgeReads, block,
            Option.elim] at inScope
          simp only [OrderedExits.branchValue, looked, Option.elim, edge_pack_fv_proof,
            List.mem_map] at read
          obtain ⟨a, member, rfl⟩ := read
          exact List.mem_map.mpr ⟨a, inScope a member, rfl⟩
    · obtain ⟨a, listed, rfl⟩ := List.mem_map.mp (carried _ ys found z member)
      exact List.mem_map.mpr ⟨a, grows a listed, rfl⟩
  | .case operand x left y right, avail, grows, known, inScope => by
    simp only [Term.relabel, PhiTermScoped] at inScope
    have leftScoped := lift_term_proof graph exits pred records base carried apart left
      (avail ++ [x]) (fun z member => List.mem_append_left _ (grows z member))
      (fun target member => known target (by simp [Term.targets, member])) inScope.2.1
    have rightScoped := lift_term_proof graph exits pred records base carried apart right
      (avail ++ [y]) (fun z member => List.mem_append_left _ (grows z member))
      (fun target member => known target (by simp [Term.targets, member])) inScope.2.2
    rw [List.map_append] at leftScoped rightScoped
    refine ⟨fun z read => ?_, leftScoped, rightScoped⟩
    simp only [liftOp_fv_proof, List.mem_map] at read
    obtain ⟨a, member, rfl⟩ := read
    exact List.mem_map.mpr ⟨a, inScope.1 a member, rfl⟩

omit [DecidableEq W] in
/-- A lifted body is in scope when the body of the φ graph, with its exits
collapsed, is in scope, every target is a block or a declared exit, and
no declared exit is a block. -/
theorem lift_body_proof (graph : Graph W K F) (exits : List (Option K)) (pred : Option K)
    (records : Option K → Option (List (Option W))) (base : List W)
    (carried : ∀ label ys, records label = some ys → ∀ z ∈ ys, z ∈ base.map some)
    (apart : ∀ target ∈ exits, OrderedExits.lookup graph target = none) :
    (source : Body W (Option K) F) → (avail : List W) → (∀ z ∈ base, z ∈ avail) →
    (∀ target ∈ source.targets,
      (OrderedExits.lookup graph target).isSome = true ∨ target ∈ exits) →
    PhiScoped (GlobalSSA.edgeReads graph pred) avail
      (source.relabel (OrderedExits.scopeLabel exits)) →
    BodyScoped records (avail.map some) (liftBody (OrderedExits.branchValue graph pred) source)
  | .term tail, avail, grows, known, inScope =>
    lift_term_proof graph exits pred records base carried apart tail avail grows known inScope
  | .let1 x operand rest, avail, grows, known, inScope => by
    simp only [Body.relabel, PhiScoped] at inScope
    have restScoped := lift_body_proof graph exits pred records base carried apart rest
      (avail ++ [x]) (fun z member => List.mem_append_left _ (grows z member)) known inScope.2
    rw [List.map_append] at restScoped
    refine ⟨fun z read => ?_, restScoped⟩
    simp only [liftOp_fv_proof, List.mem_map] at read
    obtain ⟨a, member, rfl⟩ := read
    exact List.mem_map.mpr ⟨a, inScope.1 a member, rfl⟩
  | .let2 x y operand rest, avail, grows, known, inScope => by
    simp only [Body.relabel, PhiScoped] at inScope
    have restScoped := lift_body_proof graph exits pred records base carried apart rest
      (avail ++ [x, y]) (fun z member => List.mem_append_left _ (grows z member)) known inScope.2
    rw [List.map_append] at restScoped
    refine ⟨fun z read => ?_, restScoped⟩
    simp only [liftOp_fv_proof, List.mem_map] at read
    obtain ⟨a, member, rfl⟩ := read
    exact List.mem_map.mpr ⟨a, inScope.1 a member, rfl⟩

omit [DecidableEq K] in
/-- A free read of a decoded body is the packet, or a free read of the
body that is not a φ destination. -/
theorem decode_fv_proof (source : Body (Option W) (Option K) F) : (rows : List (Row W K)) →
    ∀ z ∈ (decode rows source).toRegion.fvList,
      z = none ∨ (z ∈ source.toRegion.fvList ∧ ∀ row ∈ rows, z ≠ some row.dst)
  | [], z, member => .inr ⟨member, fun _ absent => by cases absent⟩
  | first :: rest, z, member => by
    simp only [decode, Body.toRegion, Region.fvList, Op.fvList, Val.fvList, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false, List.mem_filter, decide_eq_true_eq] at member
    rcases member with packet | ⟨member, other, _⟩
    · exact .inl packet
    · rcases decode_fv_proof source rest z member with packet | ⟨read, others⟩
      · exact .inl packet
      · exact .inr ⟨read, fun row listed => by
          rcases List.mem_cons.mp listed with rfl | listed
          · exact other
          · exact others row listed⟩

end Lower

/-! ## The entry of a closed graph -/

section Entry

variable {W K : Type w} {F : Type v} [DecidableEq W] [DecidableEq K]

omit [DecidableEq K] in
/-- A route that passes the check passes the scan. -/
theorem checkRoute_scan_proof [DecidableEq K] (certificate : GlobalSSA.Certificate W K)
    (avail : List W) (route : GlobalSSA.Route W K)
    (ok : GlobalSSA.checkRoute certificate avail route = true) :
    (GlobalSSA.Access.scan avail route.accesses).isSome = true := by
  cases scanned : GlobalSSA.Access.scan avail route.accesses with
  | none => simp [GlobalSSA.checkRoute, scanned] at ok
  | some _ => rfl

/-- A φ graph that the existing check accepts when every block arrives
with the given registers only. Its lowering carries records of those
registers only, and its lowered and versioned entry reads those registers
only, at their initial version. -/
theorem lowered_entry_proof (graph : Graph W K F) (exits : List (Option K)) (inputs : List W)
    (ok : OrderedExits.check graph exits inputs
      (graph.blocks.map fun (key, _) => (key, inputs)) = true) :
    (∀ label ys, Versioning.destinations (OrderedExits.lower graph) label = some ys →
        ∀ z ∈ ys, z ∈ inputs.map some) ∧
      ∀ name ∈ (Versioning.compile (OrderedExits.lower graph)).entry.toRegion.fvList,
        ∃ z ∈ inputs, name = (some z, 0) := by
  simp only [OrderedExits.check, Bool.and_eq_true] at ok
  obtain ⟨partition, global⟩ := ok
  simp only [GlobalSSA.check, Bool.and_eq_true, decide_eq_true_eq] at global
  obtain ⟨normalized, _, _, entryOk, blocksOk⟩ := global
  simp only [OrderedExits.checkExits, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at partition
  obtain ⟨⟨_, apartB⟩, knownB⟩ := partition
  have apart : ∀ target ∈ exits, OrderedExits.lookup graph target = none := fun target member =>
    Option.isNone_iff_eq_none.mp (apartB target member)
  have known : ∀ target ∈ graph.entry.targets ++
      graph.blocks.flatMap (fun item => item.2.body.targets),
      (OrderedExits.lookup graph target).isSome = true ∨ target ∈ exits := fun target member =>
    (knownB target member).imp id (by simp)
  have labels : (graph.blocks.map Prod.fst).Nodup := by
    simp only [Graph.check, Bool.and_eq_true, decide_eq_true_eq] at normalized
    have distinct := normalized.1.1
    simpa [OrderedExits.forScope, List.map_map, Function.comp_def] using distinct
  have reads : ∀ pred, GlobalSSA.edgeReads (OrderedExits.forScope graph exits) pred =
      GlobalSSA.edgeReads graph pred := fun pred =>
    funext (OrderedExits.edgeReads_forScope graph exits pred)
  -- the entry of the φ graph is in scope over the inputs
  have entryPhi : PhiScoped (GlobalSSA.edgeReads graph none) inputs
      (graph.entry.relabel (OrderedExits.scopeLabel exits)) := by
    rw [← reads none]
    exact body_scoped_proof _ _ inputs fun route member =>
      checkRoute_scan_proof _ inputs route (List.all_eq_true.mp entryOk route member)
  -- every block of the φ graph is in scope over the inputs and its φ destinations
  have blockPhi : ∀ key block, (key, block) ∈ graph.blocks →
      PhiScoped (GlobalSSA.edgeReads graph (some key)) (inputs ++ block.rows.map Row.dst)
        (block.body.relabel (OrderedExits.scopeLabel exits)) := by
    intro key block member
    have claimed : (key, inputs) ∈ graph.blocks.map (fun (key, _) => (key, inputs)) :=
      List.mem_map.mpr ⟨(key, block), member, rfl⟩
    have checked := List.all_eq_true.mp blocksOk (key, inputs) claimed
    simp only [Bool.and_eq_true] at checked
    have found : (OrderedExits.forScope graph exits).blocks.lookup key =
        some ⟨block.rows, block.body.relabel (OrderedExits.scopeLabel exits)⟩ :=
      lookup_mapped_proof
        (fun _ (source : Block W K F) =>
          (⟨source.rows, source.body.relabel (OrderedExits.scopeLabel exits)⟩ : Block W K F))
        graph.blocks labels member
    have routesOk := checked.2
    simp only [GlobalSSA.routes, found, Option.elim, List.all_eq_true, List.mem_map] at routesOk
    rw [← reads (some key)]
    exact body_scoped_proof _ _ _ fun route member =>
      checkRoute_scan_proof _ inputs _ (routesOk _ ⟨route, member, rfl⟩)
  -- the free reads of the lowered entry are inputs
  have entryFree : ∀ z ∈ (OrderedExits.lower graph).entry.toRegion.fvList, z ∈ inputs.map some :=
    body_fv_proof (fun _ => none) _ _
      (lift_body_proof graph exits none (fun _ => none) inputs (fun _ _ absent => by cases absent)
        apart graph.entry inputs (fun _ member => member)
        (fun target member => known target (List.mem_append_left _ member)) entryPhi)
  -- the free reads of a lowered block are the packet and inputs
  have blockFree : ∀ key block, (key, block) ∈ graph.blocks →
      ∀ z ∈ (OrderedExits.lowerBlock graph key block).body.toRegion.fvList,
        z = none ∨ z ∈ inputs.map some := by
    intro key block member z read
    have lifted := body_fv_proof (fun _ => none) _ _
      (lift_body_proof graph exits (some key) (fun _ => none) inputs
        (fun _ _ absent => by cases absent) apart block.body (inputs ++ block.rows.map Row.dst)
        (fun _ listed => List.mem_append_left _ listed)
        (fun target listed => known target (List.mem_append_right _
          (List.mem_flatMap.mpr ⟨(key, block), member, listed⟩)))
        (blockPhi key block member))
    rcases decode_fv_proof _ block.rows z read with packet | ⟨free, fresh⟩
    · exact .inl packet
    · obtain ⟨a, listed, rfl⟩ := List.mem_map.mp (lifted z free)
      rcases List.mem_append.mp listed with input | destination
      · exact .inr (List.mem_map.mpr ⟨a, input, rfl⟩)
      · obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp destination
        exact absurd rfl (fresh row rowMember)
  -- the support of the versioning is the packet and inputs
  have support : ∀ z ∈ Versioning.registers (OrderedExits.lower graph),
      z = none ∨ z ∈ inputs.map some := by
    intro z member
    simp only [Versioning.registers, List.mem_dedup, List.mem_append, List.mem_flatMap] at member
    rcases member with free | ⟨item, listed, free⟩
    · exact .inr (entryFree z free)
    · obtain ⟨⟨key, block⟩, source, rfl⟩ := List.mem_map.mp listed
      exact blockFree key block source z free
  -- so every record holds inputs only
  have carried : ∀ label ys, Versioning.destinations (OrderedExits.lower graph) label = some ys →
      ∀ z ∈ ys, z ∈ inputs.map some := by
    intro label ys found z member
    simp only [Versioning.destinations, Versioning.destinationsWith, Option.map_eq_some_iff] at found
    obtain ⟨target, looked, rfl⟩ := found
    obtain ⟨⟨key, block⟩, _, same⟩ := List.mem_map.mp (lookup_mem_proof _ looked)
    have parameter : target.param = none := by
      cases same
      rfl
    simp only [Versioning.slots, List.mem_filter, decide_eq_true_eq, parameter] at member
    exact (support z member.1).resolve_left member.2
  refine ⟨carried, fun name member => ?_⟩
  have entryScoped := lift_body_proof graph exits none
    (Versioning.destinations (OrderedExits.lower graph)) inputs carried apart graph.entry inputs
    (fun _ listed => listed) (fun target listed => known target (List.mem_append_left _ listed))
    entryPhi
  have region : (Versioning.compile (OrderedExits.lower graph)).entry.toRegion =
      Version.version (Versioning.destinations (OrderedExits.lower graph))
        (Versioning.registers (OrderedExits.lower graph)) (fun _ => 0) 0
        (OrderedExits.lower graph).entry.toRegion :=
    versionBody_region_proof _ _ _ _ _
  rw [region] at member
  obtain ⟨z, listed, rfl⟩ := version_body_proof _ _ _ _ _ _ entryScoped name member
  obtain ⟨a, input, rfl⟩ := List.mem_map.mp listed
  exact ⟨a, input, rfl⟩

end Entry

/-! ## The normalized graph -/

section Forwarded

variable {V K : Type w} {F : Type v} [DecidableEq V] [DecidableEq K]

/-- The arrival claims of a closed table are those of the normalized
graph in which every block arrives with the declared inputs only. -/
theorem inputArrivals_forward_proof (graph : Graph V K F) (table : Table V K) (inputs : List V) :
    inputArrivals graph inputs =
      (forward graph table).blocks.map fun (key, _) => (key, inputs.map Sum.inl) := by
  simp [inputArrivals, forward, List.map_map, Function.comp_def]

/-- Under a closed table, every record of the lowering holds declared
inputs only. -/
theorem closed_records_proof (graph : Graph V K F) (table : Table V K) (exits : List (Option K))
    (inputs : List V) (isClosed : closed graph table exits inputs = true) (label : Option K)
    (ys : List (Option (Name V K)))
    (found : Versioning.destinations (OrderedExits.lower (forward graph table)) label = some ys) :
    ∀ z ∈ ys, z ∈ inputs.map fun register => some (Sum.inl register) := by
  simp only [closed, inputArrivals_forward_proof graph table inputs] at isClosed
  intro z member
  have := (lowered_entry_proof (forward graph table) exits (inputs.map Sum.inl) isClosed).1 label
    ys found z member
  simpa [List.map_map, Function.comp_def] using this

/-- A closed table keeps the entry. -/
theorem closed_keeps_entry_proof (graph : Graph V K F) (table : Table V K)
    (exits : List (Option K)) (inputs : List V)
    (isClosed : closed graph table exits inputs = true) : entryKept graph table inputs = true := by
  simp only [closed, inputArrivals_forward_proof graph table inputs] at isClosed
  simp only [entryKept, List.all_eq_true]
  intro name member
  obtain ⟨z, listed, rfl⟩ :=
    (lowered_entry_proof (forward graph table) exits (inputs.map Sum.inl) isClosed).2 name member
  obtain ⟨a, input, rfl⟩ := List.mem_map.mp listed
  simp only [List.contains_iff_mem, List.mem_map]
  exact ⟨a, input, rfl⟩

end Forwarded

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Forward
