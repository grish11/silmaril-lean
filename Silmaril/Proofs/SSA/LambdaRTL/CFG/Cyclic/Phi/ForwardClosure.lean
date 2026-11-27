module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Forward.Closure.Defs
public import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Phi.ForwardDemandEntry

public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Forward

open Silmaril.SSA.LambdaRTL (Val Op)
open Silmaril.SSA.LambdaRTL.CFG (Body Term)

universe v w

/-! ## Reads of renamed operands -/

section Rename

variable {V W : Type w} {F : Type v}

/-- The reads of a renamed value. -/
theorem rename_fv_proof (f : V → W) : (value : Val V) →
    (value.rename f).fvList = value.fvList.map f
  | .var _ => rfl
  | .unit => rfl
  | .pair a b => by
    simp only [Val.rename, Val.fvList, List.map_append, rename_fv_proof f a, rename_fv_proof f b]

/-- The reads of a renamed operand. -/
theorem rename_op_fv_proof (f : V → W) (operand : Op V F) :
    (operand.rename f).fvList = operand.fvList.map f := by
  cases operand <;> simp only [Op.rename, Op.fvList, rename_fv_proof]

end Rename

/-! ## What a body needs from its arrival

A register is needed by a body when some path reads it before defining
it. A jump to a block reads the φ operands of its edge and what the
target is given. -/

section Needs

variable {V K : Type w} {F : Type v}

/-- A register that a terminator needs. -/
def TermNeeds (edge next : K → List V) (z : V) : Term V (Option K) F → Prop
  | .br none value => z ∈ value.fvList
  | .br (some target) _ => z ∈ edge target ∨ z ∈ next target
  | .case operand x left y right =>
    z ∈ operand.fvList ∨ (z ≠ x ∧ TermNeeds edge next z left) ∨
      (z ≠ y ∧ TermNeeds edge next z right)

/-- A register that a body needs. -/
def BodyNeeds (edge next : K → List V) (z : V) : Body V (Option K) F → Prop
  | .let1 x operand rest => z ∈ operand.fvList ∨ (z ≠ x ∧ BodyNeeds edge next z rest)
  | .let2 x y operand rest =>
    z ∈ operand.fvList ∨ (z ≠ x ∧ z ≠ y ∧ BodyNeeds edge next z rest)
  | .term tail => TermNeeds edge next z tail

variable [DecidableEq V]

/-- What a read and a definition at the head of a route need. -/
theorem needs_read_define_proof (names defined : List V) (rest : List (GlobalSSA.Access V))
    (z : V) :
    z ∈ needs (.read names :: .define defined :: rest) ↔
      z ∈ names ∨ (z ∉ defined ∧ z ∈ needs rest) := by
  simp [needs, and_comm]

/-- A register that a terminator needs is needed on one of its routes. -/
theorem term_needs_route_proof (edge next : K → List V) (z : V) :
    (tail : Term V (Option K) F) → TermNeeds edge next z tail →
    ∃ route ∈ GlobalSSA.termRoutes edge tail,
      z ∈ needs (route.accesses ++ [.read (route.target.elim [] next)])
  | .br none value, wanted =>
    ⟨⟨none, [.read value.fvList]⟩, by simp [GlobalSSA.termRoutes], by simpa [needs, TermNeeds] using wanted⟩
  | .br (some target) _, wanted =>
    ⟨⟨some target, [.read (edge target)]⟩, by simp [GlobalSSA.termRoutes],
      by simpa [needs, TermNeeds] using wanted⟩
  | .case operand x left y right, wanted => by
    rcases wanted with here | ⟨other, inLeft⟩ | ⟨other, inRight⟩
    · obtain ⟨first, member⟩ :=
        List.exists_mem_of_ne_nil _ (termRoutes_ne_nil_proof edge left)
      exact ⟨_, List.mem_append_left _ (List.mem_map.mpr ⟨first, member, rfl⟩),
        (needs_read_define_proof operand.fvList [x] _ z).mpr (.inl here)⟩
    · obtain ⟨route, member, needed⟩ := term_needs_route_proof edge next z left inLeft
      exact ⟨_, List.mem_append_left _ (List.mem_map.mpr ⟨route, member, rfl⟩),
        (needs_read_define_proof operand.fvList [x] _ z).mpr (.inr ⟨by simpa using other, needed⟩)⟩
    · obtain ⟨route, member, needed⟩ := term_needs_route_proof edge next z right inRight
      exact ⟨_, List.mem_append_right _ (List.mem_map.mpr ⟨route, member, rfl⟩),
        (needs_read_define_proof operand.fvList [y] _ z).mpr (.inr ⟨by simpa using other, needed⟩)⟩

/-- A register that a body needs is needed on one of its routes. -/
theorem body_needs_route_proof (edge next : K → List V) (z : V) :
    (source : Body V (Option K) F) → BodyNeeds edge next z source →
    ∃ route ∈ GlobalSSA.bodyRoutes edge source,
      z ∈ needs (route.accesses ++ [.read (route.target.elim [] next)])
  | .term tail, wanted => term_needs_route_proof edge next z tail wanted
  | .let1 x operand rest, wanted => by
    rcases wanted with here | ⟨other, later⟩
    · obtain ⟨first, member⟩ :=
        List.exists_mem_of_ne_nil _ (bodyRoutes_ne_nil_proof edge rest)
      exact ⟨_, List.mem_map.mpr ⟨first, member, rfl⟩,
        (needs_read_define_proof operand.fvList [x] _ z).mpr (.inl here)⟩
    · obtain ⟨route, member, needed⟩ := body_needs_route_proof edge next z rest later
      exact ⟨_, List.mem_map.mpr ⟨route, member, rfl⟩,
        (needs_read_define_proof operand.fvList [x] _ z).mpr (.inr ⟨by simpa using other, needed⟩)⟩
  | .let2 x y operand rest, wanted => by
    rcases wanted with here | ⟨otherX, otherY, later⟩
    · obtain ⟨first, member⟩ :=
        List.exists_mem_of_ne_nil _ (bodyRoutes_ne_nil_proof edge rest)
      exact ⟨_, List.mem_map.mpr ⟨first, member, rfl⟩,
        (needs_read_define_proof operand.fvList [x, y] _ z).mpr (.inl here)⟩
    · obtain ⟨route, member, needed⟩ := body_needs_route_proof edge next z rest later
      exact ⟨_, List.mem_map.mpr ⟨route, member, rfl⟩,
        (needs_read_define_proof operand.fvList [x, y] _ z).mpr
          (.inr ⟨by simp [otherX, otherY], needed⟩)⟩

variable [DecidableEq K]

/-- A route that passes a read. -/
theorem checkRoute_read_proof (certificate : GlobalSSA.Certificate V K) (avail names : List V)
    (target : Option K) (rest : List (GlobalSSA.Access V))
    (ok : GlobalSSA.checkRoute certificate avail ⟨target, .read names :: rest⟩ = true) :
    (∀ x ∈ names, x ∈ avail) ∧ GlobalSSA.checkRoute certificate avail ⟨target, rest⟩ = true := by
  simp only [GlobalSSA.checkRoute, GlobalSSA.Access.scan] at ok ⊢
  split at ok
  · rename_i all
    exact ⟨fun x member => by simpa using List.all_eq_true.mp all x member, ok⟩
  · simp at ok

/-- On a route that passes the check, what the route needs is available
at its start, when what each target is given is within its claim. -/
theorem needs_claimed_proof (certificate : GlobalSSA.Certificate V K) (next : K → List V)
    (within : ∀ target, ∀ z ∈ next target, z ∈ (certificate.lookup target).getD [])
    (target : Option K) : (accesses : List (GlobalSSA.Access V)) → (avail : List V) →
    GlobalSSA.checkRoute certificate avail ⟨target, accesses⟩ = true →
    ∀ z ∈ needs (accesses ++ [.read (target.elim [] next)]), z ∈ avail
  | [], avail, ok => by
    intro z member
    cases target with
    | none => simp [needs] at member
    | some key =>
      have claim := within key z (by simpa [needs] using member)
      cases found : certificate.lookup key with
      | none => simp [found] at claim
      | some required =>
        simp only [GlobalSSA.checkRoute, GlobalSSA.Access.scan, Option.any_some, Option.elim,
          found, List.all_eq_true] at ok
        rw [found] at claim
        simpa using ok z claim
  | .read names :: rest, avail, ok => by
    intro z member
    have split := checkRoute_read_proof certificate avail names target rest ok
    simp only [List.cons_append, needs, List.mem_append] at member
    rcases member with here | later
    · exact split.1 z here
    · exact needs_claimed_proof certificate next within target rest avail split.2 z later
  | .define names :: rest, avail, ok => by
    intro z member
    simp only [List.cons_append, needs, List.mem_filter] at member
    have reached := needs_claimed_proof certificate next within target rest (avail ++ names) ok z
      member.1
    exact (List.mem_append.mp reached).resolve_right (by simpa using member.2)

end Needs

/-! ## Structure of the normalized graph -/

section Structure

variable {V K : Type w} {F : Type v}

/-- The targets of a relabeled terminator. -/
theorem term_relabel_targets_proof (π : Option K → Option K) :
    (tail : Term V (Option K) F) → (tail.relabel π).targets = tail.targets.map π
  | .br _ _ => rfl
  | .case _ _ left _ right => by
    simp only [Term.relabel, Term.targets, List.map_append, term_relabel_targets_proof π left,
      term_relabel_targets_proof π right]

/-- The targets of a relabeled body. -/
theorem body_relabel_targets_proof (π : Option K → Option K) :
    (source : Body V (Option K) F) → (source.relabel π).targets = source.targets.map π
  | .term tail => term_relabel_targets_proof π tail
  | .let1 _ _ rest => body_relabel_targets_proof π rest
  | .let2 _ _ _ rest => body_relabel_targets_proof π rest

/-- Relabeling keeps the definitions of a terminator. -/
theorem term_relabel_definitions_proof (π : Option K → Option K) :
    (tail : Term V (Option K) F) →
    GlobalSSA.termDefinitions (tail.relabel π) = GlobalSSA.termDefinitions tail
  | .br _ _ => rfl
  | .case _ _ left _ right => by
    simp only [Term.relabel, GlobalSSA.termDefinitions, term_relabel_definitions_proof π left,
      term_relabel_definitions_proof π right]

/-- Relabeling keeps the definitions of a body. -/
theorem body_relabel_definitions_proof (π : Option K → Option K) :
    (source : Body V (Option K) F) →
    GlobalSSA.bodyDefinitions (source.relabel π) = GlobalSSA.bodyDefinitions source
  | .term tail => term_relabel_definitions_proof π tail
  | .let1 _ _ rest => by
    simp only [Body.relabel, GlobalSSA.bodyDefinitions, body_relabel_definitions_proof π rest]
  | .let2 _ _ _ rest => by
    simp only [Body.relabel, GlobalSSA.bodyDefinitions, body_relabel_definitions_proof π rest]

/-- Relabeling commutes with the renaming of the reads of a terminator. -/
theorem term_relabel_proof (read : V → Name V K) (π : Option K → Option K) :
    (tail : Term V (Option K) F) → (term read tail).relabel π = term read (tail.relabel π)
  | .br _ _ => rfl
  | .case _ _ left _ right => by
    simp only [term, Term.relabel, term_relabel_proof read π left, term_relabel_proof read π right]

/-- Relabeling commutes with the renaming of the reads of a body. -/
theorem body_relabel_proof (read : V → Name V K) (π : Option K → Option K) :
    (source : Body V (Option K) F) → (body read source).relabel π = body read (source.relabel π)
  | .term tail => by simp only [body, Body.relabel, term_relabel_proof]
  | .let1 _ _ rest => by simp only [body, Body.relabel, body_relabel_proof read π rest]
  | .let2 _ _ _ rest => by simp only [body, Body.relabel, body_relabel_proof read π rest]

/-- The definitions of a normalized terminator are the original ones. -/
theorem term_definitions_proof (read : V → Name V K) : (tail : Term V (Option K) F) →
    GlobalSSA.termDefinitions (term read tail) = (GlobalSSA.termDefinitions tail).map Sum.inl
  | .br _ _ => rfl
  | .case _ _ left _ right => by
    simp only [term, GlobalSSA.termDefinitions, List.map_append, List.map_cons,
      term_definitions_proof read left, term_definitions_proof read right]

/-- The definitions of a normalized body are the original ones. -/
theorem body_definitions_proof (read : V → Name V K) : (source : Body V (Option K) F) →
    GlobalSSA.bodyDefinitions (body read source) = (GlobalSSA.bodyDefinitions source).map Sum.inl
  | .term tail => term_definitions_proof read tail
  | .let1 _ _ rest => by
    simp only [body, GlobalSSA.bodyDefinitions, List.map_cons, body_definitions_proof read rest]
  | .let2 _ _ _ rest => by
    simp only [body, GlobalSSA.bodyDefinitions, List.map_cons, body_definitions_proof read rest]

/-- A list of names has no duplicate when its two sides have none. -/
theorem nodup_sides_proof {A B : Type*} : (names : List (A ⊕ B)) →
    (names.filterMap Sum.getLeft?).Nodup → (names.filterMap Sum.getRight?).Nodup → names.Nodup
  | [], _, _ => List.nodup_nil
  | .inl a :: rest, left, right => by
    simp only [List.filterMap_cons, Sum.getLeft?_inl, Sum.getRight?_inl, List.nodup_cons] at left right
    exact List.nodup_cons.mpr ⟨fun member => left.1 (List.mem_filterMap.mpr ⟨.inl a, member, rfl⟩),
      nodup_sides_proof rest left.2 right⟩
  | .inr b :: rest, left, right => by
    simp only [List.filterMap_cons, Sum.getLeft?_inr, Sum.getRight?_inr, List.nodup_cons] at left right
    exact List.nodup_cons.mpr ⟨fun member => right.1 (List.mem_filterMap.mpr ⟨.inr b, member, rfl⟩),
      nodup_sides_proof rest left right.2⟩

theorem left_inl_proof {A B : Type*} : (items : List A) →
    (items.map (Sum.inl : A → A ⊕ B)).filterMap Sum.getLeft? = items
  | [] => rfl
  | first :: rest => by
    simp only [List.map_cons, List.filterMap_cons, Sum.getLeft?_inl, left_inl_proof rest]

theorem right_inl_proof {A B : Type*} : (items : List A) →
    (items.map (Sum.inl : A → A ⊕ B)).filterMap Sum.getRight? = []
  | [] => rfl
  | first :: rest => by
    simp only [List.map_cons, List.filterMap_cons, Sum.getRight?_inl, right_inl_proof rest]

theorem left_inr_proof {A B C : Type*} (f : C → B) : (items : List C) →
    (items.map (fun c => (Sum.inr (f c) : A ⊕ B))).filterMap Sum.getLeft? = []
  | [] => rfl
  | first :: rest => by
    simp only [List.map_cons, List.filterMap_cons, Sum.getLeft?_inr, left_inr_proof f rest]

theorem right_inr_proof {A B C : Type*} (f : C → B) : (items : List C) →
    (items.map (fun c => (Sum.inr (f c) : A ⊕ B))).filterMap Sum.getRight? = items.map f
  | [] => rfl
  | first :: rest => by
    simp only [List.map_cons, List.filterMap_cons, Sum.getRight?_inr, right_inr_proof f rest]

variable [DecidableEq K]

/-- A member of an association list is found at its key. -/
theorem lookup_isSome_proof' {B : Type*} : (entries : List (K × B)) → {key : K} → {value : B} →
    (key, value) ∈ entries → (entries.lookup key).isSome = true
  | [], _, _, member => by cases member
  | (k, b) :: rest, key, value, member => by
    simp only [List.lookup]
    split
    · rfl
    · rename_i other
      rcases List.mem_cons.mp member with head | tail
      · cases head
        simp at other
      · exact lookup_isSome_proof' rest tail

/-- A member of an association list with distinct keys is the value found
at its key. -/
theorem lookup_member_proof {B : Type*} : (entries : List (K × B)) →
    (entries.map Prod.fst).Nodup → {key : K} → {value : B} → (key, value) ∈ entries →
    entries.lookup key = some value
  | [], _, _, _, member => by cases member
  | (k, b) :: rest, distinct, key, value, member => by
    simp only [List.map, List.nodup_cons] at distinct
    simp only [List.lookup]
    rcases List.mem_cons.mp member with head | tail
    · cases head
      simp
    · have other : key ≠ k := fun eq =>
        distinct.1 (eq ▸ List.mem_map.mpr ⟨(key, value), tail, rfl⟩)
      have differs : (key == k) = false := by simp [other]
      rw [differs]
      exact lookup_member_proof rest distinct.2 tail

/-- An internal label is a target after the exits are collapsed exactly
when it is a target. -/
theorem scope_target_proof (exits : List (Option K)) (key : K) (internal : some key ∉ exits)
    (targets : List (Option K)) :
    some key ∈ targets.map (OrderedExits.scopeLabel exits) ↔ some key ∈ targets := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨target, member, eq⟩
    by_cases declared : target ∈ exits
    · simp [OrderedExits.scopeLabel, declared] at eq
    · simp only [OrderedExits.scopeLabel, List.contains_iff_mem, declared, ite_false] at eq
      exact eq ▸ member
  · intro member
    exact ⟨some key, member, by simp [OrderedExits.scopeLabel, internal]⟩

/-- The predecessors of an internal label are kept when the exits are
collapsed. -/
theorem predecessors_forScope_proof (graph : Graph V K F) (exits : List (Option K)) (key : K)
    (internal : some key ∉ exits) :
    (OrderedExits.forScope graph exits).predecessors key = graph.predecessors key := by
  have entry : some key ∈ (OrderedExits.forScope graph exits).entry.targets ↔
      some key ∈ graph.entry.targets := by
    show some key ∈ (graph.entry.relabel (OrderedExits.scopeLabel exits)).targets ↔ _
    rw [body_relabel_targets_proof]
    exact scope_target_proof exits key internal _
  have blocks : (OrderedExits.forScope graph exits).blocks.filterMap
        (fun item => if some key ∈ item.2.body.targets then some (some item.1) else none) =
      graph.blocks.filterMap
        (fun item => if some key ∈ item.2.body.targets then some (some item.1) else none) := by
    show (graph.blocks.map _).filterMap _ = _
    rw [List.filterMap_map]
    apply List.filterMap_congr
    intro item _
    simp only [Function.comp, body_relabel_targets_proof, scope_target_proof exits key internal]
  unfold Graph.predecessors
  exact congrArg₂ (· ++ ·) (by simp only [entry]) blocks

variable [DecidableEq V]

/-- The predecessors of a label are kept by the normalization. -/
theorem predecessors_forward_proof (graph : Graph V K F) (table : Table V K) (key : K) :
    (forward graph table).predecessors key = graph.predecessors key := by
  have blocks : (forward graph table).blocks.filterMap
        (fun item => if some key ∈ item.2.body.targets then some (some item.1) else none) =
      graph.blocks.filterMap
        (fun item => if some key ∈ item.2.body.targets then some (some item.1) else none) := by
    show (graph.blocks.map _).filterMap _ = _
    rw [List.filterMap_map]
    apply List.filterMap_congr
    intro item _
    simp only [Function.comp, block, body_targets_proof]
  unfold Graph.predecessors
  exact congrArg₂ (· ++ ·)
    (by rw [show (forward graph table).entry = body Sum.inl graph.entry from rfl,
      body_targets_proof]) blocks

/-- Collapsing the exits commutes with the normalization, when no declared
exit is a block. -/
theorem forScope_forward_proof (graph : Graph V K F) (table : Table V K) (exits : List (Option K))
    (partition : OrderedExits.checkExits graph exits = true) :
    OrderedExits.forScope (forward graph table) exits =
      forward (OrderedExits.forScope graph exits) table := by
  show (⟨(body Sum.inl graph.entry).relabel (OrderedExits.scopeLabel exits),
      (graph.blocks.map _).map _⟩ : Graph (Name V K) K F) =
    ⟨body Sum.inl (graph.entry.relabel (OrderedExits.scopeLabel exits)), (graph.blocks.map _).map _⟩
  rw [body_relabel_proof, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro item member
  have internal : some item.1 ∉ exits :=
    OrderedExits.header_not_exit graph exits partition (lookup_isSome_proof' graph.blocks member)
  simp only [Function.comp, block, body_relabel_proof,
    predecessors_forScope_proof graph exits item.1 internal]

end Structure

/-! ## The normalized graph is normalized, with single definitions -/

section Normal

variable {V K : Type w} {F : Type v} [DecidableEq V] [DecidableEq K]

omit [DecidableEq V] [DecidableEq K] in
/-- The copies of distinct blocks are distinct. -/
theorem copies_nodup_proof {B : Type*} (received : K → List V)
    (distinct : ∀ key, (received key).Nodup) : (blocks : List (K × B)) →
    (blocks.map Prod.fst).Nodup →
    (blocks.flatMap fun item => (received item.1).map fun r => (r, item.1)).Nodup
  | [], _ => List.nodup_nil
  | first :: rest, labels => by
    simp only [List.map_cons, List.nodup_cons] at labels
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨(distinct first.1).map fun a b eq => (Prod.mk.inj eq).1,
      copies_nodup_proof received distinct rest labels.2, fun a inFirst b inRest same => ?_⟩
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp inFirst
    obtain ⟨other, member, inOther⟩ := List.mem_flatMap.mp inRest
    obtain ⟨r', _, eq⟩ := List.mem_map.mp inOther
    have key : other.1 = first.1 := (Prod.mk.inj (eq.trans same.symm)).2
    exact labels.1 (key ▸ List.mem_map.mpr ⟨other, member, rfl⟩)

/-- The definitions of a normalized block: the original φ destinations,
the copies, and the original definitions of the body. -/
theorem block_definitions_proof (table : Table V K) (graph : Graph V K F) (key : K)
    (source : Block V K F) :
    (block table graph key source).rows.map Row.dst ++
        GlobalSSA.bodyDefinitions (block table graph key source).body =
      (source.rows.map Row.dst).map Sum.inl ++
        (table.received key).map (fun r => (Sum.inr (r, key) : Name V K)) ++
        (GlobalSSA.bodyDefinitions source.body).map Sum.inl := by
  simp only [block, List.map_append, List.map_map, body_definitions_proof]
  rfl

/-- The definitions of the normalized graph are distinct when those of the
graph are, the labels are distinct and no block receives a register
twice. -/
theorem definitions_forward_proof (graph : Graph V K F) (table : Table V K) (inputs : List V)
    (unique : (GlobalSSA.definitions graph inputs).Nodup)
    (labels : (graph.blocks.map Prod.fst).Nodup)
    (distinct : ∀ key, (table.received key).Nodup) :
    (GlobalSSA.definitions (forward graph table) (inputs.map Sum.inl)).Nodup := by
  have shape : GlobalSSA.definitions (forward graph table) (inputs.map Sum.inl) =
      inputs.map Sum.inl ++ (GlobalSSA.bodyDefinitions graph.entry).map Sum.inl ++
        graph.blocks.flatMap fun (item : K × Block V K F) =>
          (item.2.rows.map Row.dst).map Sum.inl ++
            (table.received item.1).map (fun r => (Sum.inr (r, item.1) : Name V K)) ++
            (GlobalSSA.bodyDefinitions item.2.body).map Sum.inl := by
    show inputs.map Sum.inl ++ GlobalSSA.bodyDefinitions (body Sum.inl graph.entry) ++
      (graph.blocks.map _).flatMap _ = _
    rw [body_definitions_proof, List.flatMap_map]
    congr 1
    apply List.flatMap_congr
    intro item _
    exact block_definitions_proof table graph item.1 item.2
  rw [shape]
  apply nodup_sides_proof
  · simp only [List.filterMap_append, List.filterMap_flatMap, left_inl_proof, left_inr_proof,
      List.append_nil]
    exact unique
  · simp only [List.filterMap_append, List.filterMap_flatMap, right_inl_proof, right_inr_proof,
      List.append_nil, List.nil_append]
    exact copies_nodup_proof table.received distinct graph.blocks labels

/-- The labels of the normalized graph. -/
theorem forward_labels_proof (graph : Graph V K F) (table : Table V K) :
    (forward graph table).blocks.map Prod.fst = graph.blocks.map Prod.fst := by
  show (graph.blocks.map _).map Prod.fst = _
  rw [List.map_map]
  rfl

/-- The normalized graph passes the normalization check of φ graphs when
the graph does and no block receives a register twice. -/
theorem check_forward_proof (graph : Graph V K F) (table : Table V K) (ok : graph.check = true)
    (distinct : ∀ key, (table.received key).Nodup) : (forward graph table).check = true := by
  simp only [Graph.check, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at ok ⊢
  obtain ⟨⟨labels, entryTargets⟩, blocks⟩ := ok
  rw [forward_labels_proof]
  refine ⟨⟨labels, ?_⟩, ?_⟩
  · rw [show (forward graph table).entry = body Sum.inl graph.entry from rfl, body_targets_proof]
    exact entryTargets
  · intro item member
    obtain ⟨source, original, rfl⟩ := List.mem_map.mp member
    have here := blocks source original
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show _ ∧ _
      rw [show (block table graph source.1 source.2).body =
        body (reader table (some source.1)) source.2.body from rfl, body_targets_proof]
      exact here.1.1
    · show ((source.2.rows.map (row table) ++
        (table.received source.1).map (copyRow table (graph.predecessors source.1) source.1)).map
          Row.dst).Nodup
      rw [List.map_append, List.nodup_append, List.map_map, List.map_map]
      refine ⟨?_, (distinct source.1).map fun a b eq => (Prod.mk.inj (Sum.inr.inj eq)).1,
        fun a inRows b inCopies same => ?_⟩
      · have := here.1.2.map (f := (Sum.inl : V → Name V K)) Sum.inl_injective
        rw [List.map_map] at this
        exact this
      · obtain ⟨r, _, rfl⟩ := List.mem_map.mp inRows
        obtain ⟨c, _, eq⟩ := List.mem_map.mp inCopies
        cases eq.trans same.symm
    · intro r listed
      rw [predecessors_forward_proof]
      rcases List.mem_append.mp listed with inRows | inCopies
      · obtain ⟨original, rowMember, rfl⟩ := List.mem_map.mp inRows
        simp only [row, List.map_map]
        exact (here.2 original rowMember) ▸ rfl
      · obtain ⟨register, _, rfl⟩ := List.mem_map.mp inCopies
        simp only [copyRow, List.map_map]
        exact List.map_id _

end Normal

/-! ## Routes of the normalized graph -/

section Simulation

variable {V K : Type w} {F : Type v} [DecidableEq V] [DecidableEq K]

omit [DecidableEq V] in
/-- A route check passes a read of available registers. -/
theorem checkRoute_cons_read_proof {W : Type w} [DecidableEq W]
    (certificate : GlobalSSA.Certificate W K) (avail names : List W) (target : Option K)
    (rest : List (GlobalSSA.Access W)) (have_ : ∀ x ∈ names, x ∈ avail) :
    GlobalSSA.checkRoute certificate avail ⟨target, .read names :: rest⟩ =
      GlobalSSA.checkRoute certificate avail ⟨target, rest⟩ := by
  have all : names.all (fun name => avail.contains name) = true :=
    List.all_eq_true.mpr fun x member => by simpa using have_ x member
  simp only [GlobalSSA.checkRoute, GlobalSSA.Access.scan, all, ↓reduceIte]

omit [DecidableEq K] in
/-- The operand of a copy row reads the register as the predecessor reads
it, if it reads anything. -/
theorem copy_operand_proof [DecidableEq K] (table : Table V K) (key : K) (register : V)
    (pred : Option K) : (predecessors : List (Option K)) →
    ∀ w ∈ ((copyRow table predecessors key register).operand pred).fvList,
      w = reader table pred register
  | [], w, member => by simp [Row.operand, copyRow, Val.fvList] at member
  | first :: rest, w, member => by
    simp only [Row.operand, copyRow, List.map_cons, List.lookup] at member
    split at member
    · rename_i same
      rw [eq_of_beq same]
      simpa [Val.fvList] using member
    · exact copy_operand_proof table key register pred rest w member

/-- A φ operand on an edge of the normalized graph is an original operand
of the edge, or a register that the target receives, as the predecessor
reads it. -/
theorem edge_forward_proof (graph : Graph V K F) (table : Table V K) (pred : Option K)
    (target : K) : ∀ w ∈ GlobalSSA.edgeReads (forward graph table) pred target,
    ∃ z, (z ∈ GlobalSSA.edgeReads graph pred target ∨ z ∈ table.received target) ∧
      w = reader table pred z := by
  intro w member
  simp only [GlobalSSA.edgeReads, lookup_forward_proof] at member ⊢
  cases found : graph.blocks.lookup target with
  | none =>
    rw [found] at member
    simp at member
  | some source =>
    rw [found] at member
    simp only [Option.map_some, Option.elim, block, arguments, List.map_append, List.map_map,
      List.flatMap_append, List.mem_append, List.mem_flatMap, List.mem_map] at member ⊢
    rcases member with ⟨value, ⟨r, listed, rfl⟩, read⟩ | ⟨value, ⟨r, listed, rfl⟩, read⟩
    · simp only [Function.comp, operand_row_proof, rename_fv_proof, List.mem_map] at read
      obtain ⟨z, inOperand, rfl⟩ := read
      exact ⟨z, .inl ⟨_, ⟨r, listed, rfl⟩, inOperand⟩, rfl⟩
    · exact ⟨r, .inr listed, copy_operand_proof table target r pred _ w read⟩

/-- The routes of a normalized terminator pass the check, when what the
terminator needs is available as it is read. -/
theorem sim_term_proof (edge next : K → List V) (edge' : K → List (Name V K))
    (read : V → Name V K) (certificate : GlobalSSA.Certificate (Name V K) K)
    (base : List (Name V K))
    (edges : ∀ t, ∀ w ∈ edge' t, ∃ z, (z ∈ edge t ∨ z ∈ next t) ∧ w = read z) :
    (tail : Term V (Option K) F) → (avail : List (Name V K)) → (∀ w ∈ base, w ∈ avail) →
    (∀ z, read z = .inl z ∨ read z ∈ avail) →
    (∀ z, TermNeeds edge next z tail → read z ∈ avail) →
    (∀ t, some t ∈ tail.targets → ∃ req, certificate.lookup t = some req ∧ ∀ w ∈ req, w ∈ base) →
    ∀ route ∈ GlobalSSA.termRoutes edge' (term read tail),
      GlobalSSA.checkRoute certificate avail route = true
  | .br none value, avail, _, _, needed, _ => by
    intro route member
    simp only [term, GlobalSSA.termRoutes, List.mem_singleton] at member
    subst member
    have reads : ∀ x ∈ (value.rename read).fvList, x ∈ avail := fun x listed => by
      rw [rename_fv_proof] at listed
      obtain ⟨z, inValue, rfl⟩ := List.mem_map.mp listed
      exact needed z inValue
    rw [checkRoute_cons_read_proof _ _ _ _ _ reads]
    rfl
  | .br (some target) value, avail, grows, _, needed, claims => by
    intro route member
    simp only [term, GlobalSSA.termRoutes, List.mem_singleton] at member
    subst member
    have reads : ∀ x ∈ edge' target, x ∈ avail := fun x listed => by
      obtain ⟨z, wanted, rfl⟩ := edges target x listed
      exact needed z wanted
    rw [checkRoute_cons_read_proof _ _ _ _ _ reads]
    obtain ⟨req, found, within⟩ := claims target (by simp [Term.targets])
    simp only [GlobalSSA.checkRoute, GlobalSSA.Access.scan, Option.any_some, Option.elim, found,
      List.all_eq_true]
    intro w listed
    simpa using grows w (within w listed)
  | .case operand x left y right, avail, grows, local_, needed, claims => by
    intro route member
    simp only [term, GlobalSSA.termRoutes, List.mem_append, List.mem_map] at member
    have reads : ∀ w ∈ (operand.rename read).fvList, w ∈ avail := fun w listed => by
      rw [rename_op_fv_proof] at listed
      obtain ⟨z, inOperand, rfl⟩ := List.mem_map.mp listed
      exact needed z (.inl inOperand)
    rcases member with ⟨inner, innerMember, rfl⟩ | ⟨inner, innerMember, rfl⟩
    · show GlobalSSA.checkRoute certificate avail
        ⟨inner.target, .read _ :: .define [.inl x] :: inner.accesses⟩ = true
      rw [checkRoute_cons_read_proof _ _ _ _ _ reads]
      exact sim_term_proof edge next edge' read certificate base edges left (avail ++ [.inl x])
        (fun w listed => List.mem_append_left _ (grows w listed))
        (fun z => (local_ z).imp id (List.mem_append_left _))
        (fun z wanted => by
          by_cases same : z = x
          · subst same
            rcases local_ z with own | copy
            · rw [own]
              simp
            · exact List.mem_append_left _ copy
          · exact List.mem_append_left _ (needed z (.inr (.inl ⟨same, wanted⟩))))
        (fun t listed => claims t (by simp [Term.targets, listed])) inner innerMember
    · show GlobalSSA.checkRoute certificate avail
        ⟨inner.target, .read _ :: .define [.inl y] :: inner.accesses⟩ = true
      rw [checkRoute_cons_read_proof _ _ _ _ _ reads]
      exact sim_term_proof edge next edge' read certificate base edges right (avail ++ [.inl y])
        (fun w listed => List.mem_append_left _ (grows w listed))
        (fun z => (local_ z).imp id (List.mem_append_left _))
        (fun z wanted => by
          by_cases same : z = y
          · subst same
            rcases local_ z with own | copy
            · rw [own]
              simp
            · exact List.mem_append_left _ copy
          · exact List.mem_append_left _ (needed z (.inr (.inr ⟨same, wanted⟩))))
        (fun t listed => claims t (by simp [Term.targets, listed])) inner innerMember

/-- The routes of a normalized body pass the check, when what the body
needs is available as it is read. -/
theorem sim_body_proof (edge next : K → List V) (edge' : K → List (Name V K))
    (read : V → Name V K) (certificate : GlobalSSA.Certificate (Name V K) K)
    (base : List (Name V K))
    (edges : ∀ t, ∀ w ∈ edge' t, ∃ z, (z ∈ edge t ∨ z ∈ next t) ∧ w = read z) :
    (source : Body V (Option K) F) → (avail : List (Name V K)) → (∀ w ∈ base, w ∈ avail) →
    (∀ z, read z = .inl z ∨ read z ∈ avail) →
    (∀ z, BodyNeeds edge next z source → read z ∈ avail) →
    (∀ t, some t ∈ source.targets →
      ∃ req, certificate.lookup t = some req ∧ ∀ w ∈ req, w ∈ base) →
    ∀ route ∈ GlobalSSA.bodyRoutes edge' (body read source),
      GlobalSSA.checkRoute certificate avail route = true
  | .term tail, avail, grows, local_, needed, claims =>
    sim_term_proof edge next edge' read certificate base edges tail avail grows local_ needed claims
  | .let1 x operand rest, avail, grows, local_, needed, claims => by
    intro route member
    simp only [body, GlobalSSA.bodyRoutes, List.mem_map] at member
    obtain ⟨inner, innerMember, rfl⟩ := member
    have reads : ∀ w ∈ (operand.rename read).fvList, w ∈ avail := fun w listed => by
      rw [rename_op_fv_proof] at listed
      obtain ⟨z, inOperand, rfl⟩ := List.mem_map.mp listed
      exact needed z (.inl inOperand)
    show GlobalSSA.checkRoute certificate avail
      ⟨inner.target, .read _ :: .define [.inl x] :: inner.accesses⟩ = true
    rw [checkRoute_cons_read_proof _ _ _ _ _ reads]
    exact sim_body_proof edge next edge' read certificate base edges rest (avail ++ [.inl x])
      (fun w listed => List.mem_append_left _ (grows w listed))
      (fun z => (local_ z).imp id (List.mem_append_left _))
      (fun z wanted => by
        by_cases same : z = x
        · subst same
          rcases local_ z with own | copy
          · rw [own]
            simp
          · exact List.mem_append_left _ copy
        · exact List.mem_append_left _ (needed z (.inr ⟨same, wanted⟩)))
      claims inner innerMember
  | .let2 x y operand rest, avail, grows, local_, needed, claims => by
    intro route member
    simp only [body, GlobalSSA.bodyRoutes, List.mem_map] at member
    obtain ⟨inner, innerMember, rfl⟩ := member
    have reads : ∀ w ∈ (operand.rename read).fvList, w ∈ avail := fun w listed => by
      rw [rename_op_fv_proof] at listed
      obtain ⟨z, inOperand, rfl⟩ := List.mem_map.mp listed
      exact needed z (.inl inOperand)
    show GlobalSSA.checkRoute certificate avail
      ⟨inner.target, .read _ :: .define [.inl x, .inl y] :: inner.accesses⟩ = true
    rw [checkRoute_cons_read_proof _ _ _ _ _ reads]
    exact sim_body_proof edge next edge' read certificate base edges rest
      (avail ++ [.inl x, .inl y])
      (fun w listed => List.mem_append_left _ (grows w listed))
      (fun z => (local_ z).imp id (List.mem_append_left _))
      (fun z wanted => by
        by_cases sameX : z = x
        · subst sameX
          rcases local_ z with own | copy
          · rw [own]
            simp
          · exact List.mem_append_left _ copy
        · by_cases sameY : z = y
          · subst sameY
            rcases local_ z with own | copy
            · rw [own]
              simp
            · exact List.mem_append_left _ copy
          · exact List.mem_append_left _ (needed z (.inr ⟨sameX, sameY, wanted⟩)))
      claims inner innerMember

end Simulation

/-! ## The scope check of the normalized graph -/

section Core

variable {V K : Type w} {F : Type v} [DecidableEq V] [DecidableEq K]

/-- The normalized graph passes the scope check with every block arriving
with the inputs only, when the graph passes the scope check with some
claims, no block receives a register twice, the entry needs inputs only,
and each block needs only inputs, its φ destinations and what it
receives. What a route needs counts what its target receives. -/
theorem check_closed_proof (graph : Graph V K F) (table : Table V K) (inputs : List V)
    (certificate : GlobalSSA.Certificate V K)
    (ok : GlobalSSA.check graph inputs certificate = true)
    (distinct : ∀ key, (table.received key).Nodup)
    (entryNeeds : ∀ route ∈ GlobalSSA.bodyRoutes (GlobalSSA.edgeReads graph none) graph.entry,
      ∀ z ∈ needs (route.accesses ++ [.read (route.target.elim [] table.received)]), z ∈ inputs)
    (blockNeeds : ∀ item ∈ graph.blocks,
      ∀ route ∈ GlobalSSA.bodyRoutes (GlobalSSA.edgeReads graph (some item.1)) item.2.body,
      ∀ z ∈ needs (route.accesses ++ [.read (route.target.elim [] table.received)]),
        z ∈ inputs ∨ z ∈ item.2.rows.map Row.dst ∨ z ∈ table.received item.1) :
    GlobalSSA.check (forward graph table) (inputs.map Sum.inl)
      (graph.blocks.map fun item => (item.1, inputs.map Sum.inl)) = true := by
  simp only [GlobalSSA.check, Bool.and_eq_true, decide_eq_true_eq] at ok ⊢
  obtain ⟨normalized, unique, _, _, _⟩ := ok
  have shape := normalized
  simp only [Graph.check, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at shape
  obtain ⟨⟨labels, entryTargets⟩, blockShape⟩ := shape
  -- a target that is a label has the claim of the inputs
  have claim : ∀ t, t ∈ graph.blocks.map Prod.fst →
      ∃ req, (graph.blocks.map fun item => (item.1, inputs.map (Sum.inl : V → Name V K))).lookup t =
        some req ∧ ∀ w ∈ req, w ∈ inputs.map (Sum.inl : V → Name V K) := by
    intro t listed
    obtain ⟨item, member, rfl⟩ := List.mem_map.mp listed
    have keyed := lookup_keyed_proof (fun _ (_ : Block V K F) => inputs.map (Sum.inl : V → Name V K))
      graph.blocks item.1
    have present := lookup_isSome_proof' graph.blocks (key := item.1) (value := item.2) member
    cases found : graph.blocks.lookup item.1 with
    | none => simp [found] at present
    | some _ =>
      rw [found] at keyed
      exact ⟨_, keyed, fun _ listed => listed⟩
  refine ⟨check_forward_proof graph table normalized distinct,
    definitions_forward_proof graph table inputs unique labels distinct, ?_, ?_, ?_⟩
  · rw [List.map_map]
    exact labels
  · refine List.all_eq_true.mpr fun route member => ?_
    exact sim_body_proof (GlobalSSA.edgeReads graph none) table.received
      (GlobalSSA.edgeReads (forward graph table) none) Sum.inl _ (inputs.map Sum.inl)
      (edge_forward_proof graph table none) graph.entry (inputs.map Sum.inl)
      (fun _ listed => listed) (fun _ => .inl rfl)
      (fun z wanted => by
        obtain ⟨route, routeMember, needed⟩ := body_needs_route_proof _ _ z graph.entry wanted
        exact List.mem_map.mpr ⟨z, entryNeeds route routeMember z needed, rfl⟩)
      (fun t listed => claim t (by
        simpa using entryTargets.2 t (List.mem_filterMap.mpr ⟨some t, listed, rfl⟩)))
      route member
  · refine List.all_eq_true.mpr fun entry entryMember => ?_
    obtain ⟨item, member, rfl⟩ := List.mem_map.mp entryMember
    have found : (forward graph table).blocks.lookup item.1 =
        some (block table graph item.1 item.2) := by
      rw [lookup_forward_proof, lookup_member_proof graph.blocks labels (value := item.2) member]
      rfl
    have copy : ∀ z ∈ table.received item.1, (Sum.inr (z, item.1) : Name V K) ∈
        inputs.map Sum.inl ++ (block table graph item.1 item.2).rows.map Row.dst := fun z received =>
      List.mem_append_right _ (List.mem_map.mpr ⟨copyRow table (graph.predecessors item.1) item.1 z,
        List.mem_append_right _ (List.mem_map.mpr ⟨z, received, rfl⟩), rfl⟩)
    simp only [Bool.and_eq_true, found, Option.isSome_some, true_and, GlobalSSA.routes,
      Option.elim, List.all_eq_true, List.mem_map]
    rintro route ⟨inner, innerMember, rfl⟩
    exact sim_body_proof (GlobalSSA.edgeReads graph (some item.1)) table.received
      (GlobalSSA.edgeReads (forward graph table) (some item.1)) (reader table (some item.1)) _
      (inputs.map Sum.inl) (edge_forward_proof graph table (some item.1)) item.2.body
      (inputs.map Sum.inl ++ (block table graph item.1 item.2).rows.map Row.dst)
      (fun _ listed => List.mem_append_left _ listed)
      (fun z => by
        by_cases received : z ∈ table.received item.1
        · exact .inr (by simpa [reader, received] using copy z received)
        · exact .inl (by simp [reader, received]))
      (fun z wanted => by
        obtain ⟨route, routeMember, needed⟩ := body_needs_route_proof _ _ z item.2.body wanted
        by_cases received : z ∈ table.received item.1
        · simpa [reader, received] using copy z received
        · have own : reader table (some item.1) z = .inl z := by simp [reader, received]
          rw [own]
          rcases blockNeeds item member route routeMember z needed with input | row | given
          · exact List.mem_append_left _ (List.mem_map.mpr ⟨z, input, rfl⟩)
          · obtain ⟨r, listed, rfl⟩ := List.mem_map.mp row
            exact List.mem_append_right _ (List.mem_map.mpr ⟨Forward.row table r,
              List.mem_append_left _ (List.mem_map.mpr ⟨r, listed, rfl⟩), rfl⟩)
          · exact absurd given received)
      (fun t listed => claim t (by
        simpa using (blockShape item member).1.1.2 t (List.mem_filterMap.mpr ⟨some t, listed, rfl⟩)))
      inner innerMember

end Core

/-! ## The demand and the inferred table -/

section Demand

variable {V K : Type w} {F : Type v} [DecidableEq V] [DecidableEq K]

/-- A label that is not a block has no demand. -/
theorem demand_absent_proof (graph routed : Graph V K F) (inputs : List V) (key : K)
    (absent : graph.blocks.lookup key = none) :
    ∀ rounds, demand graph routed inputs rounds key = []
  | 0 => rfl
  | rounds + 1 => by simp [demand, demandStep, absent]

/-- What the inferred table gives a block is its demand after one more
round. -/
theorem received_infer_eq_proof (graph : Graph V K F) (exits : List (Option K)) (inputs : List V)
    (key : K) : (infer graph exits inputs).received key =
      demand graph (OrderedExits.forScope graph exits) inputs (graph.blocks.length + 1) key := by
  have keyed : (infer graph exits inputs).lookup key =
      (graph.blocks.lookup key).map (demandOf (OrderedExits.forScope graph exits) inputs
        (demand graph (OrderedExits.forScope graph exits) inputs graph.blocks.length) key) :=
    lookup_keyed_proof (fun k (source : Block V K F) =>
      demandOf (OrderedExits.forScope graph exits) inputs
        (demand graph (OrderedExits.forScope graph exits) inputs graph.blocks.length) k source)
      graph.blocks key
  simp only [Table.received, keyed, demand, demandStep]
  cases graph.blocks.lookup key <;> rfl

/-- The demand of a block depends on the demand of the targets of its
routes only. -/
theorem demandOf_congr_proof (routed : Graph V K F) (inputs : List V) (next next' : K → List V)
    (key : K) (source : Block V K F)
    (same : ∀ route ∈ GlobalSSA.routes routed (some key), ∀ t, route.target = some t →
      next t = next' t) :
    demandOf routed inputs next key source = demandOf routed inputs next' key source := by
  have inner : ((GlobalSSA.routes routed (some key)).flatMap fun route =>
        needs (route.accesses ++ [.read (route.target.elim [] next)])) =
      (GlobalSSA.routes routed (some key)).flatMap fun route =>
        needs (route.accesses ++ [.read (route.target.elim [] next')]) := by
    apply List.flatMap_congr
    intro route member
    cases target : route.target with
    | none => rfl
    | some t => simp only [Option.elim, same route member t target]
  simp only [demandOf, inner]

omit [DecidableEq V] [DecidableEq K] in
/-- The target of a route of a terminator is one of its targets. -/
theorem term_route_target_proof {W : Type w} (edge : K → List W) :
    (tail : Term W (Option K) F) → ∀ route ∈ GlobalSSA.termRoutes edge tail,
    route.target ∈ tail.targets
  | .br none _, route, member => by
    simp only [GlobalSSA.termRoutes, List.mem_singleton] at member
    subst member
    simp [Term.targets]
  | .br (some _) _, route, member => by
    simp only [GlobalSSA.termRoutes, List.mem_singleton] at member
    subst member
    simp [Term.targets]
  | .case _ _ left _ right, route, member => by
    simp only [GlobalSSA.termRoutes, List.mem_append, List.mem_map] at member
    rcases member with ⟨inner, innerMember, rfl⟩ | ⟨inner, innerMember, rfl⟩
    · exact List.mem_append_left _ (term_route_target_proof edge left inner innerMember)
    · exact List.mem_append_right _ (term_route_target_proof edge right inner innerMember)

omit [DecidableEq V] [DecidableEq K] in
/-- The target of a route of a body is one of its targets. -/
theorem body_route_target_proof {W : Type w} (edge : K → List W) :
    (source : Body W (Option K) F) → ∀ route ∈ GlobalSSA.bodyRoutes edge source,
    route.target ∈ source.targets
  | .term tail, route, member => term_route_target_proof edge tail route member
  | .let1 _ _ rest, route, member => by
    simp only [GlobalSSA.bodyRoutes, List.mem_map] at member
    obtain ⟨inner, innerMember, rfl⟩ := member
    exact body_route_target_proof edge rest inner innerMember
  | .let2 _ _ _ rest, route, member => by
    simp only [GlobalSSA.bodyRoutes, List.mem_map] at member
    obtain ⟨inner, innerMember, rfl⟩ := member
    exact body_route_target_proof edge rest inner innerMember

omit [DecidableEq V] in
/-- The block of a label after the exits are collapsed. -/
theorem lookup_forScope_proof (graph : Graph V K F) (exits : List (Option K)) (key : K) :
    (OrderedExits.forScope graph exits).blocks.lookup key =
      (graph.blocks.lookup key).map fun source =>
        ⟨source.rows, source.body.relabel (OrderedExits.scopeLabel exits)⟩ :=
  lookup_keyed_proof (fun _ (source : Block V K F) =>
    (⟨source.rows, source.body.relabel (OrderedExits.scopeLabel exits)⟩ : Block V K F))
    graph.blocks key

/-- Under a rank, the demand of a block stops changing after as many
rounds as its rank. -/
theorem demand_stable_proof (graph : Graph V K F) (exits : List (Option K)) (inputs : List V)
    (rank : K → Nat) (ok : ranked graph rank = true) :
    ∀ rounds key source, graph.blocks.lookup key = some source → rank key < rounds →
      demand graph (OrderedExits.forScope graph exits) inputs (rounds + 1) key =
        demand graph (OrderedExits.forScope graph exits) inputs rounds key
  | 0, _, _, _, low => by omega
  | rounds + 1, key, source, found, low => by
    show demandStep graph _ inputs _ key = demandStep graph _ inputs _ key
    simp only [demandStep, found, Option.elim]
    apply demandOf_congr_proof
    intro route routeMember t target
    cases next : graph.blocks.lookup t with
    | none => rw [demand_absent_proof _ _ _ _ next, demand_absent_proof _ _ _ _ next]
    | some nextSource =>
      have lower : rank t < rank key := by
        simp only [GlobalSSA.routes, lookup_forScope_proof, found, Option.map_some, Option.elim,
          List.mem_map] at routeMember
        obtain ⟨inner, innerMember, rfl⟩ := routeMember
        have listed := body_route_target_proof _ _ inner innerMember
        rw [body_relabel_targets_proof, show inner.target = some t from target] at listed
        obtain ⟨original, inTargets, eq⟩ := List.mem_map.mp listed
        have same : original = some t := by
          by_cases declared : original ∈ exits
          · simp [OrderedExits.scopeLabel, declared] at eq
          · simpa [OrderedExits.scopeLabel, declared] using eq
        simp only [ranked, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ok
        have here := (ok (key, source) (lookup_mem_proof _ found)).2 (some t) (same ▸ inTargets)
        simpa [next] using here
      exact demand_stable_proof graph exits inputs rank ok rounds t nextSource next (by omega)

/-- A ranked graph is saturated. -/
theorem saturated_of_ranked_proof (graph : Graph V K F) (exits : List (Option K))
    (inputs : List V) (rank : K → Nat) (ok : ranked graph rank = true) :
    saturated graph exits inputs = true := by
  simp only [saturated, List.all_eq_true, decide_eq_true_eq]
  intro item member
  have present := lookup_isSome_proof' graph.blocks (key := item.1) (value := item.2) member
  have low : rank item.1 < graph.blocks.length := by
    have here := ok
    simp only [ranked, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at here
    exact (here item member).1
  cases found : graph.blocks.lookup item.1 with
  | none => simp [found] at present
  | some source => exact demand_stable_proof graph exits inputs rank ok _ item.1 source found low

/-- Every demand is within the arrival claim of its block. -/
theorem demand_claimed_proof (graph : Graph V K F) (exits : List (Option K)) (inputs : List V)
    (certificate : GlobalSSA.Certificate V K)
    (scopeOk : GlobalSSA.check (OrderedExits.forScope graph exits) inputs certificate = true)
    (claims : claimed graph certificate = true) :
    ∀ rounds key, ∀ z ∈ demand graph (OrderedExits.forScope graph exits) inputs rounds key,
      z ∈ (certificate.lookup key).getD []
  | 0, _, z, member => by simp [demand] at member
  | rounds + 1, key, z, member => by
    simp only [demand, demandStep] at member
    cases found : graph.blocks.lookup key with
    | none =>
      rw [found] at member
      simp at member
    | some source =>
      rw [found] at member
      simp only [Option.elim, demandOf, List.mem_dedup, List.mem_filter, List.mem_flatMap] at member
      obtain ⟨⟨route, routeMember, needed⟩, _⟩ := member
      have here := claims
      simp only [claimed, List.all_eq_true] at here
      have claim := here (key, source) (lookup_mem_proof _ found)
      cases looked : certificate.lookup key with
      | none => simp [looked] at claim
      | some req =>
        have checks := scopeOk
        simp only [GlobalSSA.check, Bool.and_eq_true, decide_eq_true_eq] at checks
        obtain ⟨_, _, _, _, blocksOk⟩ := checks
        have checked := List.all_eq_true.mp blocksOk (key, req) (lookup_mem_proof certificate looked)
        simp only [Bool.and_eq_true] at checked
        exact needs_claimed_proof certificate _
          (demand_claimed_proof graph exits inputs certificate scopeOk claims rounds) route.target
          route.accesses req (List.all_eq_true.mp checked.2 route routeMember) z needed

/-- The inferred table is closed, when the existing check accepts the
graph with some arrival claims, every block has a claim that lists no
register the block defines, and the demand is saturated. -/
theorem closed_infer_proof (graph : Graph V K F) (exits : List (Option K)) (inputs : List V)
    (certificate : GlobalSSA.Certificate V K)
    (ok : OrderedExits.check graph exits inputs certificate = true)
    (claims : claimed graph certificate = true)
    (stable : saturated graph exits inputs = true) :
    closed graph (infer graph exits inputs) exits inputs = true := by
  simp only [OrderedExits.check, Bool.and_eq_true] at ok
  obtain ⟨partition, scopeOk⟩ := ok
  have checks := scopeOk
  simp only [GlobalSSA.check, Bool.and_eq_true, decide_eq_true_eq] at checks
  obtain ⟨normalized, _, _, entryOk, blocksOk⟩ := checks
  have labels : (graph.blocks.map Prod.fst).Nodup := by
    simp only [Graph.check, Bool.and_eq_true, decide_eq_true_eq] at normalized
    have distinct := normalized.1.1
    simpa [OrderedExits.forScope, List.map_map, Function.comp_def] using distinct
  -- what the table gives is the demand after as many rounds as there are blocks
  have same : (infer graph exits inputs).received =
      demand graph (OrderedExits.forScope graph exits) inputs graph.blocks.length := by
    funext key
    rw [received_infer_eq_proof]
    cases found : graph.blocks.lookup key with
    | none => rw [demand_absent_proof _ _ _ _ found, demand_absent_proof _ _ _ _ found]
    | some source =>
      have here := stable
      simp only [saturated, List.all_eq_true, decide_eq_true_eq] at here
      exact here (key, source) (lookup_mem_proof _ found)
  have within : ∀ target, ∀ z ∈ (infer graph exits inputs).received target,
      z ∈ (certificate.lookup target).getD [] := fun target z member =>
    demand_claimed_proof graph exits inputs certificate scopeOk claims (graph.blocks.length + 1)
      target z (received_infer_eq_proof graph exits inputs target ▸ member)
  have distinct : ∀ key, ((infer graph exits inputs).received key).Nodup := by
    intro key
    rw [received_infer_eq_proof]
    simp only [demand, demandStep]
    cases graph.blocks.lookup key <;> simp [demandOf, List.nodup_dedup]
  simp only [closed, OrderedExits.check, Bool.and_eq_true]
  refine ⟨by rw [checkExits_forward_proof]; exact partition, ?_⟩
  rw [forScope_forward_proof graph _ exits partition]
  have arrivals : inputArrivals graph inputs =
      (OrderedExits.forScope graph exits).blocks.map fun item =>
        (item.1, inputs.map (Sum.inl : V → Name V K)) := by
    show graph.blocks.map _ = (graph.blocks.map _).map _
    rw [List.map_map]
    rfl
  rw [arrivals]
  refine check_closed_proof (OrderedExits.forScope graph exits) (infer graph exits inputs) inputs
    certificate scopeOk distinct ?_ ?_
  · intro route member z needed
    exact needs_claimed_proof certificate _ within route.target route.accesses inputs
      (List.all_eq_true.mp entryOk route member) z needed
  · intro item member route routeMember z needed
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    by_cases row : z ∈ original.2.rows.map Row.dst
    · exact .inr (.inl row)
    by_cases input : z ∈ inputs
    · exact .inl input
    refine .inr (.inr ?_)
    have found := lookup_member_proof graph.blocks labels (value := original.2) originalMember
    have here := claims
    simp only [claimed, List.all_eq_true] at here
    have claim := here original originalMember
    cases looked : certificate.lookup original.1 with
    | none => simp [looked] at claim
    | some req =>
      simp only [looked, Option.any_some, List.all_eq_true] at claim
      have checked := List.all_eq_true.mp blocksOk (original.1, req)
        (lookup_mem_proof certificate looked)
      simp only [Bool.and_eq_true] at checked
      have full : (⟨route.target, .define (original.2.rows.map Row.dst) :: route.accesses⟩ :
          GlobalSSA.Route V K) ∈
          GlobalSSA.routes (OrderedExits.forScope graph exits) (some original.1) := by
        simp only [GlobalSSA.routes, lookup_forScope_proof, found, Option.map_some, Option.elim,
          List.mem_map]
        exact ⟨route, routeMember, rfl⟩
      have fullNeeds : z ∈ needs ((GlobalSSA.Access.define (original.2.rows.map Row.dst) ::
          route.accesses) ++ [.read (route.target.elim [] (infer graph exits inputs).received)]) := by
        simp only [List.cons_append, needs, List.mem_filter]
        exact ⟨needed, by simpa using row⟩
      have inClaim : z ∈ req := needs_claimed_proof certificate _ within route.target _ req
        (List.all_eq_true.mp checked.2 _ full) z fullNeeds
      have outside := claim z inClaim
      rw [received_infer_eq_proof]
      simp only [demand, demandStep, found, Option.elim, demandOf, List.mem_dedup, List.mem_filter,
        List.mem_flatMap]
      refine ⟨⟨_, full, same ▸ fullNeeds⟩, ?_⟩
      simpa [input] using outside

end Demand

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Forward
