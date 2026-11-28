module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader.Defs
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Pass.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader

open Silmaril.SSA.SeaOfNodes
open Diamond (Dataflow Ty ValueSort)
open GVN (weaken newest)
open GVN.Elimination (Routing splitOrigin operandScope)
open GVN.Cyclic
open GVN.Cyclic.Builder (Built build? sorts)
open GVN.Cyclic.Builder.Preheader
open GVN.Cyclic.Deletion (DeletedLoop Route)
open Loop (headerPorts)
open Pure.SubZero (Opcode)
open Silmaril.SSA.RVSDG (Origin Port Tuple Wires extend)
open scoped Pure.WordNormalize

-- Track argument reads across prefix changes. Output wires always refer to
-- the current typed producer scope and do not name capture arguments.
private abbrev Allowed (args : List (Ty Unit)) := ∀ t : Ty Unit, Port args t → Prop

private def WireAllowed {args : List (Ty Unit)} (allowed : Allowed args)
    {past : List (List (Ty Unit))} {t : Ty Unit} : Origin args past t → Prop
  | .arg port => allowed _ port
  | .output .. => True

private def WiresAllowed {args : List (Ty Unit)} (allowed : Allowed args)
    {past : List (List (Ty Unit))} : {ports : List (Ty Unit)} → Wires args past ports → Prop
  | _, .nil => True
  | _, .cons wire rest => WireAllowed allowed wire ∧ WiresAllowed allowed rest

private def FlowAllowed {args : List (Ty Unit)} (allowed : Allowed args) :
    {past sigs : List (List (Ty Unit))} → Dataflow Opcode args past sigs → Prop
  | _, _, .nil => True
  | _, _, .cons _ wires rest => WiresAllowed allowed wires ∧ FlowAllowed allowed rest

section Routing

variable {args targetArgs ports : List (Ty Unit)} {past target sigs : List (List (Ty Unit))}
variable {allowed : ∀ t : Ty Unit, Port args t → Prop}
variable {allowedTarget : ∀ t : Ty Unit, Port targetArgs t → Prop} {t : Ty Unit}

private theorem allowed_weaken (head : List (Ty Unit)) (wire : Origin args past t)
    (safe : WireAllowed allowed wire) : WireAllowed allowed (weaken head wire) := by
  cases wire <;> exact safe

private theorem allowed_split (head : List (Ty Unit)) {wire : Origin args (past ++ [head]) t}
    {prior : Origin args past t} (split : splitOrigin head wire = .inl prior)
    (safe : WireAllowed allowed wire) : WireAllowed allowed prior := by
  cases wire with
  | arg p =>
    cases split
    exact safe
  | output i port =>
    cases which : GVN.Elimination.splitOutput head past i port with
    | inl old =>
      rcases old with ⟨_, _⟩
      simp only [splitOrigin, which, Sum.map_inl, Sum.inl.injEq] at split
      subst prior
      trivial
    | inr last => simp [splitOrigin, which] at split

private theorem allowed_map (route : Routing args past target targetArgs)
    (safe : ∀ {s} (wire : Origin args past s), WireAllowed allowedTarget (route wire))
    (wires : Wires args past ports) : WiresAllowed allowedTarget (route.wires wires) := by
  induction wires with
  | nil => trivial
  | cons wire _ ih => exact ⟨safe wire, ih⟩

private theorem allowed_plugSuffix (flow : Dataflow Opcode args past sigs)
    (route : Routing args past target targetArgs)
    (safe : ∀ {s} (wire : Origin args past s), WireAllowed allowedTarget (route wire)) :
    let edited := GVN.Elimination.routeSuffix flow route
    FlowAllowed allowedTarget edited.1 ∧
      ∀ {s} (wire : Origin args (extend past sigs) s), WireAllowed allowedTarget (edited.2 wire) := by
  induction flow generalizing target with
  | nil => exact ⟨True.intro, safe⟩
  | @cons scope _ _ result op wires rest ih =>
    have pushed {s} (wire : Origin args (scope ++ [[.value result]]) s) :
        WireAllowed allowedTarget (route.push [.value result] wire) := by
      unfold Routing.push
      split
      · exact allowed_weaken _ _ (safe _)
      · trivial
    exact ⟨⟨allowed_map route safe wires, (ih _ pushed).1⟩, (ih _ pushed).2⟩

variable (route : Route args past target)

private def Preserves : Prop :=
  ∀ {s} {wire : Origin args past s} {mapped : Origin args target s},
    route wire = some mapped → WireAllowed allowed wire → WireAllowed allowed mapped

private theorem allowed_drop (head : List (Ty Unit)) :
    Preserves (allowed := allowed) (Deletion.drop (args := args) (past := past) head) := by
  intro s wire mapped accepted safe
  cases split : splitOrigin head wire with
  | inl prior =>
    have same : prior = mapped := by simpa [Deletion.drop, split] using accepted
    subst mapped
    exact allowed_split _ split safe
  | inr last => simp [Deletion.drop, split] at accepted

private theorem allowed_push (safe : Preserves (allowed := allowed) route) (head : List (Ty Unit)) :
    Preserves (allowed := allowed) (route.push head) := by
  intro s wire mapped accepted before
  cases split : splitOrigin head wire with
  | inl prior =>
    have mappedEq : (route prior).map (weaken head) = some mapped := by
      simpa [Route.push, split] using accepted
    obtain ⟨_, routed, rfl⟩ := Option.map_eq_some_iff.mp mappedEq
    exact allowed_weaken _ _ (safe routed (allowed_split _ split before))
  | inr port =>
    have mappedEq : newest port = mapped := by simpa [Route.push, split] using accepted
    subst mapped
    trivial

private theorem allowed_routeWires (safe : Preserves (allowed := allowed) route)
    {wires : Wires args past ports} {mapped : Wires args target ports}
    (accepted : route.wires? wires = some mapped) (before : WiresAllowed allowed wires) :
    WiresAllowed allowed mapped := by
  induction wires with
  | nil => cases accepted; trivial
  | cons wire rest ih =>
    obtain ⟨_, routed, next⟩ := Option.bind_eq_some_iff.mp accepted
    obtain ⟨_, tail, eq⟩ := Option.bind_eq_some_iff.mp next
    cases eq
    exact ⟨safe routed before.1, ih tail before.2⟩

private theorem allowed_routeSuffix {flow : Dataflow Opcode args past sigs}
    {mapped : Dataflow Opcode args target sigs} {finalRoute : Route args (extend past sigs) (extend target sigs)}
    (safe : Preserves (allowed := allowed) route) (before : FlowAllowed allowed flow)
    (accepted : Deletion.routeSuffix? flow route = some (mapped, @finalRoute)) :
    FlowAllowed allowed mapped ∧ Preserves (allowed := allowed) finalRoute := by
  induction flow generalizing target with
  | nil => cases accepted; exact ⟨True.intro, safe⟩
  | cons _ _ _ ih =>
    obtain ⟨_, routed, next⟩ := Option.bind_eq_some_iff.mp accepted
    obtain ⟨⟨_, _⟩, tail, eq⟩ := Option.map_eq_some_iff.mp next
    cases eq
    have suffix := ih _ (allowed_push route safe _) before.2 tail
    exact ⟨⟨allowed_routeWires route safe routed before.1, suffix.1⟩, suffix.2⟩

private theorem allowed_erase {flow : Dataflow Opcode args past sigs}
    {sort : ValueSort Unit} (candidate : GVN.Producer flow sort) {edited : Deletion.Erasure Opcode args past sigs}
    (before : FlowAllowed allowed flow) (accepted : Deletion.erase? candidate = some edited) :
    FlowAllowed allowed edited.flow ∧ Preserves (allowed := allowed) edited.route := by
  induction candidate with
  | here =>
    obtain ⟨⟨_, _⟩, routed, eq⟩ := Option.map_eq_some_iff.mp accepted
    cases eq
    exact allowed_routeSuffix _ (allowed_drop _) before.2 routed
  | later _ ih =>
    obtain ⟨_, routed, eq⟩ := Option.map_eq_some_iff.mp accepted
    cases eq
    have tail := ih before.2 routed
    exact ⟨⟨before.1, tail.1⟩, tail.2⟩

private theorem allowed_set {wires : Wires args past ports} (use : Port ports t)
    {replacement : Origin args past t} (before : WiresAllowed allowed wires)
    (safe : WireAllowed allowed replacement) :
    WiresAllowed allowed (HeaderUse.setOperand use replacement wires) := by
  induction use with
  | head => cases wires; exact ⟨safe, before.2⟩
  | tail _ ih => cases wires; exact ⟨before.1, ih before.2 safe⟩

private theorem allowed_replace {flow : Dataflow Opcode args past sigs} {sort : ValueSort Unit}
    (consumer : GVN.Producer flow sort) (use : Port (Diamond.dataPorts consumer.key.ins) t)
    {wire : Origin args (operandScope consumer) t} (before : FlowAllowed allowed flow)
    (safe : WireAllowed allowed wire) : FlowAllowed allowed (HeaderUse.replaceAt consumer use wire) := by
  induction consumer with
  | here => exact ⟨allowed_set use before.1 safe, before.2⟩
  | later _ ih => exact ⟨before.1, ih use before.2 safe⟩

private theorem allowed_prefix {flow : Dataflow Opcode args past sigs} {sort : ValueSort Unit}
    (consumer : GVN.Producer flow sort) (available : List (Pass.OutputWire args past))
    (safe : ∀ wire ∈ available, WireAllowed allowed wire.2)
    (wire : Pass.OutputWire args (operandScope consumer)) (member : wire ∈ Pass.prefixOutputs consumer available) :
    WireAllowed allowed wire.2 := by
  induction consumer with
  | here => exact safe wire member
  | later _ ih =>
    apply ih _ _ wire member
    intro next nextMem
    rcases List.mem_append.mp nextMem with earlier | last
    · obtain ⟨⟨sort, old⟩, mem, rfl⟩ := List.mem_map.mp earlier
      exact allowed_weaken _ old (safe ⟨sort, old⟩ mem)
    · obtain rfl := List.mem_singleton.mp last
      trivial

end Routing

variable {inputs carried added : List (ValueSort Unit)}
variable {entrySigs headerSigs past : List (List (Ty Unit))} {out : ValueSort Unit}

-- A kept argument is in the image of the original interface after lifting.
private abbrev Kept : Allowed (headerPorts (added ++ inputs) carried) :=
  fun _ port => ∃ original, dropHeaderPort? added port = some original

private theorem drop_lift {t : Ty Unit} (port : Port (headerPorts inputs carried) t) :
    dropHeaderPort? added (liftHeaderPort added port) = some port := by
  induction added with
  | nil => rfl
  | cons _ _ ih => exact ih

private theorem get_map {F G : Ty Unit → Type} {args : List (Ty Unit)} {t : Ty Unit}
    (p : Port args t) (tuple : Tuple F args) (f : ∀ t, F t → G t) :
    (tuple.map f).get p = f _ (tuple.get p) := by
  induction p with
  | head => cases tuple; rfl
  | tail _ ih => cases tuple with | cons _ tail => exact ih tail

private theorem identity_get {args : List (Ty Unit)} {t : Ty Unit} (p : Port args t) :
    (Silmaril.SSA.RVSDG.NestedTheta.identityPorts args).get p = p := by
  induction p with
  | head => rfl
  | tail _ ih =>
    simp only [Silmaril.SSA.RVSDG.NestedTheta.identityPorts, Tuple.get, get_map, ih]

private abbrev HeaderAllowed (loop : Native (added ++ inputs) carried entrySigs headerSigs out) : Prop :=
  FlowAllowed (Kept (added := added)) loop.header ∧
    WiresAllowed (Kept (added := added)) (observations loop)

private theorem allowed_prepare (loop : Native inputs carried entrySigs headerSigs out) :
    HeaderAllowed (added := carried) (inputs := inputs) (prepare loop) := by
  have safe {t} (wire : Origin (headerPorts inputs carried) [] t) :
      WireAllowed (Kept (added := carried)) (Routing.ofWires (headerInputs carried) wire) := by
    cases wire with
    | arg p =>
      change WireAllowed _ ((headerInputs carried).get p)
      rw [headerInputs, get_map, identity_get]
      exact ⟨p, drop_lift p⟩
    | output i _ => exact i.elim0
  obtain ⟨body, route⟩ := allowed_plugSuffix loop.header _ safe
  have packet := allowed_map _ route (observations loop)
  refine ⟨body, ?_⟩
  change WiresAllowed _ (Tuple.cons _ (.cons _ _))
  generalize (GVN.Elimination.plug loop.header (observations loop) (headerInputs carried)).2 = wires at packet ⊢
  cases wires with
  | cons guard tail => cases tail; exact packet

private theorem allowed_delete {loop : Native (added ++ inputs) carried entrySigs headerSigs out}
    {sort : ValueSort Unit} {candidate : GVN.Producer loop.header sort}
    {edited : DeletedLoop Opcode (added ++ inputs) carried entrySigs out}
    (before : HeaderAllowed (added := added) (inputs := inputs) loop) (accepted : Deletion.delete? loop candidate = some edited) :
    HeaderAllowed (added := added) (inputs := inputs) edited.graph := by
  obtain ⟨_, erased, next⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨_, guard, next⟩ := Option.bind_eq_some_iff.mp next
  obtain ⟨_, feedback, next⟩ := Option.bind_eq_some_iff.mp next
  obtain ⟨_, exit, rfl⟩ := Option.map_eq_some_iff.mp next
  obtain ⟨body, route⟩ := allowed_erase candidate before.1 erased
  exact ⟨body, route guard before.2.1, route exit before.2.2.1, allowed_routeWires _ route feedback before.2.2.2⟩

private theorem allowed_redirectWire {loop : Native (added ++ inputs) carried entrySigs headerSigs out}
    {n : Nat} {sorts : Fin n → ValueSort Unit} {g : GVN.Cyclic.Graph Opcode (added ++ inputs) sorts}
    (view : Activation.View g loop) (selected : Σ sort, GVN.Producer loop.header sort)
    {edit : Pass.Redirect loop sorts} (member : edit ∈ Pass.redirects view selected) :
    WireAllowed (Kept (added := added)) edit.wire := by
  rcases selected with ⟨_, consumer⟩
  simp only [Pass.redirects, List.mem_flatMap] at member
  obtain ⟨⟨sort, use⟩, _, original, _, ⟨wireSort, wire⟩, available, member⟩ := member
  have safe := allowed_prefix (allowed := Kept (added := added)) consumer []
    (by simp) ⟨wireSort, wire⟩ available
  split at member
  · rename_i same
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
    cases same
    exact safe
  · simp at member

private theorem allowed_tryProposal {loop : Native (added ++ inputs) carried entrySigs headerSigs out}
    {n : Nat} {sorts : Fin n → ValueSort Unit} {g : GVN.Cyclic.Graph Opcode (added ++ inputs) sorts}
    (view : Activation.View g loop) {p : Partition n} {proposal : Pass.Proposal loop sorts}
    {edited : DeletedLoop Opcode (added ++ inputs) carried entrySigs out}
    (before : HeaderAllowed (added := added) (inputs := inputs) loop)
    (member : proposal ∈ Pass.proposals view) (accepted : Pass.tryProposal? view p proposal = some edited) :
    HeaderAllowed (added := added) (inputs := inputs) edited.graph := by
  simp only [Pass.proposals, List.mem_append, List.mem_map, List.mem_flatMap] at member
  rcases member with ⟨⟨_, _⟩, _, rfl⟩ | ⟨selected, _, edit, listed, rfl⟩
  · exact allowed_delete before accepted
  · obtain ⟨redirected, redirection, deleted⟩ := Option.bind_eq_some_iff.mp accepted
    unfold HeaderUse.redirect? at redirection
    split at redirection
    · have eq := Option.some.inj redirection
      subst redirected
      obtain ⟨⟨_, candidate⟩, _, erased⟩ := List.exists_of_findSome?_eq_some deleted
      exact allowed_delete (loop := { loop with header := HeaderUse.replaceAt edit.consumer edit.use edit.wire })
        ⟨allowed_replace edit.consumer edit.use before.1 (allowed_redirectWire view selected listed), before.2⟩ erased
    · contradiction

private theorem strip_wire {t : Ty Unit} {wire : Origin (headerPorts (added ++ inputs) carried) past t}
    (safe : WireAllowed (Kept (added := added)) wire) :
    ∃ stripped, stripWire? added wire = some stripped := by
  cases wire with
  | arg p =>
    obtain ⟨port, dropped⟩ := safe
    exact ⟨.arg port, by simp [stripWire?, dropped]⟩
  | output i p => exact ⟨.output i p, rfl⟩

private theorem strip_wires {ports : List (Ty Unit)} {wires : Wires (headerPorts (added ++ inputs) carried) past ports}
    (safe : WiresAllowed (Kept (added := added)) wires) :
    ∃ stripped, stripWires? added wires = some stripped := by
  induction wires with
  | nil => exact ⟨.nil, rfl⟩
  | cons _ _ ih =>
    obtain ⟨wire, head⟩ := strip_wire safe.1
    obtain ⟨rest, tail⟩ := ih safe.2
    exact ⟨.cons wire rest, by simp [stripWires?, head, tail]⟩

private theorem strip_flow {flow : Dataflow Opcode (headerPorts (added ++ inputs) carried) past headerSigs}
    (safe : FlowAllowed (Kept (added := added)) flow) :
    ∃ stripped, stripFlow? added flow = some stripped := by
  induction flow with
  | nil => exact ⟨.nil, rfl⟩
  | cons op _ _ ih =>
    obtain ⟨inputs, wires⟩ := strip_wires safe.1
    obtain ⟨rest, tail⟩ := ih safe.2
    exact ⟨.cons op inputs rest, by simp [stripFlow?, wires, tail]⟩

variable {loop : Native inputs carried entrySigs headerSigs out}
variable {edited : DeletedLoop Opcode (carried ++ inputs) carried [] out}

theorem proposal_restores (built : Built (prepare loop)) {proposal : Pass.Proposal (prepare loop) (sorts (prepare loop))}
    (member : proposal ∈ Pass.proposals built.view)
    (accepted : Pass.tryProposal? built.view (FixedPoint.normalize built.graph) proposal = some edited) :
    ∃ result, restore? loop edited = some result := by
  obtain ⟨body, packet⟩ := allowed_tryProposal built.view (allowed_prepare loop) member accepted
  obtain ⟨_, strippedBody⟩ := strip_flow body
  obtain ⟨_, strippedPacket⟩ := strip_wires packet
  unfold restore?
  rw [strippedBody, strippedPacket]
  exact ⟨_, rfl⟩

private theorem findSome_bind {A B C : Type} (check : A → Option B) (finish : B → Option C)
    (proposals : List A)
    (restores : ∀ a ∈ proposals, ∀ b, check a = some b → ∃ c, finish b = some c) :
    (proposals.findSome? check).bind finish = proposals.findSome? (fun a => (check a).bind finish) := by
  induction proposals with
  | nil => rfl
  | cons a rest ih =>
    rw [List.findSome?_cons, List.findSome?_cons]
    cases checked : check a with
    | none => exact ih (fun b member => restores b (List.mem_cons_of_mem a member))
    | some edited =>
      obtain ⟨result, restored⟩ := restores a List.mem_cons_self edited checked
      change finish edited = (match finish edited with
        | some result => some result
        | none => rest.findSome? (fun a => (check a).bind finish))
      rw [restored]

theorem optimize_eq_scan (built : Built (prepare loop)) (builtEq : build? (prepare loop) = some built) :
    optimize? loop = (Pass.proposals built.view).findSome? (fun proposal =>
      (Pass.tryProposal? built.view (FixedPoint.normalize built.graph) proposal).bind (restore? loop)) := by
  unfold optimize?
  rw [builtEq]
  change (Pass.step? built.view).bind (restore? loop) = _
  exact findSome_bind _ _ _ (fun _ member _ accepted => proposal_restores built member accepted)

theorem optimize_none_iff (built : Built (prepare loop)) (builtEq : build? (prepare loop) = some built) :
    optimize? loop = none ↔
      ∀ proposal ∈ Pass.proposals built.view, Pass.tryProposal? built.view (FixedPoint.normalize built.graph) proposal = none := by
  unfold optimize?
  rw [builtEq, ← Pass.step?_eq_none_iff]
  change (Pass.step? built.view).bind (restore? loop) = none ↔ _
  cases stepped : Pass.step? built.view with
  | none => change (none : Option (DeletedLoop Opcode inputs carried entrySigs out)) = none ↔ _; simp
  | some edited =>
    obtain ⟨proposal, member, accepted⟩ := Pass.step?_accepted built.view stepped
    obtain ⟨result, restored⟩ := proposal_restores built member accepted
    change restore? loop edited = none ↔ some edited = none
    simp only [restored, reduceCtorEq]

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader
