module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Direct.Defs
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Equality.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Link
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family.Correct

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Direct.Proofs

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op}
variable {table : MemberSummaries V S} {imports : Ports (Ty V S)} {scope : Scope m}
variable {fn : Function V S}

private theorem capture_get {Ty : Type u} {F : Ty → Type w} {context params : Ports Ty} {ty : Ty}
    (p : Port (context ++ params) ty) (q : Port context ty)
    (selected : capturePort context p = some q) (captured : Tuple F context) (args : Tuple F params) :
    (prependContext args captured).get p = captured.get q := by
  induction captured with
  | nil => simp [capturePort] at selected
  | cons _ tail ih =>
    cases p with
    | head =>
      cases selected
      rfl
    | tail p =>
      cases found : capturePort _ p with
      | none => simp [capturePort, found] at selected
      | some actual =>
        have eq : Port.tail actual = q := by simpa only [capturePort, found, Option.map_some, Option.some.injEq] using selected
        subst q
        exact ih p actual found

private theorem read_get {Ty : Type u} {F : Ty → Type w} {args users : Ports Ty}
    {past : List (Ports Ty)} {ty : Ty}
    (wires : Wires args past users) (p : Port users ty)
    (inputs : Tuple F args) (locals : Locals F past) :
    (wires.read inputs locals).get p = (Wires.read (.cons (wires.get p) .nil) inputs locals).get .head := by
  induction p with
  | head => cases wires; rfl
  | tail _ ih => cases wires; exact ih _

theorem capture_reads {Ty : Type u} {F : Ty → Type w} {imports context params : Ports Ty}
    {outer : List (Ports Ty)} (wires : Wires imports outer context)
    (inputs : Tuple F imports) (locals : Locals F outer) (args : Tuple F params) :
    Boundary.Reads (captureBoundary wires) inputs locals (prependContext args (wires.read inputs locals)) := by
  intro ty p origin found
  cases selected : capturePort context p with
  | none => simp [captureBoundary, selected] at found
  | some captured =>
    have same : wires.get captured = origin := by simpa [captureBoundary, selected] using found
    rw [← same, capture_get p captured selected (wires.read inputs locals) args]
    exact read_get wires captured inputs locals

theorem forward_reads {Ty : Type u} {F : Ty → Type w} {imports entry child : Ports Ty}
    {outer past : List (Ports Ty)} (source : Boundary imports entry outer) (wires : Wires entry past child)
    (inputs : Tuple F imports) (locals : Locals F outer) (values : Tuple F entry)
    (reads : Boundary.Reads source inputs locals values) (childLocals : Locals F past) :
    Boundary.Reads (Boundary.forward source wires) inputs locals (wires.read values childLocals) := by
  intro ty p origin found
  rw [read_get wires p values childLocals]
  cases wire : wires.get p with
  | arg q => exact reads q (by simpa [Boundary.forward, wire] using found)
  | output => simp [Boundary.forward, wire] at found

private theorem same_port {carried : Ports (Ty V S)} {ty : Ty V S} (p q : Port carried ty)
    (same : p.index = q.index) : p = q := by
  have wires : (Tuple.cons (.arg p) .nil : Wires carried [] [ty]) = .cons (.arg q) .nil :=
    NestedTheta.Equality.addresses_injective _ _ (by simp [Wires.addresses, Origin.address, same])
  exact Origin.arg.inj (Tuple.cons.inj wires).1

private theorem feedback_source {carried : Ports (Ty V S)} {outer sigs : List (Ports (Ty V S))}
    {member : Option (MemberSummaries V S)} (source : Boundary imports carried outer)
    (body : Code Op carried [] sigs (Theta.BodyResults carried) true member)
    {ty : Ty V S} (p : Port carried ty) {origin : Origin imports outer ty}
    (found : (source.feedback body).get p = some origin) :
    source.get p = some origin ∧ body.returnArg (.tail p) = some p := by
  cases returned : body.returnArg (.tail p) with
  | none => simp [Boundary.feedback, returned] at found
  | some q =>
    by_cases same : q.index = p.index
    · exact ⟨by simpa [Boundary.feedback, returned, same] using found, congrArg some (same_port q p same)⟩
    · simp [Boundary.feedback, returned, same] at found

theorem feedback_initial {carried : Ports (Ty V S)} {outer sigs : List (Ports (Ty V S))}
    {member : Option (MemberSummaries V S)} (source : Boundary imports carried outer)
    (body : Code Op carried [] sigs (Theta.BodyResults carried) true member)
    (inputs : Tuple m.Val imports) (locals : Locals m.Val outer) (current : Tuple m.Val carried)
    (reads : source.Reads inputs locals current) : (source.feedback body).Reads inputs locals current :=
  fun {_} p {_} found => reads p (feedback_source source body p found).1

theorem feedback_preserves {carried : Ports (Ty V S)} {outer sigs : List (Ports (Ty V S))}
    {member : Option (MemberSummaries V S)} (source : Boundary imports carried outer)
    (body : Code Op carried [] sigs (Theta.BodyResults carried) true member)
    (inputs : Tuple m.Val imports) (locals : Locals m.Val outer) (current next : Tuple m.Val carried)
    (reads : (source.feedback body).Reads inputs locals current) (stable : body.Stable current next) :
    (source.feedback body).Reads inputs locals next :=
  fun {_} p {_} found => (stable p (feedback_source source body p found).2).trans (reads p found)

theorem boundary_project_read {Ty : Type u} {F : Ty → Type w} {imports entry users : Ports Ty}
    {outer past : List (Ports Ty)} (source : Boundary imports entry outer)
    (requested : Wires entry past users) (sources : Wires imports outer users)
    (found : Boundary.project source requested = some sources)
    (inputs : Tuple F imports) (locals : Locals F outer) (values : Tuple F entry)
    (reads : Boundary.Reads source inputs locals values) (inner : Locals F past) :
    sources.read inputs locals = requested.read values inner := by
  induction requested with
  | nil => cases found; rfl
  | cons origin rest ih =>
    cases origin with
    | output => simp [Boundary.project] at found
    | arg p =>
      cases selected : source.get p with
      | none => simp [Boundary.project, selected] at found
      | some q =>
        cases more : Boundary.project source rest with
        | none => simp [Boundary.project, selected, more] at found
        | some tail =>
          have same : Tuple.cons q tail = sources := by simpa [Boundary.project, selected, more] using found
          subst sources
          exact congrArg₂ Tuple.cons (reads p selected).symm (ih tail more)

theorem project_read {Ty : Type u} {F : Ty → Type w} {imports context params users : Ports Ty}
    {past localSigs : List (Ports Ty)} (wires : Wires imports past context)
    (requested : Wires (context ++ params) localSigs users) (sources : Wires imports past users)
    (found : project wires requested = some sources)
    (inputs : Tuple F imports) (locals : Locals F past) (args : Tuple F params) (inner : Locals F localSigs) :
    sources.read inputs locals = requested.read (prependContext args (wires.read inputs locals)) inner :=
  boundary_project_read (captureBoundary wires) requested sources found inputs locals _
    (capture_reads wires inputs locals args) inner

theorem widen_read {args users head : Ports (Ty V S)} {past : List (Ports (Ty V S))}
    (wires : Wires args past users) (inputs : Tuple m.Val args) (locals : Locals m.Val past)
    (value : Tuple m.Val head) :
    (widen wires).read inputs (locals.snoc value) = wires.read inputs locals := by
  induction wires with
  | nil => rfl
  | cons origin _ ih =>
    exact congrArg₂ Tuple.cons
      (Isomorphism.Local.Gamma.extendOrigin_read origin inputs locals value) ih

private theorem drop_read {args tail : Ports (Ty V S)} {past : List (Ports (Ty V S))}
    (front : Ports (Ty V S)) (wires : Wires args past (front ++ tail))
    (inputs : Tuple m.Val args) (locals : Locals m.Val past) :
    Wires.read (StaticDemand.Family.dropPrefix front wires) inputs locals =
      StaticDemand.Family.dropPrefix front (wires.read inputs locals) := by
  induction front with
  | nil => rfl
  | cons _ rest ih =>
    cases wires with
    | cons _ rest => exact ih rest

theorem seed_selects (family : StaticDemand.Family Op table imports) (i : Fin table.members.length)
    (inputs : Tuple m.Val imports) (origins : Wires imports [memberPorts table.members] (table.at i).captures)
    (found : phiCaptures family i = some origins) :
    let seeded := Scope.seed family inputs inputs
    selects seeded.guardL i ((seedWires i origins).read inputs seeded.localsL) := by
  let captured := family.captures.read inputs PUnit.unit
  let refs := family.references captured
  have written := project_read (widen family.captures)
    (StaticDemand.Family.dropPrefix (memberPorts table.members) (family.memberWires i))
    origins found inputs (past := [memberPorts table.members]) (refs, PUnit.unit)
    refs (memberPrefix table.members i.val (family.memberValue captured))
  have outer : (widen (head := memberPorts table.members) family.captures).read inputs (refs, PUnit.unit) = captured :=
    widen_read family.captures inputs PUnit.unit refs
  rw [outer] at written
  refine ⟨StaticDemand.Proofs.member_get table.members (family.memberValue captured) i, ?_⟩
  exact written.trans (drop_read (memberPorts table.members) (family.memberWires i)
    (prependContext refs captured) (memberPrefix table.members i.val (family.memberValue captured)))

theorem new_selects (binding : Binding Op scope.table imports scope.past fn)
    (inputs : Tuple m.Val imports) (locals : Locals m.Val scope.past) (guard : Guard m scope.table) :
    selects (binding.extendGuard guard inputs locals) (0 : Fin (scope.table.members.length + 1))
      ((newWires binding).read inputs (locals.snoc (.cons (binding.value inputs locals) .nil))) := by
  exact ⟨congrArg (fun xs : Tuple m.Val [fn.port] => xs.get .head)
    (Prefix.Proofs.last_read inputs locals (binding.value inputs locals)),
    widen_read binding.captures inputs locals (.cons (binding.value inputs locals) .nil)⟩

theorem boundary_call {entry : Ports (Ty V S)} (source : Boundary imports entry scope.past)
    (i : Fin scope.table.members.length)
    (target : Port entry (scope.table.at i).fn.port)
    (witnesses : Wires entry [] (scope.table.at i).captures)
    (sources expected : Wires imports scope.past (CallPorts scope.table i))
    (found : Boundary.project source (.cons (.arg target) witnesses) = some sources)
    (same : sources.addresses = expected.addresses)
    (inputs : Tuple m.Val imports) (locals : Locals m.Val scope.past) (guard : Guard m scope.table)
    (resolved : selects guard i (expected.read inputs locals)) (values : Tuple m.Val entry)
    (reads : Boundary.Reads source inputs locals values) :
    guard i (values.get target) (witnesses.read values PUnit.unit) := by
  have h := boundary_project_read source _ sources found inputs locals values reads PUnit.unit
  have eq := NestedTheta.Equality.addresses_injective sources expected same
  rw [eq] at h
  unfold selects at resolved
  rw [h] at resolved
  exact resolved

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Direct.Proofs
