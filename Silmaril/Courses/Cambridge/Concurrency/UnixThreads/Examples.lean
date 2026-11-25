module

public import Silmaril.Courses.Cambridge.Concurrency.UnixThreads.Metatheory

/-! # Checked schedules for Exercise 40 -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.Concurrency.UnixThreads.Examples

def cells : L1.Store :=
  (((∅ : L1.Store).insert "child" 0).insert "data" 0).insert "out" 0

def locations : L1.TypeEnv :=
  (((∅ : L1.TypeEnv).insert "child" .intref).insert "data" .intref).insert "out" .intref

def sender : Command := .run (.assign "data" (.int 7)) (.send "pipe" "data" .done)

def receiver : Command := .receive "pipe" "out" (.join "child" .done)

def initial : Config := Config.start (.fork "child" sender receiver) cells

def spawned : Config := initial.spawn 0 "child" sender receiver

def written : Config :=
  { spawned with store := spawned.store.insert "data" 7 }.resume 1 (.run .skip (.send "pipe" "data" .done))

def continued : Config := written.resume 1 (.send "pipe" "data" .done)

def sent : Config := continued.enqueue 1 "pipe" 7 .done

def received : Config := sent.dequeue 0 "pipe" "out" 7 [] (.join "child" .done)

def joined : Config := received.reap 0 1 .done

theorem fork_send_receive_join : lts.MTr initial [0, 1, 1, 1, 0, 0] joined := by
  have fork : Step initial 0 spawned := .fork
    (by simp [initial, Config.start]) (by simp [initial, Config.start, cells])
    (by simp [initial, Config.start, Finmap.notMem_empty])
  have write : Step spawned 1 written :=
    .runStep (by simp [spawned, initial, Config.start, Config.spawn, sender])
      (.assignValue (by simp [spawned, initial, Config.start, Config.spawn, cells]))
  have closeRun : Step written 1 continued :=
    .runDone (by simp [written, Config.resume])
  have send : Step continued 1 sent := .send (source := "data") (by simp [continued, Config.resume])
    (by simp [continued, written, Config.resume])
  have receive : Step sent 0 received := .receive
    (by simp [sent, continued, written, spawned, initial, Config.enqueue, Config.resume,
      Config.spawn, Config.start, receiver])
    (by simp [sent, continued, written, spawned, initial, Config.enqueue, Config.resume,
      Config.spawn, Config.start, cells])
    (by simp [sent, continued, written, spawned, initial, Config.enqueue, Config.resume,
      Config.spawn, Config.start])
  have join : Step received 0 joined := .join (handle := "child") (child := 1)
    (by simp [received, Config.dequeue, Config.resume])
    (by simp [received, sent, continued, written, spawned, initial, Config.dequeue, Config.enqueue,
      Config.resume, Config.spawn, Config.start])
    (by simp [received, sent, Config.dequeue, Config.enqueue, Config.resume])
  exact .stepL fork (.stepL write (.stepL closeRun (.stepL send (.stepL receive (.stepL join .refl)))))

theorem joined_observation :
    L1.Store.lookup joined.store "out" = some 7 ∧ joined.queues "pipe" = [] ∧
      joined.threads.lookup 0 = some .done ∧ joined.threads.lookup 1 = none ∧ joined.nextId = 2 := by
  simp [joined, received, sent, continued, written, spawned, initial, Config.reap, Config.dequeue,
    Config.enqueue, Config.resume, Config.spawn, Config.start]

theorem initial_wellFormed : initial.WellFormed locations := by
  apply Config.start_wellFormed
  · exact .fork (by simp [locations])
      (.run (.assign (by simp [locations]) (.int 7)) (.send (by simp [locations]) .done))
      (.receive (by simp [locations]) (.join (by simp [locations]) .done))
  · intro loc present
    simpa [locations, cells, Finmap.notMem_empty] using present

theorem joined_wellFormed : joined.WellFormed locations :=
  trace_preserves_wellFormed fork_send_receive_join initial_wellFormed

def fifoStart : Config :=
  { Config.start (.receive "pipe" "out" (.receive "pipe" "data" .done)) cells with
    queues := Function.update (fun _ => []) "pipe" [7, 9] }

def fifoMiddle : Config :=
  fifoStart.dequeue 0 "pipe" "out" 7 [9] (.receive "pipe" "data" .done)

def fifoDone : Config := fifoMiddle.dequeue 0 "pipe" "data" 9 [] .done

theorem fifo_trace : lts.MTr fifoStart [0, 0] fifoDone := by
  have first : Step fifoStart 0 fifoMiddle := .receive (by simp [fifoStart, Config.start])
    (by simp [fifoStart, Config.start, cells]) (by simp [fifoStart])
  have second : Step fifoMiddle 0 fifoDone := .receive
    (by simp [fifoMiddle, Config.dequeue, Config.resume])
    (by simp [fifoMiddle, fifoStart, Config.dequeue, Config.resume, Config.start, cells])
    (by simp [fifoMiddle, Config.dequeue])
  exact .stepL first (.stepL second .refl)

theorem fifo_observation :
    L1.Store.lookup fifoDone.store "out" = some 7 ∧
      L1.Store.lookup fifoDone.store "data" = some 9 ∧ fifoDone.queues "pipe" = [] := by
  simp [fifoDone, fifoMiddle, Config.dequeue, Config.resume]

end Silmaril.Courses.Cambridge.Concurrency.UnixThreads.Examples
