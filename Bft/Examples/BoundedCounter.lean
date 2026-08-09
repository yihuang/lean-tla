import Bft.Core
import Bft.Rules
import Bft.Refine
import Bft.Exec
import Bft.Tactic

/-!
# Bft.Examples.BoundedCounter — message-layer refinement demo (M4)

The smallest nontrivial instance of the M4 refinement layer:

* **High-level spec** ("global function"): a counter bounded by `cap`,
  `GNext: n < cap → n' = n + 1`, with the invariant `n ≤ cap`.
* **Low-level system**: a client and a server connected by a message soup.
  The client sends `inc` packets (guard: the *global* count, including
  in-flight messages, stays below `cap`); the server receives a packet and
  increments its local value.
* **Abstraction**: `abs t = server value + in-flight messages`. A `Send`
  step increments the abstraction (maps to `GNext`); a `Receive` step
  leaves it unchanged (stutter). So `refine_invariant` transports
  `n ≤ cap` to the distributed system: **the total number of increments in
  the whole system — applied or still in flight — never exceeds `cap`**.
* **Execution layer**: guarded actions, an executable run, and the
  transported invariant checked on runs.

Fairness is deliberately absent (the demo is safety-only); liveness would
add explicit justice hypotheses, as in `Examples/TicketLock`.

(The low-level state is a concrete record rather than `NetState`: keeping
the counter fields syntactically `ℕ` makes the arithmetic steps
omega-friendly. `NetState` remains the generic interface for real systems.)
-/

namespace Bft.Examples.BoundedCounter

/-- Global bound on increments. -/
def cap : ℕ := 2

/-! ## High-level spec -/

def GInit : StatePred ℕ := fun n => n = 0

def GNext : Action ℕ := fun n n' => n < cap ∧ n' = n + 1

/-- Frame: the counter itself. -/
def gvars (n : ℕ) : ℕ := n

theorem g_init_inv : ∀ s, GInit s → (fun n => n ≤ cap) s :=
  fun _s hs => hs ▸ Nat.zero_le _

theorem g_step_inv : ∀ s s', StutAction GNext gvars s s' →
    (fun n => n ≤ cap) s → (fun n => n ≤ cap) s' := by
  intro s s' hstep hinv
  have h : s ≤ cap := hinv
  rcases hstep with ⟨hlt, hs'⟩ | hstut
  · show s' ≤ cap
    omega
  · have h' : s' = s := hstut
    rw [h']
    exact hinv

theorem gsafety :
    Entails (tlaAnd (statePred GInit) (stutAlways GNext gvars))
      (always (statePred fun n => n ≤ cap)) :=
  init_invariant_stut GInit GNext gvars (fun n => n ≤ cap) g_init_inv g_step_inv

/-! ## Low-level system: client, server, message soup -/

/-- Low-level state: requests issued by the client, increments applied by
the server, and the in-flight packets. -/
structure LSt where
  client : ℕ
  server : ℕ
  msgs : List (Packet (Fin 2) Unit)
deriving Repr

/-- Abstraction: applied increments plus in-flight requests. -/
def abs (t : LSt) : ℕ := t.server + t.msgs.length

def LInit : StatePred LSt := fun t => t.client = 0 ∧ t.server = 0 ∧ t.msgs = []

/-- The client issues a request, provided the global count stays in bounds. -/
def Send : Action LSt := fun t t' =>
  abs t < cap ∧
  t' = { t with client := t.client + 1, msgs := t.msgs ++ [⟨0, 1, ()⟩] }

/-- The server receives a packet (head of the soup) and applies it. -/
def Receive : Action LSt := fun t t' =>
  ∃ p ps, t.msgs = p :: ps ∧
    t' = { t with server := t.server + 1, msgs := ps }

def LNext : Action LSt := fun t t' => Send t t' ∨ Receive t t'

/-- Frame: all low-level state. -/
def lvars (t : LSt) : LSt := t

/-! ## Simulation -/

theorem initSim : InitSim abs LInit GInit := by
  intro t ht
  show t.server + t.msgs.length = 0
  rw [ht.2.1, ht.2.2]
  rfl

theorem stepSim : StepSim abs lvars LNext gvars GNext := by
  intro t t' hstep
  rcases hstep with hnext | hstut
  · rcases hnext with ⟨hg, ht'⟩ | ⟨p, ps, hmsgs, ht'⟩
    · -- Send: the abstract counter increments
      left
      show abs t < cap ∧ abs t' = abs t + 1
      refine ⟨hg, ?_⟩
      rw [ht']
      show t.server + (t.msgs ++ [(⟨0, 1, ()⟩ : Packet (Fin 2) Unit)]).length =
           t.server + t.msgs.length + 1
      simp only [List.length_append, List.length_singleton]
      omega
    · -- Receive: the abstract state is unchanged
      right
      show abs t' = abs t
      rw [ht']
      show t.server + 1 + ps.length = t.server + t.msgs.length
      rw [hmsgs]
      simp only [List.length_cons]
      omega
  · -- Stutter
    right
    have : t' = t := hstut
    rw [this]

/-- The transported invariant: the global increment count (applied +
in-flight) never exceeds `cap` — proved once at the high level. -/
theorem lsafety :
    Entails (tlaAnd (statePred LInit) (stutAlways LNext lvars))
      (always (statePred fun t => abs t ≤ cap)) :=
  refine_invariant initSim stepSim (fun n => n ≤ cap) gsafety

/-! ## Execution layer -/

inductive Lbl where
  | send | recv
deriving DecidableEq, Repr

def guard : Lbl → LSt → Prop
  | .send, t => abs t < cap
  | .recv, t => t.msgs ≠ []

instance : ∀ l t, Decidable (guard l t)
  | .send, _t => inferInstanceAs (Decidable (_ < _))
  | .recv, _t => inferInstanceAs (Decidable ¬ _)

def update : Lbl → LSt → LSt
  | .send, t => { t with client := t.client + 1, msgs := t.msgs ++ [⟨0, 1, ()⟩] }
  | .recv, t => { t with server := t.server + 1, msgs := t.msgs.tail }

def rel : Lbl → Action LSt
  | .send => Send
  | .recv => Receive

theorem fires : ∀ l t, guard l t → rel l t (update l t) := by
  intro l t hg
  cases l
  · exact ⟨hg, rfl⟩
  · cases hm : t.msgs with
    | nil => exact absurd hm hg
    | cons p ps =>
      exact ⟨p, ps, hm, by simp [update, hm]⟩

theorem det : ∀ l t t', rel l t t' → t' = update l t := by
  intro l t t' hrel
  cases l
  · exact hrel.2
  · obtain ⟨p, ps, hmsgs, ht'⟩ := hrel
    rw [ht']
    simp [update, hmsgs]

/-- The executable spec. -/
def execSpec : ExecSpec LSt where
  lbl := Lbl
  actions := ⟨rel, guard, update, fires, det⟩
  decGuard := fun _l _t => inferInstance

/-- The executable `next` refines the model-layer `LNext`. -/
theorem exec_next_refines : ∀ t t',
    StutAction execSpec.next (fun t => t) t t' → StutAction LNext lvars t t' := by
  intro t t' hstep
  rcases hstep with ⟨l, hrel⟩ | hstut
  · cases l
    · exact Or.inl (Or.inl hrel)
    · exact Or.inl (Or.inr hrel)
  · exact Or.inr hstut

/-- Model-level step preservation of the transported invariant. -/
theorem low_step_inv : ∀ t t',
    StutAction LNext lvars t t' → abs t ≤ cap → abs t' ≤ cap := by
  intro t t' hstep hinv
  rcases stepSim t t' hstep with hg | heq
  · obtain ⟨hlt, hval⟩ := hg
    exact hval ▸ Nat.succ_le_of_lt hlt
  · have h : abs t' = abs t := heq
    exact h ▸ hinv

/-- Every executable run respects the bound. -/
theorem exec_safe (t₀ : LSt) (ht₀ : LInit t₀) (trace : List Lbl) :
    abs (execSpec.run t₀ trace) ≤ cap := by
  apply execSpec.run_invariant LInit (fun t => abs t ≤ cap) _ _ t₀ ht₀ trace
  · intro t ht
    have h0 : abs t = 0 := initSim t ht
    show abs t ≤ cap
    omega
  · intro t t' hstep hinv
    exact low_step_inv t t' (exec_next_refines t t' hstep) hinv

-- Smoke run: send, send, a third send blocked by the cap guard, then recv.
#eval execSpec.run ⟨0, 0, []⟩ [.send, .send, .send, .recv]
  -- expect { client := 2, server := 1, msgs := [{ src := 0, dst := 1, body := () }] }

end Bft.Examples.BoundedCounter
