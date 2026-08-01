import Leslie.Examples.UtilityByzantine

set_option linter.unnecessarySeqFocus false

/-! # Binding Crusader Agreement

  Binding Crusader Agreement for `n` processes with at most `f` Byzantine
  faults, where `n > 3f`.

  Each process starts with a binary input (0 or 1). The protocol produces
  a decision in {0, 1, ⊥} satisfying:
  - **Validity**: If all correct processes have input b, then every correct
    process that decides, decides b.
  - **Agreement**: No correct process decides 0 and no other correct process
    decides 1. (⊥ is compatible with both.)

  The global state is composed of:
  - A **local state** per process (receipts, approval, echo/vote/decision)
  - A **message buffer** (pending messages in transit)
  - A **list of corrupted** processes

  ## Protocol
  1. Each process sends init(input) to all.
  2. On receiving f+1 init(b) (and not yet sent init(b)): send init(b) to all.
     (Input amplification.)
  3. On receiving n−f init(b): b is "approved". If not yet echoed: echo(b) to all.
  4. When both 0 and 1 are approved: send vote(⊥) to all.
  5. On receiving n−f echo(b): send vote(b) to all.
  6. On receiving n−f vote(b): decide b.
  7. When both 0 and 1 approved and received n−f vote: decide ⊥.
  8. A process decides at most once.

  Byzantine processes can inject arbitrary messages into the network.

  ## Proof architecture

  The file proves three top-level safety properties:

  - `bca_agreement` — no two correct processes decide opposite binary values.
  - `bca_validity`  — under unanimous input, every correct decision matches.
  - `bca_binding`   — once any correct process has decided, there is a fixed
    `b ∈ {0,1}` that no correct process will ever decide.

  All three follow from inductive invariants on the global state:

  1. `bca_inv` (10 conjuncts: budget, echo/vote traces, decision backing,
     vote agreement, echo backing, echo witness, conditional unanimity).
     Used for `bca_agreement` and `bca_validity`.

  2. `bound_inv` (8 conjuncts B1–B8) tracks a *ghost* field `boundValue`.
     `boundValue` records the protocol's "committed" outcome:
       - `none`           : nothing committed yet,
       - `some (some b)`  : binary value `b` committed,
       - `some none`      : ⊥ committed.
     `boundValue` is updated by `computeBound` after every transition: it
     becomes `some none` once enough ⊥-votes are seen, and `some (some b)`
     once enough binary `b`-votes are seen. Together with the invariant
     conjuncts B1–B8 it proves binding by ruling out conflicting decisions
     across the trace (`bound_binary_monotone` + `bca_binding`).

  ## File layout

  - State / messages / actions (lines ~40–310): basic protocol structure.
  - `bca` `ActionSpec` (~165): the four kinds of action with gates and
    transitions.
  - `bca_inv` (~373) and its proofs `bca_inv_init` / `bca_inv_step` (~430).
  - `bca_agreement` and `bca_validity` (~1748–1808): immediate corollaries
    of `bca_inv`.
  - `bound_inv` (~1848) and its (large) inductive proof
    `bound_inv_step` (~2160), structured as one block per action.
  - `bound_binary_monotone` (~3489) and the final `bca_binding` (~3540).
-/

open TLA

namespace BindingCrusaderAgreement

/-! ### Messages -/

inductive MsgType where
  | init | echo | vote
  deriving DecidableEq

/-- Values in the protocol: binary (0 or 1) or ⊥.
    Represented as Option Bool: some b for binary, none for ⊥. -/
abbrev Val := Option Bool

structure Message (n : Nat) where
  src : Fin n
  dst : Fin n
  type : MsgType
  val : Val
  deriving DecidableEq

/-! ### Local state -/

structure LocalState (n : Nat) where
  /-- `sent dst t v = true` iff this process has sent message (t, v) to dst. -/
  sent : Fin n → MsgType → Val → Bool
  /-- Received init(b) from process j. -/
  initRecv : Fin n → Bool → Bool
  /-- Whether value b is approved (received ≥ n−f init(b)). -/
  approved : Bool → Bool
  /-- Value echoed (at most one). -/
  echoed : Option Bool
  /-- Received echo(b) from process j. -/
  echoRecv : Fin n → Bool → Bool
  /-- `voted v = true` iff this process has sent vote(v). -/
  voted : Val → Bool
  /-- Received vote(v) from process j. -/
  voteRecv : Fin n → Val → Bool
  /-- Decision (at most one). -/
  decided : Option Val

/-! ### Global state -/

structure State (n : Nat) where
  /-- Per-process local state. -/
  local_ : Fin n → LocalState n
  /-- Network buffer: pending messages in transit. -/
  buffer : Message n → Bool
  /-- List of corrupted (Byzantine) processes. -/
  corrupted : List (Fin n)
  /-- **Ghost**: the "bound value" used to prove binding. Monotone:
      once set, frozen. `none` = undefined; `some (some b)` = bound to
      binary `b`; `some none` = bound to ⊥. Set by threshold crossings
      (see `computeBound`). Not observed by any action. -/
  boundValue : Option (Option Bool)

/-! ### Actions -/

inductive Action (n : Nat) where
  | corrupt (i : Fin n)
  | send (src dst : Fin n) (t : MsgType) (v : Val)
  | recv (src dst : Fin n) (t : MsgType) (v : Val)
  | decide (i : Fin n) (v : Val)

/-! ### Helpers -/

variable (n f : Nat)

def isCorrect (s : State n) (p : Fin n) : Prop := p ∉ s.corrupted

/-- Count of distinct sources from which init(b) was received. -/
def countInitRecv (ls : LocalState n) (b : Bool) : Nat :=
  (List.finRange n).filter (ls.initRecv · b) |>.length

/-- Count of distinct sources from which echo(b) was received. -/
def countEchoRecv (ls : LocalState n) (b : Bool) : Nat :=
  (List.finRange n).filter (ls.echoRecv · b) |>.length

/-- Count of distinct sources from which vote(v) was received. -/
def countVoteRecv (ls : LocalState n) (v : Val) : Nat :=
  (List.finRange n).filter (ls.voteRecv · v) |>.length

/-- Count of distinct sources from which any vote was received. -/
def countAnyVoteRecv (ls : LocalState n) : Nat :=
  (List.finRange n).filter (fun q =>
    ls.voteRecv q (some false) || ls.voteRecv q (some true) || ls.voteRecv q none) |>.length

def amplifyThreshold : Nat := f + 1
def approveThreshold : Nat := n - f
def echoThreshold : Nat := n - f
def returnThreshold : Nat := n - f

/-- Number of correct processes that have voted `v`. -/
def correctVoteCount (s : State n) (v : Val) : Nat :=
  ((List.finRange n).filter (fun p =>
    decide (p ∉ s.corrupted) && (s.local_ p).voted v)).length

/-- Ghost update rule for the bound value.
    - `some none` (⊥) is frozen.
    - `some (some b)` (binary) can still be upgraded to `some none` (⊥) if the
      ⊥ threshold is crossed, but never to the opposite binary value.
    - `none` can become anything: ⊥ if `|corrupted| + correct ⊥-voters > 2f`,
      otherwise a binary value `b` if `|corrupted| + correct b-voters > f`. -/
def computeBound (s : State n) : Option (Option Bool) :=
  if s.corrupted.length + correctVoteCount n s none > 2 * f then some none
  else match s.boundValue with
    | some bv => some bv
    | none =>
      if s.corrupted.length + correctVoteCount n s (some false) > f then some (some false)
      else if s.corrupted.length + correctVoteCount n s (some true) > f then some (some true)
      else none

/-- Default initial local state: everything empty/none/false. -/
def LocalState.init : LocalState n where
  sent := fun _ _ _ => false
  initRecv := fun _ _ => false
  approved := fun _ => false
  echoed := none
  echoRecv := fun _ _ => false
  voted := fun _ => false
  voteRecv := fun _ _ => false
  decided := none

/-! ### Specification -/

/-- Binding Crusader Agreement specification.
    Parameterized by the initial input of each process. -/
def bca (input : Fin n → Bool) : ActionSpec (State n) (Action n) where
  init := fun s =>
    (∀ p, s.local_ p = LocalState.init n) ∧
    (∀ m, s.buffer m = false) ∧
    s.corrupted = [] ∧
    s.boundValue = none
  actions := fun
    --
    -- === Adversary action ===
    --
    | .corrupt i => {
        gate := fun s =>
          isCorrect n s i ∧
          s.corrupted.length + 1 ≤ f
        transition := fun s s' =>
          let s₀ : State n := { s with corrupted := i :: s.corrupted }
          s' = { s₀ with boundValue := computeBound n f s₀ }
      }
    --
    -- === Send action ===
    --
    -- Byzantine processes can send any message at any time.
    -- Correct processes must follow the protocol:
    --   INIT: send init(input) initially, or init(b) on f+1 amplification
    --   ECHO: triggered by approval of b. A correct process echoes the
    --         same value `b` to *every* destination, but never echoes a
    --         second binary value (single-value, multi-destination).
    --   VOTE: triggered by n−f echoes for b, or both approved (vote ⊥).
    --         Same single-value, multi-destination semantics.
    --
    | .send src dst t mv => {
        gate := fun s =>
          src ∈ s.corrupted ∨
          (isCorrect n s src ∧ (s.local_ src).sent dst t mv = false ∧
            match t with
            | .init =>
              -- Init(b): own input, or amplification (f+1 init(b) received)
              match mv with
              | some b =>
                input src = b ∨
                countInitRecv n (s.local_ src) b ≥ amplifyThreshold f
              | none => False  -- init messages carry binary values only
            | .echo =>
              -- Echo(b): b is approved and either no value has been echoed
              -- yet, or the same value `b` was echoed previously (so this
              -- is a re-fire to a different destination).
              match mv with
              | some b =>
                (s.local_ src).approved b = true ∧
                ((s.local_ src).echoed = none ∨ (s.local_ src).echoed = some b)
              | none => False  -- echo messages carry binary values only
            | .vote =>
              -- Vote(v): every previous vote (if any) was for the same v.
              -- This permits multi-destination broadcast of the same value
              -- while still forbidding voting two distinct values.
              (∀ w, (s.local_ src).voted w = true → w = mv) ∧
              match mv with
              | some b =>
                countEchoRecv n (s.local_ src) b ≥ echoThreshold n f
              | none =>
                (s.local_ src).approved false = true ∧
                (s.local_ src).approved true = true)
        transition := fun s s' =>
          let msg : Message n := ⟨src, dst, t, mv⟩
          let s₀ : State n := { s with
            buffer := fun m => if m = msg then true else s.buffer m
            local_ := fun p => if p = src then
              { s.local_ src with
                sent := fun d t' w => if d = dst ∧ t' = t ∧ w = mv then true
                  else (s.local_ src).sent d t' w
                echoed := match t with
                  | .echo => match mv with
                    | some b => if src ∉ s.corrupted then some b
                                else (s.local_ src).echoed
                    | none => (s.local_ src).echoed
                  | _ => (s.local_ src).echoed
                voted := match t with
                  | .vote => if src ∉ s.corrupted
                    then fun w => if w = mv then true else (s.local_ src).voted w
                    else (s.local_ src).voted
                  | _ => (s.local_ src).voted }
              else s.local_ p }
          s' = { s₀ with boundValue := computeBound n f s₀ }
      }
    --
    -- === Receive action ===
    --
    | .recv src dst t mv => {
        gate := fun s =>
          s.buffer ⟨src, dst, t, mv⟩ = true
        transition := fun s s' =>
          let msg : Message n := ⟨src, dst, t, mv⟩
          let ls := s.local_ dst
          let s₀ : State n := { s with
            buffer := fun m => if m = msg then false else s.buffer m
            local_ := fun p => if p = dst then
              match t with
              | .init =>
                match mv with
                | some b =>
                  if ls.initRecv src b = false
                  then { ls with
                    initRecv := fun q w => if q = src ∧ w = b then true
                      else ls.initRecv q w
                    -- Auto-approve if threshold reached
                    approved := fun w => if w = b ∧
                      countInitRecv n ls b + 1 ≥ approveThreshold n f
                      then true else ls.approved w }
                  else ls
                | none => ls  -- ignore ⊥ init messages
              | .echo =>
                match mv with
                | some b =>
                  if ls.echoRecv src b = false
                  then { ls with
                    echoRecv := fun q w => if q = src ∧ w = b then true
                      else ls.echoRecv q w }
                  else ls
                | none => ls  -- ignore ⊥ echo messages
              | .vote =>
                if ls.voteRecv src mv = false
                then { ls with
                  voteRecv := fun q w => if q = src ∧ w = mv then true
                    else ls.voteRecv q w }
                else ls
              else s.local_ p }
          s' = { s₀ with boundValue := computeBound n f s₀ }
      }
    --
    -- === Decide action ===
    --
    -- Correct process decides v once it has sufficient votes.
    -- Decide b (binary): ≥ n−f vote(b) received.
    -- Decide ⊥: both 0 and 1 approved, and ≥ n−f votes (any value) received.
    --
    | .decide i mv => {
        gate := fun s =>
          isCorrect n s i ∧
          (s.local_ i).decided = none ∧
          match mv with
          | some b =>
            countVoteRecv n (s.local_ i) (some b) ≥ returnThreshold n f
          | none =>
            (s.local_ i).approved false = true ∧
            (s.local_ i).approved true = true ∧
            countAnyVoteRecv n (s.local_ i) ≥ returnThreshold n f
        transition := fun s s' =>
          let s₀ : State n := { s with
            local_ := fun p => if p = i
              then { s.local_ i with decided := some mv }
              else s.local_ p }
          s' = { s₀ with boundValue := computeBound n f s₀ }
      }

/-! ### Safety properties -/

/-- **Agreement**: if a correct process decides b ∈ {0,1}, then no correct
    process decides 1−b. (⊥ is compatible with both.) -/
def agreement (s : State n) : Prop :=
  ∀ p q (b : Bool),
    isCorrect n s p → isCorrect n s q →
    (s.local_ p).decided = some (some b) →
    (s.local_ q).decided ≠ some (some (!b))

/-- **Validity**: if all processes have input b, then no correct
    process decides a value different from b. -/
def validity (input : Fin n → Bool) (b : Bool) (s : State n) : Prop :=
  (∀ p, input p = b) →
  ∀ p v, isCorrect n s p → (s.local_ p).decided = some v → v = some b

/-- **Binding**: once any correct process has decided, there exists a fixed
    b ∈ {0,1} such that no correct process ever decides b.
    The ∃ b is outside the temporal scope — b is chosen once and holds forever. -/
def binding : pred (State n) :=
  fun e => (∃ k p v, isCorrect n (e k) p ∧ (e k |>.local_ p).decided = some v) →
  ∃ b : Bool, ∀ k q, isCorrect n (e k) q → (e k |>.local_ q).decided ≠ some (some b)

/-! ### Inductive invariant

    We prove **agreement** and **validity** from a single invariant `bca_inv`.
-/

/-- Local consistency under unanimity: if all correct inputs are b, then
    a correct process's local state is consistent with b. -/
def local_consistent (b : Bool) (ls : LocalState n) : Prop :=
  (∀ dst t w, ls.sent dst t w = true → match t with
    | .init => w = some b
    | .echo => w = some b
    | .vote => w = some b ∨ w = none) ∧
  (∀ w, ls.echoed = some w → w = b) ∧
  (∀ w, ls.voted (some w) = true → w = b) ∧
  (ls.approved (!b) = false) ∧
  (∀ w, ls.decided = some w → w = some b)

/-- Buffer consistency under unanimity: all pending messages from correct
    processes are consistent with b. -/
def buffer_consistent (b : Bool) (s : State n) : Prop :=
  ∀ m, s.buffer m = true → isCorrect n s m.src → match m.type with
    | .init => m.val = some b
    | .echo => m.val = some b
    | .vote => m.val = some b ∨ m.val = none

/-- The inductive invariant for BCA safety. Conjuncts:
    1. **Budget**: at most f processes corrupted
    2. **Echo trace**: echoRecv reflects echoed values of correct processes
    3. **Buffer echo trace**: pending ECHO messages reflect echoed values
    4. **Vote trace (binary)**: voteRecv(some b) reflects voted values of correct processes
    5. **Buffer vote trace (binary)**: pending VOTE(some b) messages reflect voted values
    6. **Conditional** (for validity): if all correct inputs are b, local states
       and buffer carry b
    7. **Decision backing**: decided(some b) → ≥ n−f vote(some b) sources
    8. **Vote agreement (binary)**: all binary votes from correct processes agree
    9. **Echo backing**: every correct binary vote is backed by ≥ n−f echo sources
    10. **Echo witness**: if any correct process voted(some b), some process has
        ≥ n−f echo receipts for b -/
def bca_inv (input : Fin n → Bool) (s : State n) : Prop :=
  -- 1. Budget
  s.corrupted.length ≤ f ∧
  -- 2. Echo trace
  (∀ p q b, isCorrect n s p →
    (s.local_ q).echoRecv p b = true → (s.local_ p).echoed = some b) ∧
  -- 3. Buffer echo trace
  (∀ p dst b, isCorrect n s p →
    s.buffer ⟨p, dst, .echo, some b⟩ = true → (s.local_ p).echoed = some b) ∧
  -- 4. Vote trace (binary)
  (∀ p q b, isCorrect n s q →
    (s.local_ p).voteRecv q (some b) = true → (s.local_ q).voted (some b) = true) ∧
  -- 5. Buffer vote trace (binary)
  (∀ p dst b, isCorrect n s p →
    s.buffer ⟨p, dst, .vote, some b⟩ = true → (s.local_ p).voted (some b) = true) ∧
  -- 6. Conditional (validity): hypothesis is state-independent (all inputs, not just correct)
  -- Third clause: under unanimity, initRecv(!b) entries come only from corrupt sources
  ((∀ p, input p = true) →
    (∀ p, isCorrect n s p → local_consistent n true (s.local_ p)) ∧
    buffer_consistent n true s ∧
    (∀ q r, isCorrect n s q → (s.local_ q).initRecv r false = true → r ∈ s.corrupted)) ∧
  ((∀ p, input p = false) →
    (∀ p, isCorrect n s p → local_consistent n false (s.local_ p)) ∧
    buffer_consistent n false s ∧
    (∀ q r, isCorrect n s q → (s.local_ q).initRecv r true = true → r ∈ s.corrupted)) ∧
  -- 7. Decision backing
  (∀ p b, (s.local_ p).decided = some (some b) →
    countVoteRecv n (s.local_ p) (some b) ≥ returnThreshold n f) ∧
  -- 8. Vote agreement (binary): all correct binary votes are for the same value
  (∀ p q b₁ b₂, isCorrect n s p → isCorrect n s q →
    (s.local_ p).voted (some b₁) = true → (s.local_ q).voted (some b₂) = true → b₁ = b₂) ∧
  -- 9. Echo backing: correct binary vote → ≥ n−f echo sources
  (∀ p b, isCorrect n s p →
    (s.local_ p).voted (some b) = true →
    countEchoRecv n (s.local_ p) b ≥ echoThreshold n f) ∧
  -- 10. Echo witness: if any correct voted(some b), some process has ≥ n−f echo receipts
  (∀ b, (∃ p, isCorrect n s p ∧ (s.local_ p).voted (some b) = true) →
    ∃ q, countEchoRecv n (s.local_ q) b ≥ echoThreshold n f) ∧
  -- 11. Count → approved: crossing the approve threshold sets approved.
  --     Guarded by n > f so the threshold is positive.
  (n > f → ∀ p b, countInitRecv n (s.local_ p) b ≥ approveThreshold n f →
    (s.local_ p).approved b = true)

/-! ### Invariant proofs

  Two parts:
  - `bca_inv_init`: every initial state satisfies the invariant — most
    conjuncts are vacuous since nothing has been sent, voted, or decided.
  - `bca_inv_step`: every action preserves the invariant. The proof is a
    big case split on the action (`corrupt`, `send`, `recv`, `decide`),
    refined by `t : MsgType` and `mv : Val` for `send`/`recv`. Each leaf
    discharges all 10 conjuncts of `bca_inv` for the post-state.
-/

/-- Echo quorum intersection specialized to BCA's state. -/
private theorem bca_echo_quorum_intersection {n f : Nat} (hn : n > 3 * f)
    (s : State n) (p1 p2 : Fin n) (v w : Bool)
    (hbudget : s.corrupted.length ≤ f)
    (hetrace : ∀ p q b, isCorrect n s p →
      (s.local_ q).echoRecv p b = true → (s.local_ p).echoed = some b)
    (hv : countEchoRecv n (s.local_ p1) v ≥ echoThreshold n f)
    (hw : countEchoRecv n (s.local_ p2) w ≥ echoThreshold n f) :
    v = w :=
  _root_.echo_quorum_intersection hn v w p1 p2
    (fun p q b => (s.local_ p).echoRecv q b)
    (fun p => (s.local_ p).echoed)
    s.corrupted hbudget hetrace hv hw

-- All conjuncts vacuously true: sent/voted/echoRecv/voteRecv all false,
-- buffer empty, decided = none.
theorem bca_inv_init (input : Fin n → Bool) :
    ∀ s, (bca n f input).init s → bca_inv n f input s := by
  intro s ⟨hlocal, hbuf, hcorr⟩
  refine ⟨by simp [hcorr], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p q b _ h ; simp [hlocal, LocalState.init] at h
  · intro p dst b _ h ; simp [hbuf] at h
  · intro p q b _ h ; simp [hlocal, LocalState.init] at h
  · intro p dst b _ h ; simp [hbuf] at h
  · intro _ ; exact ⟨fun p _ => by simp [hlocal, LocalState.init, local_consistent],
      fun m hm _ => by simp [hbuf] at hm,
      fun q r _ h => by simp [hlocal, LocalState.init] at h⟩
  · intro _ ; exact ⟨fun p _ => by simp [hlocal, LocalState.init, local_consistent],
      fun m hm _ => by simp [hbuf] at hm,
      fun q r _ h => by simp [hlocal, LocalState.init] at h⟩
  · intro p b h ; simp [hlocal, LocalState.init] at h
  · intro p q b₁ b₂ _ _ hvp _ ; simp [hlocal, LocalState.init] at hvp
  · intro p b _ hvp ; simp [hlocal, LocalState.init] at hvp
  · intro b ⟨p, _, hvp⟩ ; simp [hlocal, LocalState.init] at hvp
  · -- 11. count → approved: vacuous, count is 0 in init state
    intro hnf p b hcnt
    exfalso
    have : countInitRecv n (s.local_ p) b = 0 := by
      simp [hlocal, LocalState.init, countInitRecv]
    rw [this] at hcnt
    unfold approveThreshold at hcnt
    omega

/- Inductive step: every BCA action preserves `bca_inv`.

   The proof case-splits on `action`:
   - `corrupt i`  — adds `i` to the corrupted list. Most invariants are
     monotone in `corrupted`; the budget conjunct uses the gate
     `|corrupted| + 1 ≤ f`.
   - `send src dst t mv` — extends the message buffer and (if `src` is
     correct) extends `src`'s `sent`/`echoed`/`voted` fields. The trace
     and backing conjuncts use the gate's threshold conditions; vote
     agreement uses `echo_quorum_intersection`.
   - `recv src dst t mv` — bumps the receiver's `*Recv` field and may
     also flip `approved` for init. Echo/vote traces are restored from
     `bca_inv`'s buffer-trace conjuncts.
   - `decide i mv` — only changes `decided`; all conjuncts unrelated to
     `decided` are unchanged, and decision backing comes from the gate.
-/

/-- Counting helper: if `ls.initRecv src b = false`, then the count of
    sources for `b` after adding `src` is exactly one more than before. -/
private theorem countInitRecv_succ_of_new {n : Nat} (ls : LocalState n)
    (src : Fin n) (b : Bool) (hnew : ls.initRecv src b = false) :
    ((List.finRange n).filter
      (fun q => decide (q = src) || ls.initRecv q b)).length =
    ((List.finRange n).filter (fun q => ls.initRecv q b)).length + 1 := by
  have aux : ∀ (l : List (Fin n)), src ∈ l → l.Nodup →
      (l.filter (fun q => decide (q = src) || ls.initRecv q b)).length =
      (l.filter (fun q => ls.initRecv q b)).length + 1 := by
    intro l ; induction l with
    | nil => intro h ; exact absurd h (by simp)
    | cons a t ih =>
      intro hin hnd
      simp only [List.filter_cons]
      rcases List.mem_cons.mp hin with rfl | hmem
      · -- a = src; for q ∈ t, q ≠ src, so the new filter agrees with the old.
        have hsrc_notin : src ∉ t := (List.nodup_cons.mp hnd).1
        simp [hnew]
        have heq : ∀ q ∈ t,
            (decide (q = src) || ls.initRecv q b) = ls.initRecv q b := by
          intro q hq
          have : q ≠ src := fun h => hsrc_notin (h ▸ hq)
          simp [this]
        rw [List.filter_congr heq]
      · have hnd_t := (List.nodup_cons.mp hnd).2
        have hane : a ≠ src := by
          intro h ; subst h ; exact (List.nodup_cons.mp hnd).1 hmem
        simp [hane]
        cases hra : ls.initRecv a b
        · simp ; exact ih hmem hnd_t
        · simp ; rw [ih hmem hnd_t]
  exact aux (List.finRange n) (List.mem_finRange src) (finRange_nodup n)

set_option maxHeartbeats 800000 in
theorem bca_inv_step (input : Fin n → Bool) (hn : n > 3 * f) :
    ∀ s s', (∃ i, ((bca n f input).actions i).fires s s') →
    bca_inv n f input s → bca_inv n f input s' := by
  intro s s' ⟨action, hfire⟩ ⟨hbudget, hetrace, hbet, hvtrace, hbvt, hcond_t, hcond_f,
     hvback, hvagree, hecho_back, hecho_wit, hcount_app⟩
  simp [bca, GatedAction.fires] at hfire
  obtain ⟨hgate, htrans⟩ := hfire
  cases action with
  | corrupt i =>
    subst htrans
    have hcw : ∀ q, isCorrect n { s with corrupted := i :: s.corrupted } q →
        isCorrect n s q := fun q hq h => hq (List.mem_cons_of_mem i h)
    exact ⟨by simp [List.length_cons] ; exact hgate.2,
      fun p q b hp h => hetrace p q b (hcw p hp) h,
      fun p d b hp h => hbet p d b (hcw p hp) h,
      fun p q b hp h => hvtrace p q b (hcw q hp) h,
      fun p d b hp h => hbvt p d b (hcw p hp) h,
      fun hs => let ⟨hl, hb, hic⟩ := hcond_t hs ;
        ⟨fun p hp => hl p (hcw p hp), fun m hm hsrc => hb m hm (hcw m.src hsrc),
         fun q r hq h => List.mem_cons_of_mem i (hic q r (hcw q hq) h)⟩,
      fun hs => let ⟨hl, hb, hic⟩ := hcond_f hs ;
        ⟨fun p hp => hl p (hcw p hp), fun m hm hsrc => hb m hm (hcw m.src hsrc),
         fun q r hq h => List.mem_cons_of_mem i (hic q r (hcw q hq) h)⟩,
      fun p b h => hvback p b h,
      fun p q b₁ b₂ hp hq h1 h2 => hvagree p q b₁ b₂ (hcw p hp) (hcw q hq) h1 h2,
      fun p b hp h => hecho_back p b (hcw p hp) h,
      fun b ⟨p, hp, h⟩ => hecho_wit b ⟨p, hcw p hp, h⟩,
      fun hnf p b h => hcount_app hnf p b h⟩
  | send src dst t mv =>
    subst htrans
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hbudget -- 1. budget
    · -- 2. echo trace: echoRecv unchanged; echoed may change at src for echo
      intro p q b hp h
      have h' : (s.local_ q).echoRecv p b = true := by
        by_cases hq : q = src
        · simp [hq] at h ; rw [hq]; exact h
        · simp [hq] at h ; exact h
      have hold := hetrace p q b hp h'
      by_cases hpsrc : p = src
      · subst hpsrc ; cases t with
        | init => simp ; exact hold
        | vote =>
          by_cases hc : p ∈ s.corrupted
          · simp [hc] ; exact hold
          · simp [hc] ; exact hold
        | echo =>
          by_cases hc : p ∈ s.corrupted
          · exact absurd hc hp
          · simp [hc] ; cases mv with
            | none => exact hold
            | some bv =>
              -- gate now allows re-fire when echoed = some bv. From hold
              -- (echoed = some b) and the gate disjunct we conclude b = bv,
              -- so the new echoed (some bv) equals the required some b.
              rcases hgate with hmem | ⟨_, _, _, hech⟩
              · exact absurd hmem hp
              · rcases hech with hnone | hsome
                · rw [hold] at hnone ; exact absurd hnone (by simp)
                · rw [hold] at hsome ; injection hsome with hbv ; rw [hbv]
      · simp [hpsrc] ; exact hold
    · -- 3. buffer echo trace
      intro p d b hp hbuf ; simp at hbuf
      rcases hbuf with ⟨rfl, rfl, rfl, rfl⟩ | hold
      · -- new msg = ⟨p, d, .echo, some b⟩ after substitution
        by_cases hc : p ∈ s.corrupted
        · exact absurd hc hp
        · simp [hc]
      · -- old msg in buffer
        have := hbet p d b hp hold
        by_cases hpsrc : p = src
        · subst hpsrc ; cases t with
          | init => simp ; exact this
          | vote =>
            by_cases hc : p ∈ s.corrupted
            · simp [hc] ; exact this
            · simp [hc] ; exact this
          | echo =>
            by_cases hc : p ∈ s.corrupted
            · exact absurd hc hp
            · cases mv with
              | none => simp; exact this
              | some bv =>
                rcases hgate with hmem | ⟨_, _, _, hech⟩
                · exact absurd hmem hp
                · rcases hech with hnone | hsome
                  · rw [this] at hnone ; exact absurd hnone (by simp)
                  · rw [this] at hsome ; injection hsome with hbv
                    simp [hbv, hc]
        · simp [hpsrc] ; exact this
    · -- 4. vote trace: voteRecv unchanged; voted changes at src for vote
      intro p q b hp h
      have h' : (s.local_ p).voteRecv q (some b) = true := by
        by_cases hp' : p = src
        · rw [hp'] ; simp [hp'] at h ; exact h
        · simp [hp'] at h ; exact h
      have hold := hvtrace p q b hp h'
      by_cases hqsrc : q = src
      · subst hqsrc ; cases t with
        | init => simp ; exact hold
        | echo => simp ; exact hold
        | vote =>
          by_cases hc : q ∈ s.corrupted
          · simp [hc] ; exact hold
          · simp [hc] ; by_cases hv : (some b : Val) = mv <;> simp [hv, hold]
      · simp [hqsrc] ; exact hold
    · -- 5. buffer vote trace: new msg or old
      intro p d b hp hbuf ; simp at hbuf
      rcases hbuf with ⟨rfl, rfl, rfl, rfl⟩ | hold
      · -- new msg: must be vote type with some b
        by_cases hc : p ∈ s.corrupted
        · exact absurd hc hp
        · simp [hc]
      · have := hbvt p d b hp hold
        by_cases hpsrc : p = src
        · subst hpsrc ; cases t with
          | init => simp ; exact this
          | echo =>
            by_cases hc : p ∈ s.corrupted
            · simp [hc] ; exact this
            · cases mv with
              | none => simp; exact this
              | some bv =>
                -- gate: echoed = none, but if p already voted, need voted preserved
                -- voted unchanged by echo send for correct p
                simp [hc] ; exact this
          | vote =>
            by_cases hc : p ∈ s.corrupted
            · simp [hc] ; exact this
            · simp [hc] ; by_cases hv : (some b : Val) = mv <;> simp [hv, this]
        · simp [hpsrc] ; exact this
    · -- 6a. conditional (true)
      intro hs
      obtain ⟨hl, hb, hic⟩ := hcond_t hs
      have hcount_false : ∀ q, isCorrect n s q →
          countInitRecv n (s.local_ q) false ≤ s.corrupted.length := fun q hq => by
        unfold countInitRecv
        exact nodup_sub_length
          ((finRange_nodup n).sublist List.filter_sublist)
          (fun x hx => by simp [List.mem_filter] at hx ; exact hic q x hq hx)
      -- b2 = false ruled out for any correct x sending init/echo/vote(some _)
      have hecho_val : ∀ x b2, (s.local_ x).approved b2 = true →
          isCorrect n s x → b2 = true := fun x b2 happroved hp => by
        cases b2 with
        | true => rfl
        | false =>
          have h2 : (s.local_ x).approved false = false := by
            have := (hl x hp).2.2.2.1 ; simpa using this
          rw [h2] at happroved ; exact absurd happroved (by decide)
      have hvote_val : ∀ x b2, countEchoRecv n (s.local_ x) b2 ≥ echoThreshold n f →
          isCorrect n s x → b2 = true := fun x b2 hecount hp => by
        cases b2 with
        | true => rfl
        | false =>
          exfalso
          have hgt : s.corrupted.length < countEchoRecv n (s.local_ x) false := by
            calc s.corrupted.length ≤ f := hbudget
              _ < n - f := by omega
              _ ≤ _ := hecount
          obtain ⟨r, hr_recv, hr_corr⟩ := pigeonhole_filter
            ((s.local_ x).echoRecv · false) s.corrupted hgt
          have hr_echoed := hetrace r x false hr_corr hr_recv
          have := (hl r hr_corr).2.1 false hr_echoed
          exact absurd this (by decide)
      have hinit_val : ∀ x b2, (input x = b2 ∨
          countInitRecv n (s.local_ x) b2 ≥ amplifyThreshold f) →
          isCorrect n s x → b2 = true := fun x b2 hinit hp => by
        cases b2 with
        | true => rfl
        | false =>
          exfalso
          rcases hinit with heq | hcount
          · rw [hs x] at heq ; exact absurd heq (by decide)
          · have := hcount_false x hp ; unfold amplifyThreshold at hcount ; omega
      refine ⟨?_, ?_, ?_⟩
      · -- local_consistent for s'.local_ p
        intro p hp
        by_cases hpsrc : p = src
        · subst hpsrc
          have hcons := hl p hp
          obtain ⟨hsent, hech, hvot, happ, hdec⟩ := hcons
          simp only [local_consistent]
          refine ⟨?_, ?_, ?_, happ, hdec⟩
          · -- sent
            intro dst' t' w' h
            simp at h
            by_cases hnew : dst' = dst ∧ t' = t ∧ w' = mv
            · obtain ⟨hd, ht, hw⟩ := hnew
              subst hd ; subst ht ; subst hw
              cases t' with
              | init =>
                cases w' with
                | some b2 =>
                  rcases hgate with hmem | ⟨_, _, hinit⟩
                  · exact absurd hmem hp
                  · rw [hinit_val p b2 hinit hp]
                | none =>
                  rcases hgate with hmem | ⟨_, _, hg⟩
                  · exact absurd hmem hp
                  · exact absurd hg (by simp)
              | echo =>
                cases w' with
                | some b2 =>
                  rcases hgate with hmem | ⟨_, _, happroved, _⟩
                  · exact absurd hmem hp
                  · rw [hecho_val p b2 happroved hp]
                | none =>
                  rcases hgate with hmem | ⟨_, _, hg⟩
                  · exact absurd hmem hp
                  · exact absurd hg (by simp)
              | vote =>
                cases w' with
                | some b2 =>
                  rcases hgate with hmem | ⟨_, _, _, hecount⟩
                  · exact absurd hmem hp
                  · left ; rw [hvote_val p b2 hecount hp]
                | none => right ; rfl
            · simp [hnew] at h ; exact hsent dst' t' w' h
          · -- echoed
            intro w hw
            cases t with
            | init => simp at hw ; exact hech w hw
            | echo =>
              cases mv with
              | some b2 =>
                by_cases hc : p ∈ s.corrupted
                · exact absurd hc hp
                · simp [hc] at hw
                  rcases hgate with hmem | ⟨_, _, happroved, _⟩
                  · exact absurd hmem hp
                  · have hb2 := hecho_val p b2 happroved hp
                    subst hb2 ; simp at hw ; exact hw
              | none => simp at hw ; exact hech w hw
            | vote => simp at hw ; exact hech w hw
          · -- voted
            intro w hw
            cases t with
            | init => simp at hw ; exact hvot w hw
            | echo => simp at hw ; exact hvot w hw
            | vote =>
              by_cases hc : p ∈ s.corrupted
              · exact absurd hc hp
              · simp [hc] at hw
                by_cases heq : (some w : Val) = mv
                · rcases hgate with hmem | ⟨_, _, _, hecount⟩
                  · exact absurd hmem hp
                  · rw [← heq] at hecount ; simp at hecount
                    rw [hvote_val p w hecount hp]
                · simp [heq] at hw ; exact hvot w hw
        · simp [hpsrc] ; exact hl p hp
      · -- buffer_consistent
        intro m hm hsrc_c
        simp at hm
        rcases hm with ⟨rfl, rfl, rfl, rfl⟩ | hm_old
        · cases t with
          | init =>
            cases mv with
            | some b2 =>
              rcases hgate with hmem | ⟨_, _, hinit⟩
              · exact absurd hmem hsrc_c
              · rw [hinit_val src b2 hinit hsrc_c]
            | none =>
              rcases hgate with hmem | ⟨_, _, hg⟩
              · exact absurd hmem hsrc_c
              · exact absurd hg (by simp)
          | echo =>
            cases mv with
            | some b2 =>
              rcases hgate with hmem | ⟨_, _, happroved, _⟩
              · exact absurd hmem hsrc_c
              · rw [hecho_val src b2 happroved hsrc_c]
            | none =>
              rcases hgate with hmem | ⟨_, _, hg⟩
              · exact absurd hmem hsrc_c
              · exact absurd hg (by simp)
          | vote =>
            cases mv with
            | some b2 =>
              rcases hgate with hmem | ⟨_, _, _, hecount⟩
              · exact absurd hmem hsrc_c
              · left ; rw [hvote_val src b2 hecount hsrc_c]
            | none => right ; rfl
        · exact hb m hm_old hsrc_c
      · -- hic: initRecv unchanged by send
        intro q r hq h
        by_cases hqsrc : q = src
        · rw [hqsrc] at h hq ; simp at h ; exact hic src r hq h
        · simp [hqsrc] at h ; exact hic q r hq h
    · -- 6b. conditional (false): mirror of 6a
      intro hs
      obtain ⟨hl, hb, hic⟩ := hcond_f hs
      have hcount_true : ∀ q, isCorrect n s q →
          countInitRecv n (s.local_ q) true ≤ s.corrupted.length := fun q hq => by
        unfold countInitRecv
        exact nodup_sub_length
          ((finRange_nodup n).sublist List.filter_sublist)
          (fun x hx => by simp [List.mem_filter] at hx ; exact hic q x hq hx)
      have hecho_val : ∀ x b2, (s.local_ x).approved b2 = true →
          isCorrect n s x → b2 = false := fun x b2 happroved hp => by
        cases b2 with
        | false => rfl
        | true =>
          have h2 : (s.local_ x).approved true = false := by
            have := (hl x hp).2.2.2.1 ; simpa using this
          rw [h2] at happroved ; exact absurd happroved (by decide)
      have hvote_val : ∀ x b2, countEchoRecv n (s.local_ x) b2 ≥ echoThreshold n f →
          isCorrect n s x → b2 = false := fun x b2 hecount hp => by
        cases b2 with
        | false => rfl
        | true =>
          exfalso
          have hgt : s.corrupted.length < countEchoRecv n (s.local_ x) true := by
            calc s.corrupted.length ≤ f := hbudget
              _ < n - f := by omega
              _ ≤ _ := hecount
          obtain ⟨r, hr_recv, hr_corr⟩ := pigeonhole_filter
            ((s.local_ x).echoRecv · true) s.corrupted hgt
          have hr_echoed := hetrace r x true hr_corr hr_recv
          have := (hl r hr_corr).2.1 true hr_echoed
          exact absurd this (by decide)
      have hinit_val : ∀ x b2, (input x = b2 ∨
          countInitRecv n (s.local_ x) b2 ≥ amplifyThreshold f) →
          isCorrect n s x → b2 = false := fun x b2 hinit hp => by
        cases b2 with
        | false => rfl
        | true =>
          exfalso
          rcases hinit with heq | hcount
          · rw [hs x] at heq ; exact absurd heq (by decide)
          · have := hcount_true x hp ; unfold amplifyThreshold at hcount ; omega
      refine ⟨?_, ?_, ?_⟩
      · intro p hp
        by_cases hpsrc : p = src
        · subst hpsrc
          have hcons := hl p hp
          obtain ⟨hsent, hech, hvot, happ, hdec⟩ := hcons
          simp only [local_consistent]
          refine ⟨?_, ?_, ?_, happ, hdec⟩
          · intro dst' t' w' h
            simp at h
            by_cases hnew : dst' = dst ∧ t' = t ∧ w' = mv
            · obtain ⟨hd, ht, hw⟩ := hnew
              subst hd ; subst ht ; subst hw
              cases t' with
              | init =>
                cases w' with
                | some b2 =>
                  rcases hgate with hmem | ⟨_, _, hinit⟩
                  · exact absurd hmem hp
                  · rw [hinit_val p b2 hinit hp]
                | none =>
                  rcases hgate with hmem | ⟨_, _, hg⟩
                  · exact absurd hmem hp
                  · exact absurd hg (by simp)
              | echo =>
                cases w' with
                | some b2 =>
                  rcases hgate with hmem | ⟨_, _, happroved, _⟩
                  · exact absurd hmem hp
                  · rw [hecho_val p b2 happroved hp]
                | none =>
                  rcases hgate with hmem | ⟨_, _, hg⟩
                  · exact absurd hmem hp
                  · exact absurd hg (by simp)
              | vote =>
                cases w' with
                | some b2 =>
                  rcases hgate with hmem | ⟨_, _, _, hecount⟩
                  · exact absurd hmem hp
                  · left ; rw [hvote_val p b2 hecount hp]
                | none => right ; rfl
            · simp [hnew] at h ; exact hsent dst' t' w' h
          · intro w hw
            cases t with
            | init => simp at hw ; exact hech w hw
            | echo =>
              cases mv with
              | some b2 =>
                by_cases hc : p ∈ s.corrupted
                · exact absurd hc hp
                · simp [hc] at hw
                  rcases hgate with hmem | ⟨_, _, happroved, _⟩
                  · exact absurd hmem hp
                  · have hb2 := hecho_val p b2 happroved hp
                    subst hb2 ; simp at hw ; exact hw
              | none => simp at hw ; exact hech w hw
            | vote => simp at hw ; exact hech w hw
          · intro w hw
            cases t with
            | init => simp at hw ; exact hvot w hw
            | echo => simp at hw ; exact hvot w hw
            | vote =>
              by_cases hc : p ∈ s.corrupted
              · exact absurd hc hp
              · simp [hc] at hw
                by_cases heq : (some w : Val) = mv
                · rcases hgate with hmem | ⟨_, _, _, hecount⟩
                  · exact absurd hmem hp
                  · rw [← heq] at hecount ; simp at hecount
                    rw [hvote_val p w hecount hp]
                · simp [heq] at hw ; exact hvot w hw
        · simp [hpsrc] ; exact hl p hp
      · intro m hm hsrc_c
        simp at hm
        rcases hm with ⟨rfl, rfl, rfl, rfl⟩ | hm_old
        · cases t with
          | init =>
            cases mv with
            | some b2 =>
              rcases hgate with hmem | ⟨_, _, hinit⟩
              · exact absurd hmem hsrc_c
              · rw [hinit_val src b2 hinit hsrc_c]
            | none =>
              rcases hgate with hmem | ⟨_, _, hg⟩
              · exact absurd hmem hsrc_c
              · exact absurd hg (by simp)
          | echo =>
            cases mv with
            | some b2 =>
              rcases hgate with hmem | ⟨_, _, happroved, _⟩
              · exact absurd hmem hsrc_c
              · rw [hecho_val src b2 happroved hsrc_c]
            | none =>
              rcases hgate with hmem | ⟨_, _, hg⟩
              · exact absurd hmem hsrc_c
              · exact absurd hg (by simp)
          | vote =>
            cases mv with
            | some b2 =>
              rcases hgate with hmem | ⟨_, _, _, hecount⟩
              · exact absurd hmem hsrc_c
              · left ; rw [hvote_val src b2 hecount hsrc_c]
            | none => right ; rfl
        · exact hb m hm_old hsrc_c
      · intro q r hq h
        by_cases hqsrc : q = src
        · rw [hqsrc] at h hq ; simp at h ; exact hic src r hq h
        · simp [hqsrc] at h ; exact hic q r hq h
    · -- 7. decision backing: decided/voteRecv unchanged by send
      intro p b hdec
      by_cases hpsrc : p = src
      · subst hpsrc ; simp at hdec ⊢ ; exact hvback p b hdec
      · simp [hpsrc] at hdec ⊢ ; exact hvback p b hdec
    · -- 8. vote agreement: new binary vote at src must agree with old votes
      intro p q b₁ b₂ hp hq h1 h2
      -- Extract old voted or detect new vote
      -- Case 1: new vote from src with gate giving echo count
      -- Case 2: old votes → use old hvagree
      -- For p:
      have h1_cases : (p = src ∧ some b₁ = mv ∧ t = .vote ∧ p ∉ s.corrupted) ∨
          (s.local_ p).voted (some b₁) = true := by
        by_cases hpsrc : p = src
        · subst hpsrc ; cases t with
          | init => right ; simp at h1 ; exact h1
          | echo => right ; simp at h1 ; exact h1
          | vote =>
            by_cases hc : p ∈ s.corrupted
            · right ; simp [hc] at h1 ; exact h1
            · simp [hc] at h1
              rcases h1 with rfl | hold
              · left ; exact ⟨rfl, rfl, rfl, hc⟩
              · right ; exact hold
        · right ; simp [hpsrc] at h1 ; exact h1
      have h2_cases : (q = src ∧ some b₂ = mv ∧ t = .vote ∧ q ∉ s.corrupted) ∨
          (s.local_ q).voted (some b₂) = true := by
        by_cases hqsrc : q = src
        · subst hqsrc ; cases t with
          | init => right ; simp at h2 ; exact h2
          | echo => right ; simp at h2 ; exact h2
          | vote =>
            by_cases hc : q ∈ s.corrupted
            · right ; simp [hc] at h2 ; exact h2
            · simp [hc] at h2
              rcases h2 with rfl | hold
              · left ; exact ⟨rfl, rfl, rfl, hc⟩
              · right ; exact hold
        · right ; simp [hqsrc] at h2 ; exact h2
      -- Four sub-cases
      rcases h1_cases with ⟨rfl, hmv1, ht1, hc1⟩ | h1_old
      · rcases h2_cases with ⟨hq_eq, hmv2, _, _⟩ | h2_old
        · -- Both new votes: same src, so b₁ = b₂ from mv
          rw [← hmv1] at hmv2 ; injection hmv2 with heq ; exact heq.symm
        · -- p = src new, q old. Need b₁ = b₂.
          subst ht1
          -- gate: corrupt src (contradicts hc1) or echo count for b₁
          rcases hgate with hmem | ⟨_, _, _, hecho⟩
          · exact absurd hmem hc1
          · -- mv = some b₁, gate uses some b₁ branch
            rw [← hmv1] at hecho ; simp at hecho
            exact bca_echo_quorum_intersection hn s p q b₁ b₂ hbudget hetrace hecho
              (hecho_back q b₂ hq h2_old)
      · rcases h2_cases with ⟨rfl, hmv2, ht2, hc2⟩ | h2_old
        · -- p old, q = src new. Symmetric.
          subst ht2
          rcases hgate with hmem | ⟨_, _, _, hecho⟩
          · exact absurd hmem hc2
          · rw [← hmv2] at hecho ; simp at hecho
            exact bca_echo_quorum_intersection hn s p q b₁ b₂ hbudget hetrace
              (hecho_back p b₁ hp h1_old) hecho
        · -- Both old
          exact hvagree p q b₁ b₂ hp hq h1_old h2_old
    · -- 9. echo backing: correct voted(some b) → n-f echo(b)
      intro p b hp hvp
      -- Extract old voted or new voted
      by_cases hpsrc : p = src
      · subst hpsrc
        cases t with
        | init => simp at hvp ⊢ ; exact hecho_back p b hp hvp
        | echo => simp at hvp ⊢ ; exact hecho_back p b hp hvp
        | vote =>
          -- voted may change: new or old
          simp at hvp
          by_cases hc : p ∈ s.corrupted
          · exact absurd hc hp
          · simp [hc] at hvp
            rcases hvp with ⟨rfl, rfl⟩ | hold
            · -- new vote(some b): gate gives echo count
              simp [hc] at hgate
              simp only [countEchoRecv] ; simp ; exact hgate.2.2.2
            · -- old vote: IH
              have := hecho_back p b hp hold
              simp only [countEchoRecv] at this ⊢ ; simp ; exact this
      · simp [hpsrc] at hvp ⊢ ; exact hecho_back p b hp hvp
    · -- 10. echo witness
      intro b ⟨p, hp, hvp⟩
      by_cases hpsrc : p = src
      · subst hpsrc
        cases t with
        | init => simp at hvp ; obtain ⟨q, hq⟩ := hecho_wit b ⟨p, hp, hvp⟩
                  refine ⟨q, ?_⟩
                  simp only [countEchoRecv] at hq ⊢
                  by_cases h : q = p
                  · subst h ; simpa using hq
                  · simpa [h] using hq
        | echo => simp at hvp ; obtain ⟨q, hq⟩ := hecho_wit b ⟨p, hp, hvp⟩
                  refine ⟨q, ?_⟩
                  simp only [countEchoRecv] at hq ⊢
                  by_cases h : q = p
                  · subst h ; simpa using hq
                  · simpa [h] using hq
        | vote =>
          simp at hvp
          by_cases hc : p ∈ s.corrupted
          · exact absurd hc hp
          · simp [hc] at hvp
            rcases hvp with ⟨rfl, rfl⟩ | hold
            · -- new vote: src is echo witness (gate gives count)
              simp [hc] at hgate
              exact ⟨p, by simp only [countEchoRecv] ; simp ; exact hgate.2.2.2⟩
            · obtain ⟨q, hq⟩ := hecho_wit b ⟨p, hp, hold⟩
              refine ⟨q, ?_⟩
              simp only [countEchoRecv] at hq ⊢
              by_cases h : q = p
              · subst h ; simpa using hq
              · simpa [h] using hq
      · simp [hpsrc] at hvp
        obtain ⟨q, hq⟩ := hecho_wit b ⟨p, hp, hvp⟩
        refine ⟨q, ?_⟩
        simp only [countEchoRecv] at hq ⊢
        by_cases h : q = src
        · subst h ; simpa using hq
        · simpa [h] using hq
    · -- 11. count → approved: send doesn't touch initRecv or approved
      intro hnf p b hcnt
      have hcnt' : countInitRecv n (s.local_ p) b ≥ approveThreshold n f := by
        unfold countInitRecv at hcnt ⊢
        by_cases hpsrc : p = src
        · subst hpsrc
          cases t <;> simpa using hcnt
        · simpa [hpsrc] using hcnt
      have happ_old := hcount_app hnf p b hcnt'
      by_cases hpsrc : p = src
      · subst hpsrc
        cases t <;> simpa using happ_old
      · simpa [hpsrc] using happ_old
  | recv src dst t mv =>
    subst htrans
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hbudget -- 1. budget
    · -- 2. echo trace: echoRecv may grow at dst; echoed unchanged by recv
      intro p q b hp h
      by_cases hq : q = dst
      · rw [hq] at h ; cases t with
        | init => cases mv with
          | some bv =>
            by_cases hc : (s.local_ dst).initRecv src bv = false
            · -- echoRecv unchanged by init recv; echoed unchanged
              simp [hc] at h
              have hold := hetrace p dst b hp (hq ▸ h)
              by_cases hpdst : p = dst
              · rw [hpdst] at hold ; simp [hpdst, hc] ; exact hold
              · simp [hpdst] ; exact hold
            · -- state unchanged at dst
              simp [hc] at h
              have hold := hetrace p dst b hp (hq ▸ h)
              by_cases hpdst : p = dst
              · rw [hpdst] at hold ; simp [hpdst, hc] ; exact hold
              · simp [hpdst] ; exact hold
          | none =>
            simp at h
            have hold := hetrace p dst b hp (hq ▸ h)
            by_cases hpdst : p = dst
            · rw [hpdst] at hold ; simp [hpdst] ; exact hold
            · simp [hpdst] ; exact hold
        | echo => cases mv with
          | some bv =>
            by_cases hc : (s.local_ dst).echoRecv src bv = false
            · -- NEW echoRecv entry possible
              simp [hc] at h
              rcases h with ⟨rfl, rfl⟩ | hold
              · -- new entry (src→p, bv→b): use buffer echo trace
                have hechoed := hbet p dst b hp hgate
                by_cases hpdst : p = dst
                · rw [hpdst] at hechoed
                  simp only [apply_ite LocalState.echoed, hpdst, ite_true, ite_self]
                  exact hechoed
                · simp [hpdst] ; exact hechoed
              · -- old entry
                have hechoed := hetrace p dst b hp (hq ▸ hold)
                by_cases hpdst : p = dst
                · rw [hpdst] at hechoed ; simp [hpdst, hc] ; exact hechoed
                · simp [hpdst] ; exact hechoed
            · -- state unchanged at dst
              simp [hc] at h
              have hold := hetrace p dst b hp (hq ▸ h)
              by_cases hpdst : p = dst
              · rw [hpdst] at hold ; simp [hpdst, hc] ; exact hold
              · simp [hpdst] ; exact hold
          | none =>
            simp at h
            have hold := hetrace p dst b hp (hq ▸ h)
            by_cases hpdst : p = dst
            · rw [hpdst] at hold ; simp [hpdst] ; exact hold
            · simp [hpdst] ; exact hold
        | vote =>
          by_cases hc : (s.local_ dst).voteRecv src mv = false
          · simp [hc] at h
            have hold := hetrace p dst b hp (hq ▸ h)
            by_cases hpdst : p = dst
            · rw [hpdst] at hold ; simp [hpdst, hc] ; exact hold
            · simp [hpdst] ; exact hold
          · simp [hc] at h
            have hold := hetrace p dst b hp (hq ▸ h)
            by_cases hpdst : p = dst
            · rw [hpdst] at hold ; simp [hpdst, hc] ; exact hold
            · simp [hpdst] ; exact hold
      · -- q ≠ dst: echoRecv unchanged at q, echoed unchanged at p
        simp [hq] at h
        have hold := hetrace p q b hp h
        by_cases hpdst : p = dst
        · rw [hpdst] at hold ; cases t with
          | init => cases mv with
            | some bv =>
              by_cases hc : (s.local_ dst).initRecv src bv = false
              · simp [hpdst, hc] ; exact hold
              · simp [hpdst, hc] ; exact hold
            | none => simp [hpdst] ; exact hold
          | echo => cases mv with
            | some bv =>
              by_cases hc : (s.local_ dst).echoRecv src bv = false
              · simp [hpdst, hc] ; exact hold
              · simp [hpdst, hc] ; exact hold
            | none => simp [hpdst] ; exact hold
          | vote =>
            by_cases hc : (s.local_ dst).voteRecv src mv = false
            · simp [hpdst, hc] ; exact hold
            · simp [hpdst, hc] ; exact hold
        · simp [hpdst] ; exact hold
    · -- 3. buffer echo trace: buffer shrinks, echoed unchanged
      intro p d b hp hbuf ; simp only [] at hbuf
      -- buffer shrinks: our msg still in buffer (different from consumed)
      have hbuf' : s.buffer ⟨p, d, .echo, some b⟩ = true := by
        by_cases hm : (⟨p, d, .echo, some b⟩ : Message n) = ⟨src, dst, t, mv⟩
        · -- same message consumed: use gate → buffer was true
          obtain ⟨rfl, rfl, rfl, rfl⟩ := Message.mk.inj hm
          exact hgate
        · simp [hm] at hbuf ; exact hbuf
      have hold := hbet p d b hp hbuf'
      -- echoed unchanged by recv
      by_cases hpdst : p = dst
      · rw [hpdst] at hold ⊢ ; cases t with
        | init => cases mv with
          | some bv =>
            by_cases hc : (s.local_ dst).initRecv src bv = false
            · simp [hc] ; exact hold
            · simp [hc] ; exact hold
          | none => simp ; exact hold
        | echo => cases mv with
          | some bv =>
            by_cases hc : (s.local_ dst).echoRecv src bv = false
            · simp [hc] ; exact hold
            · simp [hc] ; exact hold
          | none => simp ; exact hold
        | vote =>
          by_cases hc : (s.local_ dst).voteRecv src mv = false
          · simp [hc] ; exact hold
          · simp [hc] ; exact hold
      · simp [hpdst] ; exact hold
    · -- 4. vote trace: voteRecv may grow at dst; voted unchanged
      -- For old entries: extract old voteRecv, apply hvtrace, show voted preserved.
      -- For new entry (recv.vote): use hbvt (buffer vote trace) directly.
      intro p q b hp h
      -- voted unchanged by recv: prove conclusion for q
      -- Split on whether this is a new voteRecv entry
      by_cases hpdst : p = dst
      · rw [hpdst] at h ; cases t with
        | init => cases mv with
          | some bv =>
            by_cases hc : (s.local_ dst).initRecv src bv = false
            · simp [hc] at h
              have hold := hvtrace dst q b hp h
              by_cases hqdst : q = dst
              · rw [hqdst] at hold ⊢ ; simp [hc] ; exact hold
              · simp [hqdst] ; exact hold
            · simp [hc] at h
              have hold := hvtrace dst q b hp h
              by_cases hqdst : q = dst
              · rw [hqdst] at hold ⊢ ; simp [hc] ; exact hold
              · simp [hqdst] ; exact hold
          | none =>
            simp at h
            have hold := hvtrace dst q b hp h
            by_cases hqdst : q = dst
            · rw [hqdst] at hold ⊢ ; simp ; exact hold
            · simp [hqdst] ; exact hold
        | echo => cases mv with
          | some bv =>
            by_cases hc : (s.local_ dst).echoRecv src bv = false
            · simp [hc] at h
              have hold := hvtrace dst q b hp h
              by_cases hqdst : q = dst
              · rw [hqdst] at hold ⊢ ; simp [hc] ; exact hold
              · simp [hqdst] ; exact hold
            · simp [hc] at h
              have hold := hvtrace dst q b hp h
              by_cases hqdst : q = dst
              · rw [hqdst] at hold ⊢ ; simp [hc] ; exact hold
              · simp [hqdst] ; exact hold
          | none =>
            simp at h
            have hold := hvtrace dst q b hp h
            by_cases hqdst : q = dst
            · rw [hqdst] at hold ⊢ ; simp ; exact hold
            · simp [hqdst] ; exact hold
        | vote =>
          by_cases hc : (s.local_ dst).voteRecv src mv = false
          · simp [hc] at h
            rcases h with ⟨rfl, rfl⟩ | hold
            · -- NEW entry: q sent vote(some b) via buffer → q voted
              have hvoted := hbvt q dst b hp hgate
              -- voted unchanged at q in new state
              by_cases hqdst : q = dst
              · rw [hqdst] at hvoted ⊢
                simp only [apply_ite LocalState.voted, ite_self] ; exact hvoted
              · simp [hqdst] ; exact hvoted
            · -- OLD entry
              have hold := hvtrace dst q b hp hold
              by_cases hqdst : q = dst
              · rw [hqdst] at hold ⊢ ; simp [hc] ; exact hold
              · simp [hqdst] ; exact hold
          · simp [hc] at h
            have hold := hvtrace dst q b hp h
            by_cases hqdst : q = dst
            · rw [hqdst] at hold ⊢ ; simp [hc] ; exact hold
            · simp [hqdst] ; exact hold
      · simp [hpdst] at h
        have hold := hvtrace p q b hp h
        by_cases hqdst : q = dst
        · rw [hqdst] at hold ⊢ ; cases t with
          | init => cases mv with
            | some bv =>
              by_cases hc : (s.local_ dst).initRecv src bv = false
              · simp only [apply_ite LocalState.voted, hc, ite_self] ; exact hold
              · simp only [apply_ite LocalState.voted, hc, ite_self] ; exact hold
            | none => simp ; exact hold
          | echo => cases mv with
            | some bv =>
              by_cases hc : (s.local_ dst).echoRecv src bv = false
              · simp only [apply_ite LocalState.voted, hc, ite_self] ; exact hold
              · simp only [apply_ite LocalState.voted, hc, ite_self] ; exact hold
            | none => simp ; exact hold
          | vote =>
            by_cases hc : (s.local_ dst).voteRecv src mv = false
            · simp only [apply_ite LocalState.voted, hc, ite_self] ; exact hold
            · simp only [apply_ite LocalState.voted, hc, ite_self] ; exact hold
        · simp [hqdst] ; exact hold
    · -- 5. buffer vote trace: buffer shrinks, voted unchanged
      intro p d b hp hbuf ; simp only [] at hbuf
      have hbuf' : s.buffer ⟨p, d, .vote, some b⟩ = true := by
        by_cases hm : (⟨p, d, .vote, some b⟩ : Message n) = ⟨src, dst, t, mv⟩
        · obtain ⟨rfl, rfl, rfl, rfl⟩ := Message.mk.inj hm ; exact hgate
        · simp [hm] at hbuf ; exact hbuf
      have hold := hbvt p d b hp hbuf'
      -- voted unchanged by recv
      by_cases hpdst : p = dst
      · rw [hpdst] at hold ⊢ ; cases t with
        | init => cases mv with
          | some bv =>
            by_cases hc : (s.local_ dst).initRecv src bv = false
            · simp only [apply_ite LocalState.voted, hc, ite_self] ; exact hold
            · simp only [apply_ite LocalState.voted, hc, ite_self] ; exact hold
          | none => simp ; exact hold
        | echo => cases mv with
          | some bv =>
            by_cases hc : (s.local_ dst).echoRecv src bv = false
            · simp only [apply_ite LocalState.voted, hc, ite_self] ; exact hold
            · simp only [apply_ite LocalState.voted, hc, ite_self] ; exact hold
          | none => simp ; exact hold
        | vote =>
          by_cases hc : (s.local_ dst).voteRecv src mv = false
          · simp only [apply_ite LocalState.voted, hc, ite_self] ; exact hold
          · simp only [apply_ite LocalState.voted, hc, ite_self] ; exact hold
      · simp [hpdst] ; exact hold
    · -- 6a. conditional (true)
      intro hs
      obtain ⟨hl, hb, hic⟩ := hcond_t hs
      have hsrc_corrupt_of_false : t = .init → mv = some false →
          src ∈ s.corrupted := fun ht hmv => by
        subst ht ; subst hmv
        by_contra hsrc_c
        have := hb ⟨src, dst, .init, some false⟩ hgate hsrc_c
        simp at this
      have hcount_false : ∀ q, isCorrect n s q →
          countInitRecv n (s.local_ q) false ≤ s.corrupted.length := fun q hq => by
        unfold countInitRecv
        exact nodup_sub_length
          ((finRange_nodup n).sublist List.filter_sublist)
          (fun x hx => by simp [List.mem_filter] at hx ; exact hic q x hq hx)
      refine ⟨?_, ?_, ?_⟩
      · intro p hp
        by_cases hpdst : p = dst
        · subst hpdst
          have hcons := hl p hp
          have happ' : (s.local_ p).approved false = false := by
            have := hcons.2.2.2.1 ; simpa using this
          have hcons_full : local_consistent n true (s.local_ p) := hcons
          -- For most branches the new state equals s.local_ p; only init+some false new-entry is special
          have hbase : ∀ ls', ls' = s.local_ p → local_consistent n true ls' := fun ls' h => h ▸ hcons_full
          simp only []
          cases t with
          | init =>
            cases mv with
            | some bv =>
              dsimp only
              by_cases hnew : (s.local_ p).initRecv src bv = false
              · rw [if_pos hnew]
                cases bv with
                | true =>
                  obtain ⟨hsent, hech, hvot, _, hdec⟩ := hcons
                  refine ⟨hsent, hech, hvot, ?_, hdec⟩
                  simp ; exact happ'
                | false =>
                  obtain ⟨hsent, hech, hvot, _, hdec⟩ := hcons
                  refine ⟨hsent, hech, hvot, ?_, hdec⟩
                  have hsrc_mem := hsrc_corrupt_of_false rfl rfl
                  have hle : countInitRecv n (s.local_ p) false + 1 ≤ s.corrupted.length := by
                    have hndf : ((List.finRange n).filter
                        ((s.local_ p).initRecv · false)).Nodup :=
                      (finRange_nodup n).sublist List.filter_sublist
                    have hsrc_notin : src ∉ (List.finRange n).filter
                        ((s.local_ p).initRecv · false) := by
                      intro hm ; rw [List.mem_filter] at hm
                      rw [hnew] at hm ; exact absurd hm.2 (by simp)
                    have hnd2 : (src :: (List.finRange n).filter
                        ((s.local_ p).initRecv · false)).Nodup :=
                      List.nodup_cons.mpr ⟨hsrc_notin, hndf⟩
                    have hsub : ∀ x ∈ src :: (List.finRange n).filter
                        ((s.local_ p).initRecv · false), x ∈ s.corrupted := by
                      intro x hx
                      rcases List.mem_cons.mp hx with rfl | hx
                      · exact hsrc_mem
                      · rw [List.mem_filter] at hx ; exact hic p x hp hx.2
                    have h1 := nodup_sub_length hnd2 hsub
                    simp only [List.length_cons] at h1
                    unfold countInitRecv ; omega
                  have hne : ¬ (approveThreshold n f ≤ countInitRecv n (s.local_ p) false + 1) := by
                    have : s.corrupted.length ≤ f := hbudget
                    unfold approveThreshold ; omega
                  simp [hne] ; exact happ'
              · rw [if_neg hnew] ; exact hcons_full
            | none => dsimp only ; exact hcons_full
          | echo =>
            cases mv with
            | some bv =>
              dsimp only
              by_cases hnew : (s.local_ p).echoRecv src bv = false
              · rw [if_pos hnew]
                obtain ⟨hsent, hech, hvot, _, hdec⟩ := hcons
                exact ⟨hsent, hech, hvot, happ', hdec⟩
              · rw [if_neg hnew] ; exact hcons_full
            | none => dsimp only ; exact hcons_full
          | vote =>
            dsimp only
            by_cases hnew : (s.local_ p).voteRecv src mv = false
            · rw [if_pos hnew]
              obtain ⟨hsent, hech, hvot, _, hdec⟩ := hcons
              exact ⟨hsent, hech, hvot, happ', hdec⟩
            · rw [if_neg hnew] ; exact hcons_full
        · simp [hpdst] ; exact hl p hp
      · intro m hm hsrc_c
        have hbuf_old : s.buffer m = true := by
          simp at hm
          by_cases hm_eq : m = ⟨src, dst, t, mv⟩
          · rw [hm_eq] ; exact hgate
          · simp [hm_eq] at hm ; exact hm
        exact hb m hbuf_old hsrc_c
      · intro q r hq h
        by_cases hqdst : q = dst
        · subst hqdst
          cases t with
          | init =>
            cases mv with
            | some bv =>
              by_cases hnew : (s.local_ q).initRecv src bv = false
              · simp [hnew] at h
                rcases h with ⟨rfl, hbv⟩ | h
                · exact hsrc_corrupt_of_false rfl (by rw [← hbv])
                · exact hic q r hq h
              · simp [hnew] at h ; exact hic q r hq h
            | none =>
              simp only [] at h ; exact hic q r hq h
          | echo =>
            cases mv with
            | some bv =>
              by_cases hnew : (s.local_ q).echoRecv src bv = false
              · simp [hnew] at h ; exact hic q r hq h
              · simp [hnew] at h ; exact hic q r hq h
            | none => simp at h ; exact hic q r hq h
          | vote =>
            by_cases hnew : (s.local_ q).voteRecv src mv = false
            · simp [hnew] at h ; exact hic q r hq h
            · simp [hnew] at h ; exact hic q r hq h
        · simp [hqdst] at h ; exact hic q r hq h
    · -- 6b. conditional (false): mirror of 6a
      intro hs
      obtain ⟨hl, hb, hic⟩ := hcond_f hs
      have hsrc_corrupt_of_true : t = .init → mv = some true →
          src ∈ s.corrupted := fun ht hmv => by
        subst ht ; subst hmv
        by_contra hsrc_c
        have := hb ⟨src, dst, .init, some true⟩ hgate hsrc_c
        simp at this
      have hcount_true : ∀ q, isCorrect n s q →
          countInitRecv n (s.local_ q) true ≤ s.corrupted.length := fun q hq => by
        unfold countInitRecv
        exact nodup_sub_length
          ((finRange_nodup n).sublist List.filter_sublist)
          (fun x hx => by simp [List.mem_filter] at hx ; exact hic q x hq hx)
      refine ⟨?_, ?_, ?_⟩
      · intro p hp
        by_cases hpdst : p = dst
        · subst hpdst
          have hcons := hl p hp
          have happ' : (s.local_ p).approved true = false := by
            have := hcons.2.2.2.1 ; simpa using this
          have hcons_full : local_consistent n false (s.local_ p) := hcons
          simp only []
          cases t with
          | init =>
            cases mv with
            | some bv =>
              dsimp only
              by_cases hnew : (s.local_ p).initRecv src bv = false
              · rw [if_pos hnew]
                cases bv with
                | false =>
                  obtain ⟨hsent, hech, hvot, _, hdec⟩ := hcons
                  refine ⟨hsent, hech, hvot, ?_, hdec⟩
                  simp ; exact happ'
                | true =>
                  obtain ⟨hsent, hech, hvot, _, hdec⟩ := hcons
                  refine ⟨hsent, hech, hvot, ?_, hdec⟩
                  have hsrc_mem := hsrc_corrupt_of_true rfl rfl
                  have hle : countInitRecv n (s.local_ p) true + 1 ≤ s.corrupted.length := by
                    have hndf : ((List.finRange n).filter
                        ((s.local_ p).initRecv · true)).Nodup :=
                      (finRange_nodup n).sublist List.filter_sublist
                    have hsrc_notin : src ∉ (List.finRange n).filter
                        ((s.local_ p).initRecv · true) := by
                      intro hm ; rw [List.mem_filter] at hm
                      rw [hnew] at hm ; exact absurd hm.2 (by simp)
                    have hnd2 : (src :: (List.finRange n).filter
                        ((s.local_ p).initRecv · true)).Nodup :=
                      List.nodup_cons.mpr ⟨hsrc_notin, hndf⟩
                    have hsub : ∀ x ∈ src :: (List.finRange n).filter
                        ((s.local_ p).initRecv · true), x ∈ s.corrupted := by
                      intro x hx
                      rcases List.mem_cons.mp hx with rfl | hx
                      · exact hsrc_mem
                      · rw [List.mem_filter] at hx ; exact hic p x hp hx.2
                    have h1 := nodup_sub_length hnd2 hsub
                    simp only [List.length_cons] at h1
                    unfold countInitRecv ; omega
                  have hne : ¬ (approveThreshold n f ≤ countInitRecv n (s.local_ p) true + 1) := by
                    have : s.corrupted.length ≤ f := hbudget
                    unfold approveThreshold ; omega
                  simp [hne] ; exact happ'
              · rw [if_neg hnew] ; exact hcons_full
            | none => dsimp only ; exact hcons_full
          | echo =>
            cases mv with
            | some bv =>
              dsimp only
              by_cases hnew : (s.local_ p).echoRecv src bv = false
              · rw [if_pos hnew]
                obtain ⟨hsent, hech, hvot, _, hdec⟩ := hcons
                exact ⟨hsent, hech, hvot, happ', hdec⟩
              · rw [if_neg hnew] ; exact hcons_full
            | none => dsimp only ; exact hcons_full
          | vote =>
            dsimp only
            by_cases hnew : (s.local_ p).voteRecv src mv = false
            · rw [if_pos hnew]
              obtain ⟨hsent, hech, hvot, _, hdec⟩ := hcons
              exact ⟨hsent, hech, hvot, happ', hdec⟩
            · rw [if_neg hnew] ; exact hcons_full
        · simp [hpdst] ; exact hl p hp
      · intro m hm hsrc_c
        have hbuf_old : s.buffer m = true := by
          simp at hm
          by_cases hm_eq : m = ⟨src, dst, t, mv⟩
          · rw [hm_eq] ; exact hgate
          · simp [hm_eq] at hm ; exact hm
        exact hb m hbuf_old hsrc_c
      · intro q r hq h
        by_cases hqdst : q = dst
        · subst hqdst
          cases t with
          | init =>
            cases mv with
            | some bv =>
              by_cases hnew : (s.local_ q).initRecv src bv = false
              · simp [hnew] at h
                rcases h with ⟨rfl, hbv⟩ | h
                · exact hsrc_corrupt_of_true rfl (by rw [← hbv])
                · exact hic q r hq h
              · simp [hnew] at h ; exact hic q r hq h
            | none =>
              simp only [] at h ; exact hic q r hq h
          | echo =>
            cases mv with
            | some bv =>
              by_cases hnew : (s.local_ q).echoRecv src bv = false
              · simp [hnew] at h ; exact hic q r hq h
              · simp [hnew] at h ; exact hic q r hq h
            | none => simp at h ; exact hic q r hq h
          | vote =>
            by_cases hnew : (s.local_ q).voteRecv src mv = false
            · simp [hnew] at h ; exact hic q r hq h
            · simp [hnew] at h ; exact hic q r hq h
        · simp [hqdst] at h ; exact hic q r hq h
    · -- 7. decision backing: decided unchanged, voteRecv monotone
      intro p b hdec
      -- Extract old decided
      have hdec' : (s.local_ p).decided = some (some b) := by
        by_cases hpdst : p = dst
        · rw [hpdst] at hdec ⊢ ; cases t with
          | init => cases mv with
            | some bv =>
              by_cases hc : (s.local_ dst).initRecv src bv = false
              · simp [hc] at hdec ; exact hdec
              · simp [hc] at hdec ; exact hdec
            | none => simp at hdec ; exact hdec
          | echo => cases mv with
            | some bv =>
              by_cases hc : (s.local_ dst).echoRecv src bv = false
              · simp [hc] at hdec ; exact hdec
              · simp [hc] at hdec ; exact hdec
            | none => simp at hdec ; exact hdec
          | vote =>
            by_cases hc : (s.local_ dst).voteRecv src mv = false
            · simp [hc] at hdec ; exact hdec
            · simp [hc] at hdec ; exact hdec
        · simp [hpdst] at hdec ; exact hdec
      have hold := hvback p b hdec'
      -- voteRecv monotone: count in new state ≥ old
      simp only [countVoteRecv] at hold ⊢
      apply Nat.le_trans hold ; apply filter_length_mono ; intro q hq
      by_cases hpdst : p = dst
      · rw [hpdst] at hq ⊢ ; cases t with
        | init => cases mv with
          | some bv =>
            by_cases hc : (s.local_ dst).initRecv src bv = false
            · simp [hc] ; exact hq
            · simp [hc] ; exact hq
          | none => simp ; exact hq
        | echo => cases mv with
          | some bv =>
            by_cases hc : (s.local_ dst).echoRecv src bv = false
            · simp [hc] ; exact hq
            · simp [hc] ; exact hq
          | none => simp ; exact hq
        | vote =>
          by_cases hc : (s.local_ dst).voteRecv src mv = false
          · simp [hc]
            by_cases hqv : q = src ∧ (some b : Val) = mv
            · obtain ⟨rfl, rfl⟩ := hqv ; simp
            · simp [hqv] ; exact hq
          · simp [hc] ; exact hq
      · simp [hpdst] ; exact hq
    · -- 8. vote agreement: voted unchanged by recv
      intro p q b₁ b₂ hp hq h1 h2
      have h1' : (s.local_ p).voted (some b₁) = true := by
        by_cases h : p = dst
        · subst h ; cases t with
          | init => cases mv with
            | some b => dsimp only [] at h1 ; simp only [apply_ite LocalState.voted, ite_self] at h1 ; exact h1
            | none => dsimp only [] at h1 ; simp only [apply_ite LocalState.voted] at h1; exact h1
          | echo => cases mv with
            | some b => dsimp only [] at h1 ; simp only [apply_ite LocalState.voted, ite_self] at h1 ; exact h1
            | none => dsimp only [] at h1 ; simp only [ite_self] at h1 ; exact h1
          | vote => dsimp only [] at h1 ; simp only [apply_ite LocalState.voted, ite_self] at h1 ; exact h1
        · simp [h] at h1 ; exact h1
      have h2' : (s.local_ q).voted (some b₂) = true := by
        by_cases h : q = dst
        · subst h ; cases t with
          | init => cases mv with
            | some b => dsimp only [] at h2 ; simp only [apply_ite LocalState.voted, ite_self] at h2 ; exact h2
            | none => dsimp only [] at h2 ; simp only [apply_ite LocalState.voted] at h2 ; exact h2
          | echo => cases mv with
            | some b => dsimp only [] at h2 ; simp only [apply_ite LocalState.voted, ite_self] at h2 ; exact h2
            | none => dsimp only [] at h2 ; simp only [ite_self] at h2 ; exact h2
          | vote => dsimp only [] at h2 ; simp only [apply_ite LocalState.voted, ite_self] at h2 ; exact h2
        · simp [h] at h2 ; exact h2
      exact hvagree p q b₁ b₂ hp hq h1' h2'
    · -- 9. echo backing: voted unchanged, echoRecv may grow
      intro p b hp hvp
      -- Extract old voted
      have hvp' : (s.local_ p).voted (some b) = true := by
        by_cases h : p = dst
        · subst h ; cases t with
          | init => cases mv with
            | some bv => dsimp only [] at hvp ; simp only [apply_ite LocalState.voted, ite_self] at hvp ; exact hvp
            | none => dsimp only [] at hvp ; simp only [apply_ite LocalState.voted] at hvp ; exact hvp
          | echo => cases mv with
            | some bv => dsimp only [] at hvp ; simp only [apply_ite LocalState.voted, ite_self] at hvp ; exact hvp
            | none => dsimp only [] at hvp ; simp only [ite_self] at hvp ; exact hvp
          | vote => dsimp only [] at hvp ; simp only [apply_ite LocalState.voted, ite_self] at hvp ; exact hvp
        · simp [h] at hvp ; exact hvp
      have hold := hecho_back p b hp hvp'
      -- echoRecv monotone: count in new state ≥ count in old state
      simp only [countEchoRecv] at hold ⊢
      apply Nat.le_trans hold ; apply filter_length_mono ; intro q hq
      by_cases h : p = dst
      · subst h ; cases t with
        | init => cases mv with
          | some bv => dsimp only [] ; simp only [apply_ite LocalState.echoRecv, ite_self] ; exact hq
          | none => dsimp only [] ; simp only [apply_ite LocalState.echoRecv] ; exact hq
        | echo => cases mv with
          | some bv => dsimp only [] ; simp only [apply_ite LocalState.echoRecv]
                       split
                       · split
                         · dsimp only []
                           show (decide (q = src) && decide (b = bv) ||
                                (s.local_ p).echoRecv q b) = true
                           simp [hq]
                         · exact hq
                       · exact hq
          | none => dsimp only [] ; simp only [ite_self] ; exact hq
        | vote => dsimp only [] ; simp only [apply_ite LocalState.echoRecv, ite_self] ; exact hq
      · simp [h] ; exact hq
    · -- 10. echo witness: voted unchanged, echoRecv monotone → old witness persists
      intro b ⟨p, hp, hvp⟩
      have hvp' : (s.local_ p).voted (some b) = true := by
        by_cases h : p = dst
        · subst h ; cases t with
          | init => cases mv with
            | some bv => dsimp only [] at hvp ; simp only [apply_ite LocalState.voted, ite_self] at hvp ; exact hvp
            | none => dsimp only [] at hvp ; simp only [apply_ite LocalState.voted] at hvp ; exact hvp
          | echo => cases mv with
            | some bv => dsimp only [] at hvp ; simp only [apply_ite LocalState.voted, ite_self] at hvp ; exact hvp
            | none => dsimp only [] at hvp ; simp only [ite_self] at hvp ; exact hvp
          | vote => dsimp only [] at hvp ; simp only [apply_ite LocalState.voted, ite_self] at hvp ; exact hvp
        · simp [h] at hvp ; exact hvp
      obtain ⟨q, hq⟩ := hecho_wit b ⟨p, hp, hvp'⟩
      refine ⟨q, ?_⟩ ; simp only [countEchoRecv] at hq ⊢
      apply Nat.le_trans hq ; apply filter_length_mono ; intro r hr
      by_cases h : q = dst
      · subst h ; cases t with
        | init => cases mv with
          | some bv => dsimp only [] ; simp only [apply_ite LocalState.echoRecv, ite_self] ; exact hr
          | none => dsimp only [] ; simp only [apply_ite LocalState.echoRecv] ; exact hr
        | echo => cases mv with
          | some bv => dsimp only [] ; simp only [apply_ite LocalState.echoRecv]
                       split
                       · split
                         · dsimp only []
                           show (decide (r = src) && decide (b = bv) ||
                                (s.local_ q).echoRecv r b) = true
                           simp [hr]
                         · exact hr
                       · exact hr
          | none => dsimp only [] ; simp only [ite_self] ; exact hr
        | vote => dsimp only [] ; simp only [apply_ite LocalState.echoRecv, ite_self] ; exact hr
      · simp [h] ; exact hr
    · -- 11. count → approved (recv case)
      intro hnf p b hcnt
      by_cases hpdst : p = dst
      · subst hpdst
        cases t with
        | echo =>
          -- echo recv: initRecv and approved unchanged at p
          cases mv with
          | none =>
            simp only [if_true] at hcnt ⊢
            exact hcount_app hnf p b hcnt
          | some bv =>
            simp only [if_true] at hcnt ⊢
            by_cases hifr : (s.local_ p).echoRecv src bv = false
            · rw [if_pos hifr] at hcnt ⊢
              exact hcount_app hnf p b hcnt
            · rw [if_neg hifr] at hcnt ⊢
              exact hcount_app hnf p b hcnt
        | vote =>
          -- vote recv: initRecv and approved unchanged at p
          simp only [if_true] at hcnt ⊢
          by_cases hifr : (s.local_ p).voteRecv src mv = false
          · rw [if_pos hifr] at hcnt ⊢
            exact hcount_app hnf p b hcnt
          · rw [if_neg hifr] at hcnt ⊢
            exact hcount_app hnf p b hcnt
        | init =>
          cases mv with
          | none =>
            simp only [if_true] at hcnt ⊢
            exact hcount_app hnf p b hcnt
          | some bv =>
            simp only [if_true] at hcnt ⊢
            by_cases halready : (s.local_ p).initRecv src bv = false
            · rw [if_pos halready] at hcnt ⊢
              -- New local at p: initRecv updated for (src, bv), approved possibly flipped.
              by_cases hbeq : b = bv
              · -- b = bv: count grew by 1, approved set if threshold crossed
                subst hbeq
                show (decide (b = b) && decide (approveThreshold n f ≤
                    countInitRecv n (s.local_ p) b + 1) || (s.local_ p).approved b) = true
                simp only [decide_true, Bool.true_and]
                -- Compute new count = old count + 1
                have hcnt_grow : countInitRecv n (s.local_ p) b + 1 ≥ approveThreshold n f := by
                  have heq : countInitRecv n
                      { sent := (s.local_ p).sent,
                        initRecv := fun q w =>
                          decide (q = src) && decide (w = b) || (s.local_ p).initRecv q w,
                        approved := fun w =>
                          decide (w = b) && decide
                            (approveThreshold n f ≤ countInitRecv n (s.local_ p) b + 1) ||
                          (s.local_ p).approved w,
                        echoed := (s.local_ p).echoed, echoRecv := (s.local_ p).echoRecv,
                        voted := (s.local_ p).voted, voteRecv := (s.local_ p).voteRecv,
                        decided := (s.local_ p).decided } b =
                      countInitRecv n (s.local_ p) b + 1 := by
                    unfold countInitRecv
                    show ((List.finRange n).filter
                      (fun q => decide (q = src) && decide (b = b) || (s.local_ p).initRecv q b)).length
                      = _
                    simp only [decide_true, Bool.and_true]
                    exact countInitRecv_succ_of_new (s.local_ p) src b halready
                  rw [heq] at hcnt
                  omega
                have : decide (approveThreshold n f ≤ countInitRecv n (s.local_ p) b + 1) = true := by
                  simp [hcnt_grow]
                rw [this] ; simp
              · -- b ≠ bv: count and approved for b unchanged
                show (decide (b = bv) && decide (approveThreshold n f ≤
                    countInitRecv n (s.local_ p) bv + 1) || (s.local_ p).approved b) = true
                have hbeq_false : decide (b = bv) = false := by simp [hbeq]
                rw [hbeq_false] ; simp
                -- Reduce new count b to old count b
                have hcnt' : countInitRecv n (s.local_ p) b ≥ approveThreshold n f := by
                  have heq : countInitRecv n
                      { sent := (s.local_ p).sent,
                        initRecv := fun q w =>
                          decide (q = src) && decide (w = bv) || (s.local_ p).initRecv q w,
                        approved := fun w =>
                          decide (w = bv) && decide
                            (approveThreshold n f ≤ countInitRecv n (s.local_ p) bv + 1) ||
                          (s.local_ p).approved w,
                        echoed := (s.local_ p).echoed, echoRecv := (s.local_ p).echoRecv,
                        voted := (s.local_ p).voted, voteRecv := (s.local_ p).voteRecv,
                        decided := (s.local_ p).decided } b =
                      countInitRecv n (s.local_ p) b := by
                    unfold countInitRecv
                    congr 1
                    apply List.filter_congr
                    intro q _
                    show (decide (q = src) && decide (b = bv) || (s.local_ p).initRecv q b) =
                         (s.local_ p).initRecv q b
                    rw [hbeq_false] ; simp
                  rw [heq] at hcnt ; exact hcnt
                exact hcount_app hnf p b hcnt'
            · rw [if_neg halready] at hcnt ⊢
              exact hcount_app hnf p b hcnt
      · -- p ≠ dst: local state at p unchanged
        simp [hpdst] at hcnt ⊢
        exact hcount_app hnf p b hcnt
  | decide i mv =>
    subst htrans
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hbudget -- 1. budget
    · -- 2. echo trace: echoRecv/echoed unchanged
      intro p q b hp h
      have hq' : (s.local_ q).echoRecv p b = true := by
        by_cases hq : q = i
        · rw [hq] ; simp [hq] at h ; exact h
        · simp [hq] at h ; exact h
      have h' := hetrace p q b hp hq'
      by_cases hp' : p = i
      · rw [hp'] ; simp ; rw [← hp'] ; exact h'
      · simp [hp'] ; exact h'
    · -- 3. buffer echo trace: buffer unchanged
      intro p d b hp h ; have h' := hbet p d b hp h
      by_cases hp' : p = i
      · rw [hp'] ; simp ; rw [← hp'] ; exact h'
      · simp [hp'] ; exact h'
    · -- 4. vote trace: voteRecv/voted unchanged
      intro p q b hp h
      have hp'' : (s.local_ p).voteRecv q (some b) = true := by
        by_cases hp' : p = i
        · rw [hp'] ; simp [hp'] at h ; exact h
        · simp [hp'] at h ; exact h
      have h' := hvtrace p q b hp hp''
      by_cases hq : q = i
      · rw [hq] ; simp ; rw [← hq] ; exact h'
      · simp [hq] ; exact h'
    · -- 5. buffer vote trace: buffer unchanged
      intro p d b hp h ; have h' := hbvt p d b hp h
      by_cases hp' : p = i
      · rw [hp'] ; simp ; rw [← hp'] ; exact h'
      · simp [hp'] ; exact h'
    · -- 6a. conditional (true): under unanimity input=true, decided must be some true
      intro hs
      obtain ⟨hl, hb, hic⟩ := hcond_t hs
      refine ⟨?_, hb, ?_⟩
      swap
      · intro q r hq h
        simp only [apply_ite LocalState.initRecv] at h
        by_cases hqi : q = i
        · rw [hqi] at h hq ; simp at h ; exact hic i r hq h
        · simp [hqi] at h ; exact hic q r hq h
      · intro p hp
        by_cases hpi : p = i
        · subst hpi ; have hcons := hl p hp
          simp only [local_consistent] at hcons ⊢
          refine ⟨hcons.1, hcons.2.1, hcons.2.2.1, hcons.2.2.2.1, ?_⟩
          intro w hdec ; simp at hdec
          -- new decision: gate determines mv; need mv = some true
          subst hdec
          cases mv with
          | some b =>
            -- gate: countVoteRecv (some b) ≥ n-f → pigeonhole → correct voter
            have hcount := hgate.2.2
            have hgt : s.corrupted.length < countVoteRecv n (s.local_ p) (some b) :=
              calc s.corrupted.length ≤ f := hbudget
                _ < n - f := by omega
                _ ≤ _ := hcount
            obtain ⟨r, hr_vote, hr_corr⟩ := pigeonhole_filter
              ((s.local_ p).voteRecv · (some b)) s.corrupted hgt
            have hr_voted := hvtrace p r b hr_corr hr_vote
            have hr_cons := hl r hr_corr
            simp only [local_consistent] at hr_cons
            have := hr_cons.2.2.1 b hr_voted
            rw [this]
          | none =>
            -- gate: both approved (approved false = true), but local_cons says approved false = false
            have happ : (s.local_ p).approved false = false := (hl p hp).2.2.2.1
            have happ' : (s.local_ p).approved false = true := hgate.2.2.1
            rw [happ] at happ' ; exact absurd happ' (by simp)
        · simp [hpi] ; exact hl p hp
    · -- 6b. conditional (false): symmetric
      intro hs
      obtain ⟨hl, hb, hic⟩ := hcond_f hs
      refine ⟨?_, hb, ?_⟩
      swap
      · intro q r hq h
        simp only [apply_ite LocalState.initRecv] at h
        by_cases hqi : q = i
        · rw [hqi] at h hq ; simp at h ; exact hic i r hq h
        · simp [hqi] at h ; exact hic q r hq h
      · intro p hp
        by_cases hpi : p = i
        · subst hpi ; have hcons := hl p hp
          simp only [local_consistent] at hcons ⊢
          refine ⟨hcons.1, hcons.2.1, hcons.2.2.1, hcons.2.2.2.1, ?_⟩
          intro w hdec ; simp at hdec
          subst hdec
          cases mv with
          | some b =>
            have hcount := hgate.2.2
            have hgt : s.corrupted.length < countVoteRecv n (s.local_ p) (some b) :=
              calc s.corrupted.length ≤ f := hbudget
                _ < n - f := by omega
                _ ≤ _ := hcount
            obtain ⟨r, hr_vote, hr_corr⟩ := pigeonhole_filter
              ((s.local_ p).voteRecv · (some b)) s.corrupted hgt
            have hr_voted := hvtrace p r b hr_corr hr_vote
            have hr_cons := hl r hr_corr
            simp only [local_consistent] at hr_cons
            have := hr_cons.2.2.1 b hr_voted
            rw [this]
          | none =>
            -- under input=false unanimity, approved true = false (from local_cons)
            -- but gate says approved true = true
            have happ : (s.local_ p).approved true = false := by
              have := (hl p hp).2.2.2.1 ; simp at this ; exact this
            have happ' : (s.local_ p).approved true = true := hgate.2.2.2.1
            rw [happ] at happ' ; exact absurd happ' (by simp)
        · simp [hpi] ; exact hl p hp
    · -- 7. decision backing
      intro p b hdec ; by_cases hpi : p = i
      · subst hpi ; simp at hdec ; subst hdec ; simp ; exact hgate.2.2
      · simp [hpi] at hdec ⊢ ; exact hvback p b hdec
    · -- 8. vote agreement: voted unchanged
      intro p q b₁ b₂ hp hq h1 h2
      have h1' : (s.local_ p).voted (some b₁) = true := by
        by_cases h : p = i
        · rw [h] ; simp [h] at h1 ; exact h1
        · simp [h] at h1 ; exact h1
      have h2' : (s.local_ q).voted (some b₂) = true := by
        by_cases h : q = i
        · rw [h] ; simp [h] at h2 ; exact h2
        · simp [h] at h2 ; exact h2
      exact hvagree p q b₁ b₂ hp hq h1' h2'
    · -- 9. echo backing: voted/echoRecv unchanged
      intro p b hp hvp
      have hvp' : (s.local_ p).voted (some b) = true := by
        by_cases h : p = i
        · rw [h] ; simp [h] at hvp ; exact hvp
        · simp [h] at hvp ; exact hvp
      have h' := hecho_back p b hp hvp'
      simp only [countEchoRecv] at h' ⊢
      by_cases hpi : p = i
      · rw [hpi] ; simp ; rw [← hpi] ; exact h'
      · simp [hpi] ; exact h'
    · -- 10. echo witness: voted unchanged
      intro b ⟨p, hp, hvp⟩
      have hvp' : (s.local_ p).voted (some b) = true := by
        by_cases h : p = i
        · rw [h] ; simp [h] at hvp ; exact hvp
        · simp [h] at hvp ; exact hvp
      obtain ⟨q, hq⟩ := hecho_wit b ⟨p, hp, hvp'⟩
      refine ⟨q, ?_⟩ ; simp only [countEchoRecv] at hq ⊢
      by_cases h : q = i
      · rw [h] ; simp ; rw [← h] ; exact hq
      · simp [h] ; exact hq
    · -- 11. count → approved: decide doesn't touch initRecv or approved
      intro hnf p b hcnt
      have hcnt' : countInitRecv n (s.local_ p) b ≥ approveThreshold n f := by
        unfold countInitRecv at hcnt ⊢
        by_cases hpi : p = i
        · subst hpi ; simpa using hcnt
        · simpa [hpi] using hcnt
      have happ_old := hcount_app hnf p b hcnt'
      by_cases hpi : p = i
      · subst hpi ; simpa using happ_old
      · simpa [hpi] using happ_old

/-! ### Agreement -/

/-- Agreement: all non-faulty processes that decide a binary value, decide
    the same binary value. Proof: each binary decision has ≥ n−f votes.
    Pigeonhole gives a correct voter for each. Vote agreement (conjunct 8)
    forces the values to be equal. -/
theorem bca_agreement (input : Fin n → Bool) (hn : n > 3 * f) :
    pred_implies (bca n f input).safety
      [tlafml| □ ⌜ agreement n ⌝] := by
  intro e hsafety
  have hinv := init_invariant
    (bca_inv_init n f input)
    (fun s s' hn' hi => bca_inv_step n f input hn s s' hn' hi)
    e hsafety
  intro k
  obtain ⟨hbudget, _, _, hvtrace, _, _, _, hvback, hvagree, _, _⟩ := hinv k
  intro p q b hp hq hdecp hdecq
  -- p decided (some b), q decided (some (!b)). Derive contradiction.
  -- Decision backing: each has ≥ n−f votes.
  have hvp := hvback p b hdecp
  have hvq := hvback q (!b) hdecq
  -- Pigeonhole: correct voter for each.
  have hgt_p : (exec.drop k e 0).corrupted.length <
      countVoteRecv n (exec.drop k e 0 |>.local_ p) (some b) :=
    calc (exec.drop k e 0).corrupted.length ≤ f := hbudget
      _ < n - f := by omega
      _ ≤ _ := hvp
  obtain ⟨rp, hrp_vote, hrp_corr⟩ := pigeonhole_filter
    ((exec.drop k e 0).local_ p |>.voteRecv · (some b)) (exec.drop k e 0).corrupted hgt_p
  have hgt_q : (exec.drop k e 0).corrupted.length <
      countVoteRecv n (exec.drop k e 0 |>.local_ q) (some (!b)) :=
    calc (exec.drop k e 0).corrupted.length ≤ f := hbudget
      _ < n - f := by omega
      _ ≤ _ := hvq
  obtain ⟨rq, hrq_vote, hrq_corr⟩ := pigeonhole_filter
    ((exec.drop k e 0).local_ q |>.voteRecv · (some (!b))) (exec.drop k e 0).corrupted hgt_q
  -- Vote trace: rp voted (some b), rq voted (some (!b)).
  have hrp_voted := hvtrace p rp b hrp_corr hrp_vote
  have hrq_voted := hvtrace q rq (!b) hrq_corr hrq_vote
  -- Vote agreement: b = !b, contradiction.
  have := hvagree rp rq b (!b) hrp_corr hrq_corr hrp_voted hrq_voted
  simp at this

/-! ### Validity -/

/-- Validity: if all correct processes have input b, any correct process
    that decides, decides b. Derives from conjunct 6 (conditional). -/
theorem bca_validity (input : Fin n → Bool) (hn : n > 3 * f) (b : Bool) :
    pred_implies (bca n f input).safety
      [tlafml| □ ⌜ validity n input b ⌝] := by
  intro e hsafety
  have hinv := init_invariant
    (bca_inv_init n f input)
    (fun s s' hn' hi => bca_inv_step n f input hn s s' hn' hi)
    e hsafety
  intro k
  obtain ⟨_, _, _, _, _, hcond_t, hcond_f, _, _, _, _⟩ := hinv k
  intro hall p v hp hdec
  cases b with
  | true => exact (hcond_t hall).1 p hp |>.2.2.2.2 v hdec
  | false => exact (hcond_f hall).1 p hp |>.2.2.2.2 v hdec

/-! ### Binding

    We prove `binding` using the ghost `boundValue`. Intuitively, `boundValue`
    tracks a "committed" outcome:
    - `none` means no commitment yet;
    - `some (some b)` means binary `b` is committed — no correct process will
      ever decide `some (!b)`;
    - `some none` means ⊥ is committed — no correct process will ever decide a
      binary value.

    The strategy: define an invariant `bound_inv` capturing these facts, prove
    it is inductive, then derive `binding`. -/

/-- Bound invariant. Conjuncts:

    **B1. Bound set before any correct decision.** If some correct process has
    decided, then `boundValue ≠ none`. Follows from the fact that any correct
    decide needs `n − f` vote receipts, hence strictly more than `f` sources,
    at least one of them correct and having voted — which crosses the threshold
    to set `boundValue`.

    **B2. Correct decisions lie in {boundValue, ⊥}.** If a correct process has
    decided `some (some b)` (binary), then `boundValue = some (some b)` or
    `boundValue = some none`. Since ⊥ is compatible with any binding-`b`, the
    first case provides the witness, the second is handled below.

    **B3. Bound-⊥ blocks future binary decisions.** If `boundValue = some none`
    (i.e., `|corrupted| + correct ⊥-voters > 2f`), then no correct process ever
    decides a binary value. Reason: fewer than `n − 2f` correct processes
    remain free to vote binary, so any `n − f` vote receipts must include
    corrupt sources; pigeonhole then fails to find a correct binary voter.

    **B4. Bound-binary restricts future binary votes.** If
    `boundValue = some (some b₀)`, then no correct process has voted
    `some (!b₀)`. Follows from echo-quorum intersection: the `> f` correct
    `b₀`-voters each have `n − f` echo receipts for `b₀`, so any correct vote
    for `!b₀` would require echo receipts for `!b₀` sharing ≥ `n − 2f ≥ f + 1`
    correct sources, contradicting single-echo. -/
def bound_inv (s : State n) : Prop :=
  -- B1: Correct binary decisions match the bound (or bound is ⊥).
  (∀ p b, isCorrect n s p → (s.local_ p).decided = some (some b) →
    s.boundValue = some (some b) ∨ s.boundValue = some none) ∧
  -- B2: Once bound is ⊥, no correct binary decision exists.
  (s.boundValue = some none →
    ∀ p b, isCorrect n s p → (s.local_ p).decided ≠ some (some b)) ∧
  -- B3: Once bound is binary `b₀`, no correct process has voted `some (!b₀)`.
  (∀ b₀, s.boundValue = some (some b₀) →
    ∀ p, isCorrect n s p → (s.local_ p).voted (some (!b₀)) = false) ∧
  -- B4: Once bound is binary `b₀`, some process has an echo quorum for `b₀`
  -- (persisted across corruption via `echoRecv` monotonicity).
  (∀ b₀, s.boundValue = some (some b₀) →
    ∃ p, countEchoRecv n (s.local_ p) b₀ ≥ echoThreshold n f) ∧
  -- B5: `boundValue` is always the `computeBound` of the current state.
  (s.boundValue = computeBound n f s) ∧
  -- B6: A correct process votes at most one value (vote-once invariant).
  (∀ p, isCorrect n s p → ∀ v₁ v₂, (s.local_ p).voted v₁ = true →
    (s.local_ p).voted v₂ = true → v₁ = v₂) ∧
  -- B7: The corrupted list has no duplicates (each corrupt action's gate
  -- enforces `i ∉ s.corrupted`).
  s.corrupted.Nodup ∧
  -- B8: If the bound has become ⊥, the ⊥ threshold is currently crossed.
  -- This is stronger than the obvious inherited form and needed for B2 (to
  -- rule out binary decisions from a correct process currently in a ⊥ state).
  (s.boundValue = some none →
    s.corrupted.length + correctVoteCount n s none > 2 * f)

theorem bound_inv_init :
    ∀ s, ∀ input, (bca n f input).init s → bound_inv n f s := by
  intro s input ⟨hlocal, _, hcorr, hbv⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p b _ hdec ; simp [hlocal, LocalState.init] at hdec
  · intro hbv' ; rw [hbv] at hbv' ; exact absurd hbv' (by simp)
  · intro b₀ hbv' ; rw [hbv] at hbv' ; exact absurd hbv' (by simp)
  · intro b₀ hbv' ; rw [hbv] at hbv' ; exact absurd hbv' (by simp)
  · rw [hbv] ; unfold computeBound
    have hf : ∀ v, correctVoteCount n s v = 0 := fun v => by
      simp [correctVoteCount, hlocal, LocalState.init]
    simp [hf, hcorr, hbv]
  · intro p _ v₁ v₂ h _ ; simp [hlocal, LocalState.init] at h
  · rw [hcorr] ; exact List.nodup_nil
  · intro h ; rw [hbv] at h ; exact absurd h (by simp)

/-- `computeBound` preserves a binary value (possibly upgrading to ⊥). -/
theorem computeBound_preserves_binary (s : State n) (b₀ : Bool) :
    s.boundValue = some (some b₀) →
    computeBound n f s = some (some b₀) ∨ computeBound n f s = some none := by
  intro h
  unfold computeBound
  split
  · right ; rfl
  · left ; rw [h]

/-- `computeBound` preserves ⊥. -/
theorem computeBound_preserves_bot (s : State n) :
    s.boundValue = some none → computeBound n f s = some none := by
  intro h
  unfold computeBound
  split
  · rfl
  · rw [h]

/-- If `computeBound` returns a binary value, either the old bound was already
    that same binary value, or the old bound was `none` and the corresponding
    threshold has just crossed. Used for B3 and B4 of `bound_inv_step`. -/
theorem computeBound_eq_some_some (s : State n) (b₀ : Bool)
    (h : computeBound n f s = some (some b₀)) :
    s.boundValue = some (some b₀) ∨
    (s.boundValue = none ∧
     ¬ (s.corrupted.length + correctVoteCount n s none > 2 * f) ∧
     s.corrupted.length + correctVoteCount n s (some b₀) > f) := by
  unfold computeBound at h
  by_cases hbot : s.corrupted.length + correctVoteCount n s none > 2 * f
  · rw [if_pos hbot] at h ; exact absurd h (by simp)
  · rw [if_neg hbot] at h
    match hbv : s.boundValue, h with
    | some (some b'), h =>
      left
      injection h with h1 ; injection h1 with h2 ; rw [h2]
    | some none, h => exact absurd h (by simp)
    | none, h =>
      by_cases h_f : s.corrupted.length + correctVoteCount n s (some false) > f
      · rw [if_pos h_f] at h
        cases b₀ with
        | false => right ; exact ⟨rfl, hbot, h_f⟩
        | true => exact absurd h (by simp)
      · rw [if_neg h_f] at h
        by_cases h_t : s.corrupted.length + correctVoteCount n s (some true) > f
        · rw [if_pos h_t] at h
          cases b₀ with
          | true => right ; exact ⟨rfl, hbot, h_t⟩
          | false => exact absurd h (by simp)
        · rw [if_neg h_t] at h ; exact absurd h (by simp)

/-- If `computeBound` returns `some none`, either the old bound was already
    `some none`, or the ⊥ threshold has just crossed. -/
theorem computeBound_eq_some_none (s : State n)
    (h : computeBound n f s = some none) :
    s.boundValue = some none ∨
    s.corrupted.length + correctVoteCount n s none > 2 * f := by
  unfold computeBound at h
  by_cases hbot : s.corrupted.length + correctVoteCount n s none > 2 * f
  · right ; exact hbot
  · rw [if_neg hbot] at h
    match hbv : s.boundValue, h with
    | some (some _), h => exact absurd h (by simp)
    | some none, _ => left ; rfl
    | none, h =>
      by_cases h_f : s.corrupted.length + correctVoteCount n s (some false) > f
      · rw [if_pos h_f] at h ; exact absurd h (by simp)
      · rw [if_neg h_f] at h
        by_cases h_t : s.corrupted.length + correctVoteCount n s (some true) > f
        · rw [if_pos h_t] at h ; exact absurd h (by simp)
        · rw [if_neg h_t] at h ; exact absurd h (by simp)

/-- If `computeBound` returns `none` then no threshold has crossed: neither
    the ⊥ threshold (`> 2f`) nor either binary threshold (`> f`). This is the
    direct contrapositive of the `computeBound` cases when the old bound is
    `none` and the new value is `none`. -/
theorem computeBound_eq_none (s : State n)
    (h : computeBound n f s = none) :
    s.corrupted.length + correctVoteCount n s none ≤ 2 * f ∧
    s.corrupted.length + correctVoteCount n s (some false) ≤ f ∧
    s.corrupted.length + correctVoteCount n s (some true) ≤ f := by
  unfold computeBound at h
  by_cases hbot : s.corrupted.length + correctVoteCount n s none > 2 * f
  · rw [if_pos hbot] at h ; exact absurd h (by simp)
  · rw [if_neg hbot] at h
    cases hbv : s.boundValue with
    | some bv => rw [hbv] at h ; exact absurd h (by simp)
    | none =>
      rw [hbv] at h
      by_cases h_f : s.corrupted.length + correctVoteCount n s (some false) > f
      · rw [if_pos h_f] at h ; exact absurd h (by simp)
      · rw [if_neg h_f] at h
        by_cases h_t : s.corrupted.length + correctVoteCount n s (some true) > f
        · rw [if_pos h_t] at h ; exact absurd h (by simp)
        · exact ⟨by omega, by omega, by omega⟩

/-- **Idempotence of `computeBound`**: applying `computeBound` to a state
    whose `boundValue` has just been set by `computeBound` yields the same
    result. Proved by exhaustive case analysis on which branch of
    `computeBound n f s` fires. -/
theorem computeBound_idempotent (s : State n) :
    computeBound n f { s with boundValue := computeBound n f s } = computeBound n f s := by
  -- `correctVoteCount` and `.corrupted` don't read the boundValue field,
  -- so any struct update with `boundValue := _` preserves them.
  have hcvc_eq : ∀ bv v,
      correctVoteCount n ({ s with boundValue := bv } : State n) v
      = correctVoteCount n s v := fun _ _ => rfl
  have hcorr_eq : ∀ bv,
      ({ s with boundValue := bv } : State n).corrupted = s.corrupted := fun _ => rfl
  by_cases hbot : s.corrupted.length + correctVoteCount n s none > 2 * f
  · have hX : computeBound n f s = some none := by
      unfold computeBound ; simp [hbot]
    rw [hX] ; unfold computeBound ; simp [hcvc_eq, hbot]
  · cases hbv : s.boundValue with
    | some bv =>
      have hX : computeBound n f s = some bv := by
        unfold computeBound ; simp [hbot, hbv]
      rw [hX] ; unfold computeBound ; simp [hcvc_eq, hbot]
    | none =>
      by_cases h_f : s.corrupted.length + correctVoteCount n s (some false) > f
      · have hX : computeBound n f s = some (some false) := by
          unfold computeBound ; simp [hbot, hbv, h_f]
        rw [hX] ; unfold computeBound ; simp [hcvc_eq, hbot]
      · by_cases h_t : s.corrupted.length + correctVoteCount n s (some true) > f
        · have hX : computeBound n f s = some (some true) := by
            unfold computeBound ; simp [hbot, hbv, h_f, h_t]
          rw [hX] ; unfold computeBound ; simp [hcvc_eq, hbot]
        · have hX : computeBound n f s = none := by
            unfold computeBound ; simp [hbot, hbv, h_f, h_t]
          rw [hX] ; unfold computeBound
          simp [hcvc_eq, hbot, h_f, h_t]

/-- Congruence for `computeBound` on fields it reads. -/
theorem computeBound_congr (n f : Nat) {s s' : State n}
    (hc : s'.corrupted = s.corrupted)
    (hv : ∀ p v, (s'.local_ p).voted v = (s.local_ p).voted v)
    (hbv : s'.boundValue = s.boundValue) :
    computeBound n f s' = computeBound n f s := by
  have hcvc : ∀ v, correctVoteCount n s' v = correctVoteCount n s v := by
    intro v ; simp only [correctVoteCount, hc]
    apply congrArg ; apply List.filter_congr ; intro p _
    simp [hv p v]
  unfold computeBound ; simp only [hc, hcvc, hbv]

/-- Transfer `bound_inv` along a congruence of the fields it reads.
    `echoRecv` only needs monotone growth (enough for the existential in B4). -/
theorem bound_inv_congr (n f : Nat) {s s' : State n}
    (hc : s'.corrupted = s.corrupted)
    (hv : ∀ p v, (s'.local_ p).voted v = (s.local_ p).voted v)
    (hd : ∀ p v, (s'.local_ p).decided = v ↔ (s.local_ p).decided = v)
    (he : ∀ p q b, (s.local_ p).echoRecv q b = true → (s'.local_ p).echoRecv q b = true)
    (hbv : s'.boundValue = s.boundValue) :
    bound_inv n f s → bound_inv n f s' := fun ⟨hB1, hB2, hB3, hB4, hB5, hB6, hB7, hB8⟩ => by
  have hic : ∀ p, isCorrect n s' p = isCorrect n s p := fun p => by
    unfold isCorrect ; rw [hc]
  have hcmon : ∀ p b, countEchoRecv n (s.local_ p) b ≤ countEchoRecv n (s'.local_ p) b := by
    intro p b
    apply filter_length_mono
    intro q hq ; exact he p q b hq
  have hcvc_eq : ∀ v, correctVoteCount n s' v = correctVoteCount n s v := by
    intro v ; simp only [correctVoteCount, hc]
    apply congrArg ; apply List.filter_congr ; intro q _ ; simp [hv q v]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p b hcp hdec
    have hcp' : isCorrect n s p := (hic p) ▸ hcp
    have hdec' : (s.local_ p).decided = some (some b) := (hd p _).mp hdec
    rw [hbv] ; exact hB1 p b hcp' hdec'
  · intro hbv' p b hcp
    rw [hbv] at hbv'
    have hcp' : isCorrect n s p := (hic p) ▸ hcp
    have := hB2 hbv' p b hcp'
    intro hdec ; exact this ((hd p _).mp hdec)
  · intro b₀ hbv' p hcp
    rw [hbv] at hbv'
    have hcp' : isCorrect n s p := (hic p) ▸ hcp
    rw [hv p (some (!b₀))] ; exact hB3 b₀ hbv' p hcp'
  · intro b₀ hbv'
    rw [hbv] at hbv'
    obtain ⟨p, hp⟩ := hB4 b₀ hbv'
    exact ⟨p, Nat.le_trans hp (hcmon p b₀)⟩
  · rw [hbv, computeBound_congr n f hc hv hbv, hB5]
  · intro p hcp v₁ v₂ hv1 hv2
    have hcp' : isCorrect n s p := (hic p) ▸ hcp
    rw [hv p v₁] at hv1 ; rw [hv p v₂] at hv2
    exact hB6 p hcp' v₁ v₂ hv1 hv2
  · rw [hc] ; exact hB7
  · intro hbv' ; rw [hbv] at hbv' ; rw [hc, hcvc_eq] ; exact hB8 hbv'

/-- `correctVoteCount` ignores the `boundValue` field. -/
theorem correctVoteCount_with_bv (s : State n) (bv : Option (Option Bool)) (v : Val) :
    correctVoteCount n ({ s with boundValue := bv } : State n) v = correctVoteCount n s v := rfl

/-- **Pigeonhole from decision backing**: a correct binary decision at `p`
    guarantees at least `n − f − |corrupted|` correct voters in the current
    state for the same binary value. Relies on `vote_trace` from `bca_inv`. -/

theorem correct_voters_of_decision (s : State n) (p : Fin n) (b : Bool)
    (hvtrace : ∀ p q b, isCorrect n s q → (s.local_ p).voteRecv q (some b) = true →
      (s.local_ q).voted (some b) = true)
    (hcount : countVoteRecv n (s.local_ p) (some b) ≥ n - f) :
    correctVoteCount n s (some b) ≥ n - f - s.corrupted.length := by
  unfold correctVoteCount
  have hcorr_bound : ((List.finRange n).filter (fun q =>
      (s.local_ p).voteRecv q (some b) && decide (q ∈ s.corrupted))).length
      ≤ s.corrupted.length := by
    apply Nat.le_trans (filter_and_le _ _ _)
    exact nodup_sub_length ((finRange_nodup n).sublist List.filter_sublist)
      (fun x hx => by simp [List.mem_filter] at hx ; exact hx)
  have hsplit := filter_split ((s.local_ p).voteRecv · (some b))
    (fun q => decide (q ∈ s.corrupted)) (List.finRange n)
  have hnot_corr : ((List.finRange n).filter (fun q =>
      (s.local_ p).voteRecv q (some b) && !decide (q ∈ s.corrupted))).length
      ≥ n - f - s.corrupted.length := by
    unfold countVoteRecv at hcount ; omega
  apply Nat.le_trans hnot_corr
  apply filter_length_mono
  intro q hq
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hq
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hq.2, hvtrace p q b hq.2 hq.1⟩

/-- The number of processes not in `s.corrupted` equals `n − |s.corrupted|`
    when `s.corrupted` is `Nodup`. -/
theorem not_corrupted_count (s : State n) (hB7 : s.corrupted.Nodup)
    (hbnd : s.corrupted.length ≤ n) :
    ((List.finRange n).filter (fun q => !decide (q ∈ s.corrupted))).length
    = n - s.corrupted.length := by
  have hcorr_filter : ((List.finRange n).filter (fun q =>
      decide (q ∈ s.corrupted))).length = s.corrupted.length := by
    apply Nat.le_antisymm
    · exact nodup_sub_length ((finRange_nodup n).sublist List.filter_sublist)
        (fun x hx => by simp [List.mem_filter] at hx ; exact hx)
    · exact nodup_sub_length hB7
        (fun x hx => by simp [List.mem_filter, hx])
  have hsum : ∀ (l : List (Fin n)),
      (l.filter (fun q => !decide (q ∈ s.corrupted))).length
      + (l.filter (fun q => decide (q ∈ s.corrupted))).length
      = l.length := by
    intro l
    induction l with
    | nil => simp
    | cons a t ih =>
      simp only [List.filter_cons, List.length_cons]
      by_cases h : a ∈ s.corrupted
      · simp [h] ; omega
      · simp [h] ; omega
  have := hsum (List.finRange n)
  rw [List.length_finRange] at this
  omega

/-- **Vote-once disjointness over two values**: the sum of correct voters for
    `(some b)` and `none` is at most the total number of correct processes
    `n − |s.corrupted|` (requires vote-once B6 and nodup B7).
    Proof strategy: `correctVoteCount(none)` is bounded above by the count of
    correct processes that have *not* voted `(some b)` (via B6); then
    `filter_split` completes the argument. -/
theorem vote_once_disjoint (s : State n)
    (hB6 : ∀ p, isCorrect n s p → ∀ v₁ v₂,
      (s.local_ p).voted v₁ = true → (s.local_ p).voted v₂ = true → v₁ = v₂)
    (hB7 : s.corrupted.Nodup) (hbnd : s.corrupted.length ≤ n) (b : Bool) :
    correctVoteCount n s (some b) + correctVoteCount n s none ≤ n - s.corrupted.length := by
  -- Bound correctVoteCount(none) by |{q ∉ c ∧ !voted q (some b)}| using B6
  unfold correctVoteCount
  have hnone_le : ((List.finRange n).filter
          (fun p => decide (p ∉ s.corrupted) && (s.local_ p).voted none)).length
      ≤ ((List.finRange n).filter
          (fun q => decide (q ∉ s.corrupted) && !(s.local_ q).voted (some b))).length := by
    apply filter_length_mono
    intro q hq
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
    obtain ⟨hq_corr, hq_voted⟩ := hq
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
    refine ⟨hq_corr, ?_⟩
    by_contra hvb
    have hvb' : (s.local_ q).voted (some b) = true := by
      cases h : (s.local_ q).voted (some b) with
      | true => rfl
      | false => exact absurd h hvb
    exact nomatch (hB6 q hq_corr (some b) none hvb' hq_voted)
  -- filter_split: cnt(some b ∧ ¬c) + cnt(!voted b ∧ ¬c) = cnt(¬c)
  have hsplit := filter_split (fun q : Fin n => decide (q ∉ s.corrupted))
    (fun q => (s.local_ q).voted (some b)) (List.finRange n)
  -- And cnt(¬c) = n - |corr|
  have hcount_not_c : ((List.finRange n).filter
      (fun q => decide (q ∉ s.corrupted))).length = n - s.corrupted.length := by
    have hforms : ((List.finRange n).filter (fun q => decide (q ∉ s.corrupted))).length
                = ((List.finRange n).filter (fun q => !decide (q ∈ s.corrupted))).length := by
      congr 1 ; apply List.filter_congr ; intro x _ ; simp
    rw [hforms] ; exact not_corrupted_count n s hB7 hbnd
  omega

/-- A correct voter for `(some b₀)` exists in `s` whenever the binary
    threshold for `b₀` has just crossed in the corrupt-action post-state
    (so the correctVoteCount in the post-state is positive when net of
    growing `corrupted`). Used for B3 and B4 of the corrupt action. -/
private theorem corrupt_extract_voter (n f : Nat) (s : State n) (i : Fin n)
    (b₀ : Bool) (bv : Option (Option Bool))
    (hbudget_new : s.corrupted.length + 1 ≤ f)
    (hthresh : s.corrupted.length + 1 + correctVoteCount n
      ({ s with corrupted := i :: s.corrupted, boundValue := bv } : State n)
      (some b₀) > f) :
    ∃ q, q ∉ s.corrupted ∧ (s.local_ q).voted (some b₀) = true := by
  have hcvc_le : correctVoteCount n
      ({ s with corrupted := i :: s.corrupted, boundValue := bv } : State n)
      (some b₀) ≤ correctVoteCount n s (some b₀) := by
    apply filter_length_mono
    intro q hq
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hq ⊢
    exact ⟨fun h => hq.1 (List.mem_cons_of_mem i h), hq.2⟩
  have hpos : correctVoteCount n s (some b₀) ≥ 1 := by omega
  obtain ⟨q, hq⟩ := List.exists_mem_of_length_pos
    (show 0 < ((List.finRange n).filter (fun r =>
      decide (r ∉ s.corrupted) && (s.local_ r).voted (some b₀))).length by
      unfold correctVoteCount at hpos ; omega)
  rw [List.mem_filter] at hq
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
  exact ⟨q, hq.2.1, hq.2.2⟩

/- **Inductive step for `bound_inv`** — by far the largest proof in the
   file. It case-splits on the action and discharges B1–B8 for each.

    The argument structure across actions:

    - `corrupt i` (~ corresponding case): adds a process to `corrupted`.
      The hard case is B2: a newly crossed ⊥ threshold combined with an
      existing correct binary decision must be ruled out. Done by combining
      `correct_voters_of_decision` with `vote_once_disjoint` to get a
      counting contradiction (uses `n > 3f`).

    - `recv ...`: most receive actions only update `*Recv` / `approved`,
      leaving voted/decided/corrupted untouched. These dispatch to a generic
      `recv_noop` helper that uses `bound_inv_congr`. The interesting case
      is `recv vote`, which can grow `voteRecv` and thus affect echo
      backing for B4 (handled via the buffer-vote-trace from `bca_inv`).

    - `send ...`: split on `t : MsgType`. `init`/`echo` only change `sent`
      (and possibly `echoed`), so they reduce to congruence. The hard case
      is `send vote`:
        * `vote (some b)` from a correct `src`: a new binary vote may
          newly cross `b`'s threshold; we use the *echo quorum* gate fact
          plus `echo_quorum_intersection` to forbid an opposite binary
          bound.
        * `vote none` (⊥) from a correct `src`: src adds to
          `correctVoteCount(none)` by exactly 1, possibly newly crossing
          the ⊥ threshold. The B2 sub-case is the hardest: the new ⊥
          bound combined with an existing correct binary decision must be
          contradicted. The proof applies `vote_once_disjoint` to the
          intermediate state (the post-state without the boundValue
          override), uses `hcnt_bin` to relate binary counts to those in
          `s`, and combines with `correct_voters_of_decision` plus the
          freshly crossed ⊥ threshold to derive `f < |corrupted|`,
          contradicting the budget.
        * Corrupt `src`: voted is unchanged so everything reduces to
          congruence.

    - `decide i mv`: only changes `decided`. The new decider's case
      requires linking the gate's `n − f` vote receipts to a correct voter
      via `correct_voters_of_decision`, then either matching an existing
      bound (B1) or contradicting a ⊥ bound via vote-once disjointness
      (B2).
-/
-- Tactic shorthand for "voted-unchanged" send sub-cases. Refers to local
-- identifiers `s`, `n`, `f`, `src`, `hbvinv`, `hB5`, and (optionally)
-- `hsrc_mem`, so it must be invoked in a context that binds them.
-- Closes a `countEchoRecv (post.local_ q) b = countEchoRecv (s.local_ q) b`
-- goal arising in the `send vote` cases of B4. echoRecv is unchanged at
-- every process (post differs from s only in `sent`/`voted`/buffer), so the
-- projection reduces.
set_option hygiene false in
syntax "echo_count_unchanged" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| echo_count_unchanged) => `(tactic|
      (simp only [countEchoRecv]
       apply congrArg ; apply List.filter_congr ; intro r _
       by_cases hqsrc : q = src
       · rw [hqsrc] ; simp
       · simp [hqsrc]))

-- Reduce a hypothesis on `decided` at the post-state of a `send` action to
-- the same hypothesis at `s` (decided is unchanged for every process).
-- Splits on `p = src` and uses `simp` to unfold the conditional.
set_option hygiene false in
syntax "extract_decided" ident "from" ident "as" term : tactic
set_option hygiene false in
macro_rules
  | `(tactic| extract_decided $h':ident from $h:ident as $t:term) => `(tactic|
      (have $h':ident : (s.local_ p).decided = $t := by
         by_cases hpsrc : p = src
         · subst hpsrc ; simp at $h:ident ; exact $h:ident
         · simp [hpsrc] at $h:ident ; exact $h:ident))

set_option hygiene false in
syntax "send_voted_unchanged" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| send_voted_unchanged) => `(tactic|
      (refine bound_inv_congr n f (s := s) rfl ?_ ?_ ?_ ?_ hbvinv
       all_goals first
         | (intro p v ; by_cases hpsrc : p = src
            · subst hpsrc ; first | simp [hsrc_mem] | simp
            · simp [hpsrc])
         | (intro p q b' hold ; by_cases hpsrc : p = src
            · subst hpsrc ; simp ; exact hold
            · simp [hpsrc] ; exact hold)
         | (refine Eq.trans (computeBound_congr n f (s := s) (s' := _)
              rfl ?_ rfl) hB5.symm
            intro p v
            by_cases hpsrc : p = src
            · subst hpsrc ; first | simp [hsrc_mem] | simp
            · simp [hpsrc])))

theorem bound_inv_step (hn : n > 3 * f) :
    ∀ input s s', (∃ i, ((bca n f input).actions i).fires s s') →
    bca_inv n f input s → bound_inv n f s → bound_inv n f s' := by
  intro input s s' ⟨action, hfire⟩ hbcainv hbvinv
  obtain ⟨hbudget, hetrace, _, hvtrace, _, _, _, hvback, hvagree, hecho_back, _, _⟩ := hbcainv
  cases action with
  -- ============================================================
  -- Case: corrupt i — turn process i Byzantine.
  -- All local fields stay the same; only `corrupted` and `boundValue`
  -- change. Hardest sub-goal is B2 (counting contradiction).
  -- ============================================================
  | corrupt i =>
    simp [bca, GatedAction.fires] at hfire
    obtain ⟨hgate, htrans⟩ := hfire
    subst htrans
    obtain ⟨hB1, hB2, hB3, hB4, hB5, hB6, hB7, hB8⟩ := hbvinv
    have hi_corr : i ∉ s.corrupted := hgate.1
    have hbudget_new : s.corrupted.length + 1 ≤ f := hgate.2
    have hcorr_sub : ∀ q, q ∉ (i :: s.corrupted) → q ∉ s.corrupted :=
      fun q hq h => hq (List.mem_cons_of_mem i h)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- B1: correct binary decision → new bound ∈ {some (some b), some none}
      intro p b hcp hdec
      have hcp' : isCorrect n s p := hcorr_sub p hcp
      -- Decided unchanged, so old B1 gives us the old bound
      rcases hB1 p b hcp' hdec with hold_b | hold_bot
      · -- old bound = some (some b); new bound preserves binary (possibly upgrading to ⊥)
        exact computeBound_preserves_binary n f _ b hold_b
      · -- old bound = some none; new bound stays some none
        right ; exact computeBound_preserves_bot n f _ hold_bot
    · -- B2: new bound = some none → no correct in s' has a binary decision
      intro hnew_bv p b hcp hdec
      have hcp' : isCorrect n s p := hcorr_sub p hcp
      -- Either old bound was already some none (apply old hB2), or ⊥ crossed in s₀
      rcases computeBound_eq_some_none n f _ hnew_bv with hold_bot | hthresh_new
      · exact hB2 hold_bot p b hcp' hdec
      · -- ⊥ newly crossed in s₀; combined with correct decision, derive contradiction
        rcases hB1 p b hcp' hdec with hold_b | hold_bot
        · -- Old bound was some (some b). From hB5, ⊥ was NOT crossed in s.
          have hcomp_eq : computeBound n f s = some (some b) := hB5.symm.trans hold_b
          have hold_not_bot : s.corrupted.length + correctVoteCount n s none ≤ 2 * f := by
            by_contra hbot
            have h1 : computeBound n f s = some none := by
              unfold computeBound ; simp [hbot]
            rw [h1] at hcomp_eq ; exact absurd hcomp_eq (by simp)
          have hlen : (i :: s.corrupted).length = s.corrupted.length + 1 := by simp
          rw [hlen] at hthresh_new
          have hcvc_none_le : correctVoteCount n
              ({ s with corrupted := i :: s.corrupted, boundValue := s.boundValue } : State n) none
              ≤ correctVoteCount n s none := by
            apply filter_length_mono
            intro q hq
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hq ⊢
            exact ⟨fun h => hq.1 (List.mem_cons_of_mem i h), hq.2⟩
          -- So correctVoteCount n s none ≥ 2f - |s.corrupted|
          have hcvc_none_ge : correctVoteCount n s none ≥ 2 * f - s.corrupted.length := by omega
          -- decision_backing + pigeonhole: correct(some b) ≥ n - f - |s.corrupted|
          have hvtrace_p : ∀ p q b, isCorrect n s q →
              (s.local_ p).voteRecv q (some b) = true → (s.local_ q).voted (some b) = true :=
            fun p q b hq hvr => hvtrace p q b hq hvr
          have hcnt := hvback p b hdec
          have hcvc_b_ge : correctVoteCount n s (some b) ≥ n - f - s.corrupted.length :=
            correct_voters_of_decision n f s p b hvtrace_p hcnt
          -- vote_once_disjoint: sum ≤ n - |s.corrupted|
          have hdisj := vote_once_disjoint n s hB6 hB7 (by omega : s.corrupted.length ≤ n) b
          -- Budget: |s.corrupted| ≤ f - 1 (from |s.corrupted| + 1 ≤ f)
          -- Combine: (n-f-|corr|) + (2f-|corr|) = n+f-2|corr| ≤ n - |corr| → f ≤ |corr|,
          -- contradicting |corr| ≤ f - 1
          omega
        · exact hB2 hold_bot p b hcp' hdec
    · -- B3: new bound = some (some b₀) → no correct in s' voted (some !b₀)
      intro b₀ hnew_bv p hcp
      have hcp' : isCorrect n s p := hcorr_sub p hcp
      rcases computeBound_eq_some_some n f _ b₀ hnew_bv with hold_same | ⟨_, _, hthresh⟩
      · -- Old bound was already some (some b₀); use old B3 (voted unchanged)
        exact hB3 b₀ hold_same p hcp'
      · -- Bound newly set; find a correct voter for b₀ and invoke vote_agreement
        have hlen : (i :: s.corrupted).length = s.corrupted.length + 1 := by simp
        rw [hlen] at hthresh
        obtain ⟨q, hq_corr, hq_voted⟩ :=
          corrupt_extract_voter n f s i b₀ s.boundValue hbudget_new hthresh
        -- q is a correct voter for b₀; by vote_agreement, p can't vote !b₀
        by_contra hvoted_opp
        have hvoted_opp' : (s.local_ p).voted (some (!b₀)) = true := by
          cases h : (s.local_ p).voted (some (!b₀)) with
          | true => rfl
          | false => exact absurd h hvoted_opp
        have hagree := hvagree q p b₀ (!b₀) hq_corr hcp' hq_voted hvoted_opp'
        exact absurd hagree (by cases b₀ <;> decide)
    · -- B4: new bound = some (some b₀) → ∃ p with echo quorum for b₀
      intro b₀ hnew_bv
      -- Use the helper to extract: either old bound was already some (some b₀)
      -- (reuse B4) or old bound was none and the threshold crossed in s₀
      rcases computeBound_eq_some_some n f _ b₀ hnew_bv with hold_same | ⟨hold_none, _, hthresh⟩
      · -- hold_same says s₀.boundValue = some (some b₀), i.e. s.boundValue = some (some b₀)
        exact hB4 b₀ hold_same
      · -- Threshold crossed in s₀: ≥ 1 correct voter for b₀ exists (using budget)
        have hlen : (i :: s.corrupted).length = s.corrupted.length + 1 := by simp
        rw [hlen] at hthresh
        obtain ⟨q, hq_corr, hq_voted⟩ :=
          corrupt_extract_voter n f s i b₀ s.boundValue hbudget_new hthresh
        exact ⟨q, hecho_back q b₀ hq_corr hq_voted⟩
    · -- B5: idempotence via the helper lemma
      exact (computeBound_idempotent n f { s with corrupted := i :: s.corrupted }).symm
    · -- B6
      intro p hcp v₁ v₂ hv1 hv2
      exact hB6 p (hcorr_sub p hcp) v₁ v₂ hv1 hv2
    · -- B7: new corrupted list is still Nodup (gate ensures i ∉ s.corrupted)
      exact List.nodup_cons.mpr ⟨hi_corr, hB7⟩
    · -- B8: if new bound = some none, ⊥ threshold holds in new state
      intro hnb
      -- correctVoteCount is independent of boundValue
      have hcvc_any : ∀ (bv : Option (Option Bool)) (v : Val),
          correctVoteCount n
            ({ s with corrupted := i :: s.corrupted, boundValue := bv } : State n) v
          = correctVoteCount n
            ({ s with corrupted := i :: s.corrupted, boundValue := s.boundValue } : State n) v := by
        intro _ _ ; rfl
      rw [hcvc_any]
      rcases computeBound_eq_some_none n f _ hnb with hold_bot | hthresh_new
      · -- Old bound was some none; apply hB8 at s. Removing i from the
        -- correct set drops correctVoteCount(none) by at most 1, but adds 1
        -- to |corrupted|, so the sum can only increase.
        have hs_bot : s.boundValue = some none := hold_bot
        have hold := hB8 hs_bot
        have hlen : (i :: s.corrupted).length = s.corrupted.length + 1 := by simp
        -- Key bound: cvc_s(none) ≤ cvc_s₀(none) + 1
        have hcvc_bound : correctVoteCount n s none ≤
            correctVoteCount n
              ({ s with corrupted := i :: s.corrupted, boundValue := s.boundValue } : State n)
              none + 1 := by
          unfold correctVoteCount
          have h1 : ((List.finRange n).filter (fun p =>
              decide (p ∉ s.corrupted) && (s.local_ p).voted none)).length
              ≤ (i :: ((List.finRange n).filter (fun p =>
                decide (p ∉ i :: s.corrupted) && (s.local_ p).voted none))).length := by
            apply nodup_sub_length
              ((finRange_nodup n).sublist List.filter_sublist)
            intro x hx
            simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hx
            simp only [List.mem_cons, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
            by_cases heq : x = i
            · left ; exact heq
            · right
              refine ⟨hx.1, ?_, hx.2.2⟩
              intro h
              rcases h with h1 | h1
              · exact heq h1
              · exact hx.2.1 h1
          simp only [List.length_cons] at h1
          exact h1
        -- Now: (|corr|+1) + cvc_s₀(none) > 2f
        show (i :: s.corrupted).length + _ > 2 * f
        rw [hlen]
        omega
      · exact hthresh_new
  -- ============================================================
  -- Case: recv src dst t mv — receive a message at dst.
  -- Most branches only update `*Recv`/`approved`; voted/decided/
  -- corrupted are unchanged so the invariant transfers via
  -- `bound_inv_congr` (encapsulated as `recv_noop`).
  -- ============================================================
  | recv src dst t mv =>
    -- Split on `t` and `mv` BEFORE extracting htrans so the nested match
    -- reduces before `subst` introduces dependent-match artifacts.
    -- Helper for "no-op" branches: state changes only in buffer, `bound_inv` transfers directly.
    have recv_noop : ∀ (htrans' : s' = { s with
          buffer := fun m => !decide (m = { src := src, dst := dst, type := t, val := mv }) && s.buffer m,
          local_ := fun p => if p = dst then s.local_ dst else s.local_ p,
          boundValue := computeBound n f { s with
            buffer := fun m => !decide (m = { src := src, dst := dst, type := t, val := mv }) && s.buffer m,
            local_ := fun p => if p = dst then s.local_ dst else s.local_ p } }),
        bound_inv n f s' := by
      intro htrans'
      have hlocal_eq :
          (fun p => if p = dst then s.local_ dst else s.local_ p) = s.local_ := by
        funext p ; by_cases hpdst : p = dst <;> simp [hpdst]
      rw [hlocal_eq] at htrans'
      subst htrans'
      refine bound_inv_congr n f (s := s) rfl (fun _ _ => rfl) (fun _ _ => Iff.rfl)
        (fun _ _ _ h => h) ?_ hbvinv
      exact (computeBound_congr n f (s := s) rfl (fun _ _ => rfl) rfl).trans
        hbvinv.2.2.2.2.1.symm
    -- Helper for "update-dst" branches: only initRecv/approved/echoRecv/voteRecv may change at dst.
    -- voted/decided unchanged; echoRecv may grow but the congruence accepts that.
    have recv_update : ∀ (ls' : LocalState n)
        (_hvoted_eq : (ls' : LocalState n).voted = (s.local_ dst).voted)
        (_hdecided_eq : ls'.decided = (s.local_ dst).decided)
        (_hecho_mono : ∀ q b, (s.local_ dst).echoRecv q b = true → ls'.echoRecv q b = true)
        (htrans' : s' = { s with
          buffer := fun m => !decide (m = { src := src, dst := dst, type := t, val := mv }) && s.buffer m,
          local_ := fun p => if p = dst then ls' else s.local_ p,
          boundValue := computeBound n f { s with
            buffer := fun m => !decide (m = { src := src, dst := dst, type := t, val := mv }) && s.buffer m,
            local_ := fun p => if p = dst then ls' else s.local_ p } }),
        bound_inv n f s' := by
      intro ls' hv_eq hd_eq he_mono htrans'
      subst htrans'
      have hv : ∀ (p : Fin n) v,
          ((fun p => if p = dst then ls' else s.local_ p) p).voted v = (s.local_ p).voted v := by
        intro p v ; by_cases hpdst : p = dst
        · subst hpdst ; simp [hv_eq]
        · simp [hpdst]
      refine bound_inv_congr n f (s := s) rfl hv ?_ ?_ ?_ hbvinv
      · intro p v ; by_cases hpdst : p = dst
        · subst hpdst ; simp [hd_eq]
        · simp [hpdst]
      · intro p q b hold ; by_cases hpdst : p = dst
        · subst hpdst ; simp ; exact he_mono q b hold
        · simp [hpdst] ; exact hold
      · refine Eq.trans (b := computeBound n f s) ?_ hbvinv.2.2.2.2.1.symm
        exact computeBound_congr n f (s := s)
          (s' := { s with
            buffer := fun m => !decide (m = { src := src, dst := dst, type := t, val := mv }) && s.buffer m,
            local_ := fun p => if p = dst then ls' else s.local_ p,
            boundValue := s.boundValue })
          rfl hv rfl
    cases t with
    | init =>
      cases mv with
      | some b =>
        simp [bca, GatedAction.fires] at hfire
        obtain ⟨hgate, htrans⟩ := hfire
        by_cases hnew : (s.local_ dst).initRecv src b = false
        · rw [if_pos hnew] at htrans
          exact recv_update { s.local_ dst with
            initRecv := fun q w =>
              decide (q = src) && decide (w = b) || (s.local_ dst).initRecv q w,
            approved := fun w =>
              decide (w = b) && decide (approveThreshold n f ≤ countInitRecv n (s.local_ dst) b + 1)
              || (s.local_ dst).approved w }
            rfl rfl (fun _ _ h => h) htrans
        · simp only [if_neg hnew] at htrans ; exact recv_noop htrans
      | none =>
        simp [bca, GatedAction.fires] at hfire
        obtain ⟨_, htrans⟩ := hfire
        exact recv_noop htrans
    | echo =>
      cases mv with
      | some b =>
        simp [bca, GatedAction.fires] at hfire
        obtain ⟨hgate, htrans⟩ := hfire
        by_cases hnew : (s.local_ dst).echoRecv src b = false
        · rw [if_pos hnew] at htrans
          exact recv_update { s.local_ dst with
            echoRecv := fun q w =>
              decide (q = src) && decide (w = b) || (s.local_ dst).echoRecv q w }
            rfl rfl (fun q w h => by simp ; right ; exact h) htrans
        · simp only [if_neg hnew] at htrans ; exact recv_noop htrans
      | none =>
        simp [bca, GatedAction.fires] at hfire
        obtain ⟨_, htrans⟩ := hfire
        exact recv_noop htrans
    | vote =>
      simp [bca, GatedAction.fires] at hfire
      obtain ⟨hgate, htrans⟩ := hfire
      by_cases hnew : (s.local_ dst).voteRecv src mv = false
      · rw [if_pos hnew] at htrans
        exact recv_update { s.local_ dst with
          voteRecv := fun q w =>
            decide (q = src) && decide (w = mv) || (s.local_ dst).voteRecv q w }
          rfl rfl (fun _ _ h => h) htrans
      · simp only [if_neg hnew] at htrans ; exact recv_noop htrans
  -- ============================================================
  -- Case: send src dst t mv — src emits a message.
  -- For `init`/`echo` only `sent`/`echoed` change, so the invariant
  -- transfers via congruence. For `vote` we get a real new vote which
  -- can move `boundValue` — this is the largest sub-case.
  -- ============================================================
  | send src dst t mv =>
    -- Case-split on `t` first so the nested `match t with` in the transition
    -- reduces before `subst htrans`, avoiding dependent-match issues.
    cases t with
    -- ---------- send init ---------- (voted/decided unchanged)
    | init =>
      simp [bca, GatedAction.fires] at hfire
      obtain ⟨_, htrans⟩ := hfire
      subst htrans
      have hB5 := hbvinv.2.2.2.2.1
      send_voted_unchanged
    -- ---------- send echo ---------- (only `sent`/`echoed` change)
    | echo =>
      -- Split on mv before subst to avoid dependent match
      cases mv with
      | some b =>
        simp [bca, GatedAction.fires] at hfire
        obtain ⟨_, htrans⟩ := hfire
        subst htrans
        have hB5 := hbvinv.2.2.2.2.1
        send_voted_unchanged
      | none =>
        -- mv = none: the correct-case gate match is False, so src must be corrupt.
        -- Transition proceeds normally; voted still unchanged.
        simp [bca, GatedAction.fires] at hfire
        obtain ⟨_, htrans⟩ := hfire
        subst htrans
        have hB5 := hbvinv.2.2.2.2.1
        send_voted_unchanged
    -- ---------- send vote ---------- (the hard sub-case: voted grows)
    -- We further split on `mv` (binary or ⊥) and on whether `src` is
    -- correct or corrupt. Corrupt-src branches are trivial congruences.
    | vote =>
      -- Split on mv so the match in the gate/transition reduces cleanly
      cases mv with
      -- send vote (some b): may newly cross the binary `b` threshold.
      | some b =>
        simp [bca, GatedAction.fires] at hfire
        obtain ⟨hgate, htrans⟩ := hfire
        subst htrans
        -- Sub-split on whether src is correct or corrupt
        by_cases hsrc_mem : src ∈ s.corrupted
        case neg =>
          -- Correct src voting (some b): voted grows at src
          obtain ⟨hB1, hB2, hB3, hB4, hB5, hB6, hB7, hB8⟩ := hbvinv
          have hgate_src := hgate.resolve_left hsrc_mem
          have hgate_voted_only : ∀ w, (s.local_ src).voted w = true → w = some b :=
            hgate_src.2.2.1
          have hold_not_voted : ∀ w, w ≠ some b → (s.local_ src).voted w = false := by
            intro w hne
            cases h : (s.local_ src).voted w
            · rfl
            · exact absurd (hgate_voted_only w h) hne
          have hecho_src : echoThreshold n f ≤ countEchoRecv n (s.local_ src) b :=
            hgate_src.2.2.2
          -- Shorthand for the post-state struct (parameterized by bv)
          let s_post : Option (Option Bool) → State n := fun bv => { s with
            buffer := fun m =>
              decide (m = { src := src, dst := dst, type := MsgType.vote, val := some b })
              || s.buffer m,
            local_ := fun p' => if p' = src then
              { s.local_ src with
                sent := fun d t' w =>
                  decide (d = dst) && (decide (t' = MsgType.vote) && decide (w = some b))
                  || (s.local_ src).sent d t' w,
                voted := if src ∈ s.corrupted then (s.local_ src).voted
                  else fun w => decide (w = some b) || (s.local_ src).voted w }
              else s.local_ p',
            boundValue := bv }
          -- Shared count helper: for any value v ≠ some b, the post-state's
          -- correctVoteCount equals s's (src's new vote is `some b`, not `v`).
          have hcnt_other : ∀ (v : Val) (bv : Option (Option Bool)), v ≠ some b →
              correctVoteCount n (s_post bv) v = correctVoteCount n s v := by
            intro v bv hne
            simp only [correctVoteCount, s_post]
            apply congrArg ; apply List.filter_congr ; intro q _
            by_cases hqsrc : q = src
            · rw [hqsrc] ; simp [hsrc_mem, hold_not_voted v hne, hne]
            · simp [hqsrc]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · -- B1: decided unchanged → new bound preserves (possibly upgrading to ⊥)
            intro p b' hcp hdec
            extract_decided hdec' from hdec as some (some b')
            rcases hB1 p b' hcp hdec' with hold_b | hold_bot
            · exact computeBound_preserves_binary n f _ b' hold_b
            · right ; exact computeBound_preserves_bot n f _ hold_bot
          · -- B2: new = some none → no correct binary decision
            intro hnb p b' hcp hdec
            extract_decided hdec' from hdec as some (some b')
            rcases computeBound_eq_some_none n f _ hnb with hold_bot | hthresh
            · exact hB2 hold_bot p b' hcp hdec'
            · -- ⊥ crossed in s₀; since cnt(none) unchanged, ⊥ must have crossed in s
              rw [hcnt_other none _ (by simp)] at hthresh
              have hbv_s : s.boundValue = some none := by
                rw [hB5] ; unfold computeBound ; simp [hthresh]
              exact hB2 hbv_s p b' hcp hdec'
          · -- B3: new bound = some (some b₀) → no correct voted (some !b₀)
            intro b₀ hnb p hcp
            -- First derive: no correct in s voted (some !b). Uses echo_quorum_intersection
            -- with src's echo quorum for b + another correct's echo quorum for !b.
            have hno_opp : ∀ q, q ∉ s.corrupted → (s.local_ q).voted (some (!b)) = false := by
              intro q hq
              by_contra hv
              have hv' : (s.local_ q).voted (some (!b)) = true := by
                cases h : (s.local_ q).voted (some (!b)) with
                | true => rfl
                | false => exact absurd h hv
              have hecho_q := hecho_back q (!b) hq hv'
              have h_eq := echo_quorum_intersection hn b (!b) src q
                (fun p q b => (s.local_ p).echoRecv q b)
                (fun p => (s.local_ p).echoed)
                s.corrupted hbudget
                (fun p q b hcp heq => hetrace p q b hcp heq)
                hecho_src hecho_q
              exact absurd h_eq (by cases b <;> decide)
            -- Now handle p = src vs p ≠ src
            by_cases hpsrc : p = src
            · -- p = src: don't subst, use rewriting instead
              rw [hpsrc]
              by_cases hb₀ : b₀ = !b
              subst hb₀
              rcases computeBound_eq_some_some n f _ (!b) hnb with hold_same | ⟨hold_none, _, hthresh⟩
              · obtain ⟨q_wit, hq_wit⟩ := hB4 (!b) hold_same
                have h_eq := echo_quorum_intersection hn (!b) b q_wit src
                  (fun p q b => (s.local_ p).echoRecv q b)
                  (fun p => (s.local_ p).echoed)
                  s.corrupted hbudget
                  (fun p q b hcp heq => hetrace p q b hcp heq)
                  hq_wit hecho_src
                exact absurd h_eq (by cases b <;> decide)
              · -- Newly crossed for (!(!b)) = b. But src's vote does add to cnt(some b)
                -- so threshold for b could cross. But goal was `some (some !b)`, which
                -- requires threshold for !b, not b.
                -- Wait: b₀ = !b, so threshold is for (some !b). Let's compute cnt(!b)
                -- in s₀: src's new vote is (some b), not (some !b). So cnt(!b) unchanged.
                -- And in s, cnt(!b) didn't cross (bound was none). Contradiction.
                exfalso
                rw [hcnt_other (some (!b)) _ (by cases b <;> decide)] at hthresh
                -- hthresh : |corr| + cnt_s(!b) > f. But computeBound s = none means cnt didn't cross.
                have ⟨_, hno_f, hno_t⟩ := computeBound_eq_none n f s (hB5.symm.trans hold_none)
                cases b with
                | false => exact absurd hthresh (by simp at hthresh ; omega)
                | true => exact absurd hthresh (by simp at hthresh ; omega)
              · -- b₀ ≠ !b: new voted(!b₀) = decide (!b₀ = b) || old voted = false
                have hne : (some (!b₀) : Val) ≠ some b := by
                  intro h ; injection h with h ; exact hb₀ (by rw [← h]; cases b₀ <;> rfl)
                simp [hsrc_mem, hold_not_voted _ hne]
                cases b <;> cases b₀ <;> simp at hb₀ ⊢
            · -- p ≠ src: voted unchanged
              simp [hpsrc]
              rcases computeBound_eq_some_some n f _ b₀ hnb with hold_same | ⟨hold_none, _, hthresh⟩
              · exact hB3 b₀ hold_same p hcp
              · -- Newly crossed. If b₀ = b: use hno_opp (p ≠ src, so hcp : isCorrect s p).
                -- If b₀ ≠ b: contradict (cnt for !b unchanged).
                by_cases hbeq : b₀ = b
                · subst hbeq ; exact hno_opp p hcp
                · exfalso
                  -- b₀ ≠ b: cnt(b₀) in s₀ = cnt(b₀) in s (src's vote is b ≠ b₀)
                  rw [hcnt_other (some b₀) _ (fun h => hbeq (by injection h))] at hthresh
                  have ⟨_, hno_f, hno_t⟩ :=
                    computeBound_eq_none n f s (hB5.symm.trans hold_none)
                  cases b₀ with
                  | false => exact absurd hthresh (by simp at hthresh ; omega)
                  | true => exact absurd hthresh (by simp at hthresh ; omega)
          · -- B4: new bound = some (some b₀) → ∃ echo witness
            intro b₀ hnb
            rcases computeBound_eq_some_some n f _ b₀ hnb with hold_same | ⟨hold_none, _, hthresh⟩
            · -- Same bound: use old hB4 (echoRecv unchanged)
              obtain ⟨q, hq⟩ := hB4 b₀ hold_same
              refine ⟨q, ?_⟩
              have heq : countEchoRecv n ((s_post s.boundValue).local_ q) b₀
                  = countEchoRecv n (s.local_ q) b₀ := by
                simp only [s_post] ; echo_count_unchanged
              rw [heq] ; exact hq
            · -- Newly crossed: if b₀ = b use src, else contradict
              by_cases hbeq : b₀ = b
              · rw [hbeq]
                refine ⟨src, ?_⟩
                have heq : countEchoRecv n ((s_post s.boundValue).local_ src) b
                    = countEchoRecv n (s.local_ src) b := by
                  simp only [countEchoRecv, s_post]
                  apply congrArg ; apply List.filter_congr ; intro r _ ; simp
                rw [heq] ; exact hecho_src
              · exfalso
                rw [hcnt_other (some b₀) _ (fun h => hbeq (by injection h))] at hthresh
                have ⟨_, hno_f, hno_t⟩ :=
                  computeBound_eq_none n f s (hB5.symm.trans hold_none)
                cases b₀ with
                | false => exact absurd hthresh (by simp at hthresh ; omega)
                | true => exact absurd hthresh (by simp at hthresh ; omega)
          · -- B5: idempotence
            exact (computeBound_idempotent n f _).symm
          · -- B6: vote-once. For p = src, all old votes were `some b`,
            --     and the new vote is also `some b`, so still single-valued.
            intro p hcp v₁ v₂ hv1 hv2
            by_cases hpsrc : p = src
            · subst hpsrc
              simp [hsrc_mem] at hv1 hv2
              -- hv1, hv2 each say: w = some b ∨ old voted w = true.
              -- By the gate, any old voted w = true → w = some b. So both are some b.
              have h1 : v₁ = some b := by
                rcases hv1 with rfl | h
                · rfl
                · exact hgate_voted_only v₁ h
              have h2 : v₂ = some b := by
                rcases hv2 with rfl | h
                · rfl
                · exact hgate_voted_only v₂ h
              rw [h1, h2]
            · simp [hpsrc] at hv1 hv2
              exact hB6 p hcp v₁ v₂ hv1 hv2
          · -- B7: corrupted unchanged
            exact hB7
          · -- B8: vote (some b) doesn't change correctVoteCount(none)
            intro hnb
            rw [hcnt_other none _ (by simp)]
            rcases computeBound_eq_some_none n f _ hnb with hold_bot | hthresh
            · exact hB8 hold_bot
            · rw [hcnt_other none _ (by simp)] at hthresh ; exact hthresh
        case pos =>
          -- Corrupt src: voted unchanged
          have hB5 := hbvinv.2.2.2.2.1
          send_voted_unchanged
      -- send vote none (⊥): adds 1 to `correctVoteCount(none)` if src
      -- is correct, possibly newly crossing the ⊥ threshold.
      | none =>
        simp [bca, GatedAction.fires] at hfire
        obtain ⟨hgate, htrans⟩ := hfire
        subst htrans
        by_cases hsrc_mem : src ∈ s.corrupted
        case pos =>
          -- Corrupt src: voted unchanged
          have hB5 := hbvinv.2.2.2.2.1
          send_voted_unchanged
        case neg =>
          -- Correct src voting ⊥: adds to correctVoteCount(none)
          obtain ⟨hB1, hB2, hB3, hB4, hB5, hB6, hB7, hB8⟩ := hbvinv
          have hgate_src := hgate.resolve_left hsrc_mem
          have hgate_voted_only : ∀ w, (s.local_ src).voted w = true → w = none :=
            hgate_src.2.2.1
          have hold_not_voted : ∀ w, w ≠ none → (s.local_ src).voted w = false := by
            intro w hne
            cases h : (s.local_ src).voted w
            · rfl
            · exact absurd (hgate_voted_only w h) hne
          -- Shorthand for the post-state struct (parameterized by bv)
          let s_post : Option (Option Bool) → State n := fun bv => { s with
            buffer := fun m =>
              decide (m = { src := src, dst := dst, type := MsgType.vote, val := none })
              || s.buffer m,
            local_ := fun p' => if p' = src then
              { s.local_ src with
                sent := fun d t' w =>
                  decide (d = dst) && (decide (t' = MsgType.vote) && decide (w = none))
                  || (s.local_ src).sent d t' w,
                voted := if src ∈ s.corrupted then (s.local_ src).voted
                  else fun w => decide (w = none) || (s.local_ src).voted w }
              else s.local_ p',
            boundValue := bv }
          -- correctVoteCount(some b₀) unchanged (src votes none, not (some b₀))
          have hcnt_bin : ∀ (b₀ : Bool) (bv : Option (Option Bool)),
              correctVoteCount n (s_post bv) (some b₀) = correctVoteCount n s (some b₀) := by
            intro b₀ bv
            simp only [correctVoteCount, s_post]
            apply congrArg ; apply List.filter_congr ; intro q _
            by_cases hqsrc : q = src
            · rw [hqsrc] ; simp [hsrc_mem, hold_not_voted (some b₀) (by simp)]
            · simp [hqsrc]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · -- B1
            intro p b' hcp hdec
            extract_decided hdec' from hdec as some (some b')
            rcases hB1 p b' hcp hdec' with hold_b | hold_bot
            · exact computeBound_preserves_binary n f _ b' hold_b
            · right ; exact computeBound_preserves_bot n f _ hold_bot
          · -- B2: new = some none → no correct binary decision
            intro hnb p b' hcp hdec
            extract_decided hdec' from hdec as some (some b')
            rcases hB1 p b' hcp hdec' with hold_b | hold_bot
            · -- Old bound = some (some b'); new = some none requires ⊥ newly crossed.
              -- Counting contradiction (no need for the +1: vote_once at new state
              -- + binary backing already exceeds n − |corr|).
              rcases computeBound_eq_some_none n f _ hnb with hold_bot' | hthresh
              · exact hB2 hold_bot' p b' hcp hdec'
              · exfalso
                -- vote-once at new struct (∀ bv): new voted at src is monotonically
                -- the union of old voted (which only includes none) with `none`,
                -- so still single-valued (none); vote-once preserved.
                have hB6_new : ∀ (bv : Option (Option Bool)) p, isCorrect n (s_post bv) p →
                    ∀ v₁ v₂, ((s_post bv).local_ p).voted v₁ = true →
                      ((s_post bv).local_ p).voted v₂ = true → v₁ = v₂ := by
                  intro bv p hcp v₁ v₂ hv1 hv2
                  simp only [s_post] at hv1 hv2
                  by_cases hpsrc : p = src
                  · subst hpsrc
                    simp [hsrc_mem] at hv1 hv2
                    have h1 : v₁ = none := by
                      rcases hv1 with rfl | h
                      · rfl
                      · exact hgate_voted_only v₁ h
                    have h2 : v₂ = none := by
                      rcases hv2 with rfl | h
                      · rfl
                      · exact hgate_voted_only v₂ h
                    rw [h1, h2]
                  · simp [hpsrc] at hv1 hv2
                    exact hB6 p hcp v₁ v₂ hv1 hv2
                -- vote_once_disjoint at the new state.
                have hdisj := vote_once_disjoint n (s_post s.boundValue)
                  (hB6_new s.boundValue) hB7 (by show s.corrupted.length ≤ n; omega) b'
                rw [hcnt_bin] at hdisj
                -- Bridge hthresh to s_post form via defeq
                have hthresh' : s.corrupted.length +
                    correctVoteCount n (s_post s.boundValue) none > 2 * f := hthresh
                clear hthresh
                have hcorr_eq : (s_post s.boundValue).corrupted.length = s.corrupted.length :=
                  rfl
                have hvtrace_p : ∀ p q b, isCorrect n s q →
                    (s.local_ p).voteRecv q (some b) = true → (s.local_ q).voted (some b) = true :=
                  fun p q b hq hvr => hvtrace p q b hq hvr
                have hcnt_backing := hvback p b' hdec'
                have hcvc_b_ge := correct_voters_of_decision n f s p b' hvtrace_p hcnt_backing
                omega
            · exact hB2 hold_bot p b' hcp hdec'
          · -- B3
            intro b₀ hnb p hcp
            rcases computeBound_eq_some_some n f _ b₀ hnb with hold_same | ⟨hold_none, _, hthresh⟩
            · by_cases hpsrc : p = src
              · rw [hpsrc] ; simp [hsrc_mem, hold_not_voted (some (!b₀)) (by simp)]
              · simp [hpsrc] ; exact hB3 b₀ hold_same p hcp
            · exfalso
              rw [hcnt_bin] at hthresh
              have ⟨_, hno_f, hno_t⟩ :=
                computeBound_eq_none n f s (hB5.symm.trans hold_none)
              cases b₀ with
              | false => exact absurd hthresh (by simp at hthresh ; omega)
              | true => exact absurd hthresh (by simp at hthresh ; omega)
          · -- B4
            intro b₀ hnb
            rcases computeBound_eq_some_some n f _ b₀ hnb with hold_same | ⟨hold_none, _, hthresh⟩
            · obtain ⟨q, hq⟩ := hB4 b₀ hold_same
              refine ⟨q, ?_⟩
              have heq : countEchoRecv n ((s_post s.boundValue).local_ q) b₀
                  = countEchoRecv n (s.local_ q) b₀ := by
                simp only [s_post] ; echo_count_unchanged
              rw [heq] ; exact hq
            · exfalso
              rw [hcnt_bin] at hthresh
              have ⟨_, hno_f, hno_t⟩ :=
                computeBound_eq_none n f s (hB5.symm.trans hold_none)
              cases b₀ with
              | false => exact absurd hthresh (by simp at hthresh ; omega)
              | true => exact absurd hthresh (by simp at hthresh ; omega)
          · -- B5: idempotence
            exact (computeBound_idempotent n f _).symm
          · -- B6: vote-once. Same shape as before but the gate now allows
            -- repeated voting of `none`; both v₁ and v₂ collapse to `none`.
            intro p hcp v₁ v₂ hv1 hv2
            by_cases hpsrc : p = src
            · subst hpsrc
              simp [hsrc_mem] at hv1 hv2
              have h1 : v₁ = none := by
                rcases hv1 with rfl | h
                · rfl
                · exact hgate_voted_only v₁ h
              have h2 : v₂ = none := by
                rcases hv2 with rfl | h
                · rfl
                · exact hgate_voted_only v₂ h
              rw [h1, h2]
            · simp [hpsrc] at hv1 hv2
              exact hB6 p hcp v₁ v₂ hv1 hv2
          · -- B7
            exact hB7
          · -- B8: new = some none → ⊥ threshold in new state
            intro hnb
            -- Define the intermediate state (no boundValue override) once
            let sInter : State n := { s with
              buffer := fun m =>
                decide (m = { src := src, dst := dst, type := MsgType.vote, val := none })
                || s.buffer m,
              local_ := fun p' => if p' = src then
                { s.local_ src with
                  sent := fun d t' w =>
                    decide (d = dst) && (decide (t' = MsgType.vote) && decide (w = none))
                    || (s.local_ src).sent d t' w,
                  voted := if src ∈ s.corrupted then (s.local_ src).voted
                    else fun w => decide (w = none) || (s.local_ src).voted w }
                else s.local_ p' }
            -- Key: cnt(none) at sInter ≥ cnt_s(none) (src added its vote)
            have hcnt_ge : correctVoteCount n s none ≤ correctVoteCount n sInter none := by
              apply filter_length_mono
              intro q hq
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hq ⊢
              refine ⟨hq.1, ?_⟩
              by_cases hqsrc : q = src
              · show ((fun p' => if p' = src then _ else s.local_ p') q).voted none = true
                rw [hqsrc] ; simp [hsrc_mem]
              · show ((fun p' => if p' = src then _ else s.local_ p') q).voted none = true
                simp [hqsrc] ; exact hq.2
            -- The goal's state differs from sInter only in boundValue; use the helper
            have hcnt_goal_eq : correctVoteCount n
                ({ sInter with boundValue := computeBound n f sInter } : State n) none
                = correctVoteCount n sInter none :=
              correctVoteCount_with_bv n sInter (computeBound n f sInter) none
            -- Also s.corrupted.length = sInter.corrupted.length
            have hcorr_eq : sInter.corrupted = s.corrupted := rfl
            rcases computeBound_eq_some_none n f _ hnb with hold_bot | hthresh
            · have hold_bound : s.boundValue = some none := hold_bot
              have hB8_s := hB8 hold_bound
              show s.corrupted.length + correctVoteCount n
                  ({ sInter with boundValue := computeBound n f sInter } : State n) none > 2 * f
              rw [hcnt_goal_eq]
              omega
            · -- hthresh is about the goal's state; normalize via helper
              show s.corrupted.length + correctVoteCount n
                  ({ sInter with boundValue := computeBound n f sInter } : State n) none > 2 * f
              show sInter.corrupted.length + _ > 2 * f
              exact hthresh
  -- ============================================================
  -- Case: decide i mv — process i records its decision.
  -- Only `decided` changes; `voted`/`echoRecv`/`corrupted` are
  -- untouched, so the new bound equals `s.boundValue`. The hard
  -- sub-cases (B1, B2) must verify that the *new* decision at i is
  -- consistent with the current bound, using the gate's vote-count
  -- threshold to find a correct backing voter.
  -- ============================================================
  | decide i mv =>
    simp [bca, GatedAction.fires] at hfire
    obtain ⟨hgate, htrans⟩ := hfire
    subst htrans
    obtain ⟨hB1, hB2, hB3, hB4, hB5, hB6, hB7, hB8⟩ := hbvinv
    -- Gate facts
    have hi_correct : isCorrect n s i := hgate.1
    have hi_not_decided : (s.local_ i).decided = none := hgate.2.1
    -- Helpers: at each p, voted and echoRecv agree with s; decided agrees except at i
    have hvoted_eq : ∀ (p : Fin n) (v : Val),
        ((fun p => if p = i then { s.local_ i with decided := some mv }
          else s.local_ p) p).voted v = (s.local_ p).voted v := by
      intro p v
      by_cases hpi : p = i
      · subst hpi ; simp
      · simp [hpi]
    have hecho_eq : ∀ (p : Fin n) (q : Fin n) (b : Bool),
        ((fun p => if p = i then { s.local_ i with decided := some mv }
          else s.local_ p) p).echoRecv q b = (s.local_ p).echoRecv q b := by
      intro p q b
      by_cases hpi : p = i
      · subst hpi ; simp
      · simp [hpi]
    -- The new boundValue equals s.boundValue (via computeBound_congr + hB5)
    have hnew_bv : (computeBound n f
        ({ s with local_ := fun p => if p = i
          then { s.local_ i with decided := some mv } else s.local_ p } : State n))
        = s.boundValue := by
      have := computeBound_congr n f (s := s)
        (s' := { s with local_ := fun p => if p = i
          then { s.local_ i with decided := some mv } else s.local_ p })
        rfl hvoted_eq rfl
      rw [this] ; exact hB5.symm
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- B1: correct binary decision → new bound ∈ {some (some b), some none}
      intro p b hcp hdec
      by_cases hpi : p = i
      · -- New decider i
        subst hpi
        simp at hdec
        -- After simp, hdec : mv = some b
        cases mv with
        | none => exact absurd hdec (by simp)
        | some b' =>
          -- hdec : some b' = some b (or b' = b after simp)
          simp at hdec ; subst hdec
          -- Now need: new bound ∈ {some (some b'), some none}.
          -- new bound = s.boundValue. Get correct voter from gate.
          rw [hnew_bv]
          have hcnt : countVoteRecv n (s.local_ p) (some b') ≥ n - f := by
            have := hgate.2.2
            unfold returnThreshold at this
            exact this
          have hvtrace' : ∀ p q b, isCorrect n s q →
              (s.local_ p).voteRecv q (some b) = true → (s.local_ q).voted (some b) = true :=
            fun p q b hq hvr => hvtrace p q b hq hvr
          have hcvc_ge := correct_voters_of_decision n f s p b' hvtrace' hcnt
          have hcvc_pos : correctVoteCount n s (some b') ≥ 1 := by
            have : n - f > f := by omega
            omega
          -- ∃ correct voter r for (some b')
          obtain ⟨r, hr⟩ := List.exists_mem_of_length_pos
            (show 0 < ((List.finRange n).filter (fun q =>
              decide (q ∉ s.corrupted) && (s.local_ q).voted (some b'))).length by
              unfold correctVoteCount at hcvc_pos ; omega)
          rw [List.mem_filter] at hr
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
          have hr_corr : isCorrect n s r := hr.2.1
          have hr_voted : (s.local_ r).voted (some b') = true := hr.2.2
          have hr_echo := hecho_back r b' hr_corr hr_voted
          -- Case on s.boundValue via hB5
          -- Since |corrupted| + correctVoteCount(some b') > f (via hcvc_ge and n > 3f),
          -- the binary threshold for b' has crossed in s, so s.boundValue ≠ none.
          have hthresh_b' : s.corrupted.length + correctVoteCount n s (some b') > f := by omega
          cases h_bv : s.boundValue with
          | none =>
            exfalso
            have ⟨_, hno_f, hno_t⟩ := computeBound_eq_none n f s (hB5.symm.trans h_bv)
            cases b' <;> omega
          | some ov =>
            cases ov with
            | none => right ; rfl
            | some b_old =>
              left
              -- Use B4 to get echo witness for b_old, then echo_quorum_intersection
              obtain ⟨q_old, hq_old⟩ := hB4 b_old h_bv
              have h_unique : b_old = b' := echo_quorum_intersection hn b_old b' q_old r
                (fun p q b => (s.local_ p).echoRecv q b)
                (fun p => (s.local_ p).echoed)
                s.corrupted hbudget
                (fun p q b hcp heq => hetrace p q b hcp heq)
                hq_old hr_echo
              rw [h_unique]
      · -- Old decider
        have hcp' : isCorrect n s p := hcp
        have hdec' : (s.local_ p).decided = some (some b) := by
          simp [hpi] at hdec ; exact hdec
        rw [hnew_bv]
        exact hB1 p b hcp' hdec'
    · -- B2: new bound = some none → no correct in s' has binary decision
      intro hnb p b hcp hdec
      rw [hnew_bv] at hnb
      by_cases hpi : p = i
      · -- New decider i with decided = some mv; if mv = some b, need contradiction
        subst hpi
        simp at hdec
        cases mv with
        | none => exact absurd hdec (by simp)
        | some b' =>
          simp at hdec ; subst hdec
          -- Counting contradiction: same as corrupt B2
          have hcnt : countVoteRecv n (s.local_ p) (some b') ≥ n - f := by
            have := hgate.2.2
            unfold returnThreshold at this
            exact this
          have hvtrace' : ∀ p q b, isCorrect n s q →
              (s.local_ p).voteRecv q (some b) = true → (s.local_ q).voted (some b) = true :=
            fun p q b hq hvr => hvtrace p q b hq hvr
          have hcvc_b_ge := correct_voters_of_decision n f s p b' hvtrace' hcnt
          -- hB8 directly gives ⊥ threshold crossed in s
          have hbot_crossed := hB8 hnb
          have hdisj := vote_once_disjoint n s hB6 hB7 (by omega : s.corrupted.length ≤ n) b'
          omega
      · -- Old decider: apply old hB2
        have hcp' : isCorrect n s p := hcp
        have hdec' : (s.local_ p).decided = some (some b) := by
          simp [hpi] at hdec ; exact hdec
        exact hB2 hnb p b hcp' hdec'
    · -- B3: new bound = some (some b₀) → no correct voted (some !b₀)
      -- voted unchanged, bound = s.boundValue
      intro b₀ hnb p hcp
      rw [hnew_bv] at hnb
      rw [hvoted_eq p (some (!b₀))]
      exact hB3 b₀ hnb p hcp
    · -- B4: new bound = some (some b₀) → ∃ p with echo quorum for b₀
      intro b₀ hnb
      rw [hnew_bv] at hnb
      obtain ⟨q, hq⟩ := hB4 b₀ hnb
      refine ⟨q, ?_⟩
      have : countEchoRecv n (s.local_ q) b₀ = countEchoRecv n
          ((fun p => if p = i then { s.local_ i with decided := some mv }
            else s.local_ p) q) b₀ := by
        simp only [countEchoRecv]
        congr 1 ; apply List.filter_congr ; intro x _ ; rw [hecho_eq q x b₀]
      rw [← this] ; exact hq
    · -- B5: idempotence via the helper lemma
      exact (computeBound_idempotent n f
        ({ s with local_ := fun p => if p = i
          then { s.local_ i with decided := some mv } else s.local_ p } : State n)).symm
    · -- B6: vote-once preserved (voted unchanged)
      intro p hcp v₁ v₂ hv1 hv2
      rw [hvoted_eq p v₁] at hv1
      rw [hvoted_eq p v₂] at hv2
      exact hB6 p hcp v₁ v₂ hv1 hv2
    · -- B7: corrupted unchanged
      exact hB7
    · -- B8: corrupted/voted unchanged; bound unchanged; inherit
      intro hnb
      rw [hnew_bv] at hnb
      -- correctVoteCount reads only voted (which is unchanged) and corrupted
      -- (unchanged), so the new state's correctVoteCount(none) equals s's.
      have hcvc_any : ∀ (bv : Option (Option Bool)) (v : Val),
          correctVoteCount n
            ({ s with
              local_ := fun p => if p = i then { s.local_ i with decided := some mv }
                else s.local_ p,
              boundValue := bv } : State n) v
          = correctVoteCount n s v := by
        intro _ v
        simp only [correctVoteCount]
        apply congrArg ; apply List.filter_congr ; intro q _
        rw [hvoted_eq q v]
      rw [hcvc_any]
      exact hB8 hnb

/-- **Cross-step binary-bound monotonicity.** Once the bound value is set to
    a binary value `b₀` at some step `k₁`, at every later step `k₂ ≥ k₁` the
    bound value is either still `some (some b₀)` or has been upgraded to
    `some none` — it is never `some (some (!b₀))`.

    Proved by induction on `k₂ - k₁`, using the next-step relation from the
    safety assumption and `computeBound_preserves_binary` at each step. -/
theorem bound_binary_monotone (input : Fin n → Bool)
    (e : exec (State n)) (hsafety : e |=tla= (bca n f input).safety)
    (b₀ : Bool) (k₁ k₂ : Nat) (hk : k₁ ≤ k₂)
    (h₁ : (e k₁).boundValue = some (some b₀)) :
    (e k₂).boundValue = some (some b₀) ∨ (e k₂).boundValue = some none := by
  obtain ⟨_, hnext⟩ := hsafety
  have step : ∀ k, (e k).boundValue = some (some b₀) ∨ (e k).boundValue = some none →
      (e (k+1)).boundValue = some (some b₀) ∨ (e (k+1)).boundValue = some none := by
    intro k hk_bv
    have hstep : (bca n f input).toSpec.next (e k) (e (k + 1)) := by
      have := hnext k
      simp [action_pred, exec.drop] at this
      rwa [Nat.add_comm] at this
    obtain ⟨action, _, htrans⟩ := hstep
    -- Show `(e(k+1)).boundValue = computeBound n f s₀` for some `s₀` whose own
    -- `boundValue` agrees with `(e k).boundValue`, then apply preservation lemmas.
    suffices h : ∃ s₀ : State n, s₀.boundValue = (e k).boundValue ∧
        (e (k + 1)).boundValue = computeBound n f s₀ by
      obtain ⟨s₀, hs₀, hs'⟩ := h
      rcases hk_bv with hk_bv | hk_bv
      · rw [hs'] ; exact computeBound_preserves_binary n f s₀ b₀ (hs₀.trans hk_bv)
      · right ; rw [hs']
        exact computeBound_preserves_bot n f s₀ (hs₀.trans hk_bv)
    cases action with
    | corrupt i =>
      simp [bca] at htrans
      rw [htrans] ; refine ⟨_, ?_, rfl⟩ ; rfl
    | send src dst t mv =>
      simp [bca] at htrans
      rw [htrans] ; refine ⟨_, ?_, rfl⟩ ; rfl
    | recv src dst t mv =>
      simp [bca] at htrans
      rw [htrans] ; refine ⟨_, ?_, rfl⟩ ; rfl
    | decide i mv =>
      simp [bca] at htrans
      rw [htrans] ; refine ⟨_, ?_, rfl⟩ ; rfl
  induction hk with
  | refl => exact Or.inl h₁
  | step _ ih => exact step _ ih

/-- Binding: once any correct process has decided, there is a fixed `b`
    such that no correct process ever decides `some b`.

    Proof sketch: using `bound_inv`, we classically case-split on whether any
    reachable state has `boundValue = some (some b)` for some binary `b`.
    - If yes, pick the opposite value `!b`. By B1, every correct binary decision
      matches the bound; by the (monotone) cross-step consistency of the binary
      bound value (currently assumed), the bound's binary value is unique across
      the trace, ruling out decisions for `!b`.
    - If no, pick anything; B1 forces every correct binary decision to satisfy
      `bound = some none`, and then B2 immediately yields a contradiction. -/
theorem bca_binding (input : Fin n → Bool) (hn : n > 3 * f) :
    pred_implies (bca n f input).safety (binding n) := by
  intro e hsafety
  -- Combined invariant: bca_inv ∧ bound_inv; both are inductive.
  have hinv := init_invariant
    (fun s hi => (⟨bca_inv_init n f input s hi, bound_inv_init n f s input hi⟩ :
      bca_inv n f input s ∧ bound_inv n f s))
    (fun s s' hnext ⟨hbca, hbv⟩ =>
      (⟨bca_inv_step n f input hn s s' hnext hbca,
        bound_inv_step n f hn input s s' hnext hbca hbv⟩ :
        bca_inv n f input s' ∧ bound_inv n f s'))
    e hsafety
  have hinv' : ∀ k, bca_inv n f input (e k) ∧ bound_inv n f (e k) := fun k => by
    have h : bca_inv n f input (exec.drop k e 0) ∧ bound_inv n f (exec.drop k e 0) := hinv k
    simp only [exec.drop, Nat.zero_add] at h
    exact h
  intro hexists
  by_cases hbin : ∃ k b, (e k).boundValue = some (some b)
  · obtain ⟨k₁, b₁, hbv₁⟩ := hbin
    refine ⟨!b₁, fun k q hq hdec_eq => ?_⟩
    rcases (hinv' k).2.1 q (!b₁) hq hdec_eq with hb_k | hb_k
    · -- `(e k).boundValue = some (some (!b₁))` and `(e k₁).boundValue = some (some b₁)`.
      -- By `bound_binary_monotone`, comparing k and k₁, derive a contradiction.
      rcases Nat.le_total k₁ k with hle | hle
      · rcases bound_binary_monotone n f input e hsafety b₁ k₁ k hle hbv₁ with h | h
        · rw [h] at hb_k ; injection hb_k with h2 ; injection h2 with h3
          exact absurd h3 (by cases b₁ <;> decide)
        · rw [h] at hb_k ; exact absurd hb_k (by simp)
      · rcases bound_binary_monotone n f input e hsafety (!b₁) k k₁ hle hb_k with h | h
        · rw [h] at hbv₁ ; injection hbv₁ with h2 ; injection h2 with h3
          exact absurd h3 (by cases b₁ <;> decide)
        · rw [h] at hbv₁ ; exact absurd hbv₁ (by simp)
    · exact (hinv' k).2.2.1 hb_k q (!b₁) hq hdec_eq
  · refine ⟨false, fun k q hq hdec_eq => ?_⟩
    rcases (hinv' k).2.1 q false hq hdec_eq with hb_k | hb_k
    · exact hbin ⟨k, false, hb_k⟩
    · exact (hinv' k).2.2.1 hb_k q false hq hdec_eq

end BindingCrusaderAgreement
