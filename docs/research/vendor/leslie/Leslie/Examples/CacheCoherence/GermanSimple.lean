import Leslie.SymShared

open TLA SymShared

/-! ## German's Cache Coherence Protocol

    This file models a parameterized version of **German's directory-based
    cache coherence protocol** for a single cache line shared by `n` clients.
    The model follows the classic Murphi-style presentation: a distinguished
    home node receives requests, sends invalidations when needed, counts
    invalidation acknowledgements, and finally grants shared or exclusive
    access to the requester.

    ### Protocol overview

    The protocol tracks one cache line only. This is standard for cache
    coherence safety proofs, since coherence constraints are per-line.

    Each client cache is in one of three states:

    - `I`: invalid
    - `S`: shared
    - `E`: exclusive

    The home node stores:

    - the memory value for the line
    - an optional pending requester
    - whether the pending request is shared or exclusive
    - the number of invalidation acknowledgements still awaited

    Each client stores:

    - its cache state and cached value
    - `chan1`: request channel to the home (`reqS` / `reqE`)
    - `chan2`: response / invalidation channel from the home
    - `chan3`: invalidation acknowledgement back to the home

    The model is encoded as a `SymSharedSpec`, so the acting process is always
    a client index `i : Fin n`, while the transition may update both shared
    state and every client's local state.

    ### Key specification choices

    The transition system `german` models the following actions:

    - client-side request actions: `reqShared`, `reqExclusive`
    - client-side local reactions: `recvInv`, `recvGrantShared`,
      `recvGrantExclusive`
    - local store by an exclusive holder: `store v`
    - home-side control actions: `homeProcessReqShared`,
      `homeProcessReqExclusive`, `homeProcessInvAck`

    Home-side request processing has two cases:

    - if no conflicting holder exists, the home enqueues a grant immediately
    - otherwise it records a pending request and sends invalidations

    The invalidation-ack step decrements the pending counter, and when the
    last acknowledgement arrives, the home sends the deferred grant.

    Two grant-consumption guards are important for the safety proof:

    - `recvGrantShared` requires that no other cache is in `E`
    - `recvGrantExclusive` requires that all other caches are in `I`

    These are the point where the protocol's control-state assumptions are
    connected to the cache-state safety property being proved.

    ### Safety properties

    The file proves three related safety properties.

    1. **SWMR (single-writer / multiple-reader)**:

    - if some client is in `E`, every other client is in `I`
    - if some client is in `S`, no other client is in `E`

       This is encoded as `swmr`.

    2. **Clean-copy data invariant**:

    - if a client is in `E`, its cached value equals memory
    - if a client is in `S`, its cached value equals memory

       This is encoded as `data_inv`.

    3. **Coherence of visible copies**:

    - any two non-Invalid caches agree on the line value

       This is encoded as `coherence` and is derived from `data_inv`.

    The combined inductive invariant used in the proofs is `inv = swmr ∧ data_inv`.

    ### Informal proof outline

    The key invariant theorem is `german_inv_invariant`, which proves
    `□ (swmr ∧ data_inv)` by direct induction using `init_invariant`.

    1. **Initial state**:
       every cache starts in `I` with value `0`, and memory also starts at `0`.
       So both `swmr` and `data_inv` hold trivially.

    2. **Inductive step**:
       show every protocol action preserves both `swmr` and `data_inv`.

       Most actions do not change any cache state at all; they only update
       channels, the memory value, or the home's pending-request metadata.
       Those cases are discharged by small lemmas showing the post-state cache
       and value projections are equal to the pre-state projections.

       The interesting cases are the three actions that really change cache
       states:

       - `recvInv`: the acting client moves to `I`, which cannot create a new
         exclusivity violation.
       - `recvGrantShared`: the acting client moves from `I` to `S`; the step
         guard ensures that no other client is currently `E`.
       - `recvGrantExclusive`: the acting client moves from `I` to `E`; the
         step guard ensures that every other client is already `I`.

       In each of these cases, the proof performs a small case split on whether
       the clients mentioned in the invariant are the acting client or not.

       The `store` action is the interesting data case: the exclusive holder
       updates both its local value and memory to the new value. The proof uses
       `swmr` to show that no other client can simultaneously be in `S` or `E`,
       so `data_inv` is preserved.

    3. **Derived coherence**:
       once `data_inv` is proved, coherence follows immediately because every
       non-Invalid cache value is equal to memory, and hence equal to every
       other non-Invalid cache value.
-/

namespace German

abbrev Val := Nat

inductive CacheState where
  | I
  | S
  | E
  deriving DecidableEq, Repr, BEq

inductive Msg where
  | empty
  | reqS
  | reqE
  | inv
  | gntS
  | gntE
  | invAck
  deriving DecidableEq, Repr, BEq

inductive PendingKind where
  | shared
  | exclusive
  deriving DecidableEq, Repr, BEq

structure HomeState where
  mem : Val
  pendingRequester : Option Nat
  pendingKind : Option PendingKind
  pendingAcks : Nat
  deriving DecidableEq, Repr

structure ProcState where
  cache : CacheState
  val : Val
  chan1 : Msg
  chan2 : Msg
  chan3 : Msg
  deriving DecidableEq, Repr

inductive GermanAct where
  | reqShared
  | reqExclusive
  | store (v : Val)
  | recvInv
  | recvGrantShared
  | recvGrantExclusive
  | homeProcessReqShared
  | homeProcessReqExclusive
  | homeProcessInvAck
  deriving DecidableEq

def setLocal {α : Type} {n : Nat} (locals : Fin n → α) (i : Fin n) (x : α) :
    Fin n → α :=
  fun k => if k = i then x else locals k

def countIfFin (n : Nat) (P : Fin n → Bool) : Nat :=
  (List.range n).foldl
    (fun acc m =>
      if h : m < n then
        if P ⟨m, h⟩ then acc + 1 else acc
      else
        acc)
    0

def exclusiveHolderCount (n : Nat) (i : Fin n)
    (s : SymState HomeState ProcState n) : Nat :=
  countIfFin n (fun k => decide (k ≠ i) && (s.locals k).cache == .E)

def nonInvalidHolderCount (n : Nat) (i : Fin n)
    (s : SymState HomeState ProcState n) : Nat :=
  countIfFin n (fun k => decide (k ≠ i) && !((s.locals k).cache == .I))

def requesterGrantLocals {n : Nat} (s : SymState HomeState ProcState n)
    (i : Fin n) (msg : Msg) : Fin n → ProcState :=
  fun k =>
    if k = i then
      { (s.locals k) with chan1 := .empty, chan2 := msg }
    else
      s.locals k

def invalidateExclusiveLocals {n : Nat} (s : SymState HomeState ProcState n)
    (i : Fin n) : Fin n → ProcState :=
  fun k =>
    if k = i then
      { (s.locals k) with chan1 := .empty }
    else if (s.locals k).cache = .E then
      { (s.locals k) with chan2 := .inv }
    else
      s.locals k

def invalidateSharersLocals {n : Nat} (s : SymState HomeState ProcState n)
    (i : Fin n) : Fin n → ProcState :=
  fun k =>
    if k = i then
      { (s.locals k) with chan1 := .empty }
    else if (s.locals k).cache = .I then
      s.locals k
    else
      { (s.locals k) with chan2 := .inv }

def grantPendingLocals {n : Nat} (s : SymState HomeState ProcState n)
    (requester : Nat) (msg : Msg) : Fin n → ProcState :=
  fun k =>
    if k.1 = requester then
      { (s.locals k) with chan2 := msg }
    else
      s.locals k

def german : SymSharedSpec where
  Shared := HomeState
  Local := ProcState
  ActType := GermanAct
  init_shared := fun sh =>
    sh.mem = 0 ∧
    sh.pendingRequester = none ∧
    sh.pendingKind = none ∧
    sh.pendingAcks = 0
  init_local := fun l =>
    l.cache = .I ∧
    l.val = 0 ∧
    l.chan1 = .empty ∧
    l.chan2 = .empty ∧
    l.chan3 = .empty
  step := fun n i a s s' =>
    match a with
    | .reqShared =>
        (s.locals i).cache = .I ∧
        (s.locals i).chan1 = .empty ∧
        (s.locals i).chan2 = .empty ∧
        s' = { shared := s.shared
             , locals := setLocal s.locals i { (s.locals i) with chan1 := .reqS } }
    | .reqExclusive =>
        (s.locals i).cache = .I ∧
        (s.locals i).chan1 = .empty ∧
        (s.locals i).chan2 = .empty ∧
        s' = { shared := s.shared
             , locals := setLocal s.locals i { (s.locals i) with chan1 := .reqE } }
    | .store v =>
        (s.locals i).cache = .E ∧
        s' = { shared := { s.shared with mem := v }
             , locals := setLocal s.locals i { (s.locals i) with val := v } }
    | .recvInv =>
        (s.locals i).chan2 = .inv ∧
        ((s.locals i).cache = .S ∨ (s.locals i).cache = .E) ∧
        s' = { shared := s.shared
             , locals := setLocal s.locals i
                 { (s.locals i) with cache := .I, chan2 := .empty, chan3 := .invAck } }
    | .recvGrantShared =>
        (s.locals i).cache = .I ∧
        (s.locals i).chan2 = .gntS ∧
        (∀ j : Fin n, j ≠ i → (s.locals j).cache ≠ .E) ∧
        s' = { shared := s.shared
             , locals := setLocal s.locals i
                 { (s.locals i) with cache := .S, val := s.shared.mem, chan2 := .empty } }
    | .recvGrantExclusive =>
        (s.locals i).cache = .I ∧
        (s.locals i).chan2 = .gntE ∧
        (∀ j : Fin n, j ≠ i → (s.locals j).cache = .I) ∧
        s' = { shared := s.shared
             , locals := setLocal s.locals i
                 { (s.locals i) with cache := .E, val := s.shared.mem, chan2 := .empty } }
    | .homeProcessReqShared =>
        (s.locals i).chan1 = .reqS ∧
        s.shared.pendingRequester = none ∧
        (((exclusiveHolderCount n i s = 0) ∧
          s' = { shared := s.shared
               , locals := requesterGrantLocals s i .gntS }) ∨
         ((exclusiveHolderCount n i s > 0) ∧
          s' = { shared := { s.shared with
                    pendingRequester := some i.1
                    pendingKind := some .shared
                    pendingAcks := exclusiveHolderCount n i s }
               , locals := invalidateExclusiveLocals s i }))
    | .homeProcessReqExclusive =>
        (s.locals i).chan1 = .reqE ∧
        s.shared.pendingRequester = none ∧
        (((nonInvalidHolderCount n i s = 0) ∧
          s' = { shared := s.shared
               , locals := requesterGrantLocals s i .gntE }) ∨
         ((nonInvalidHolderCount n i s > 0) ∧
          s' = { shared := { s.shared with
                    pendingRequester := some i.1
                    pendingKind := some .exclusive
                    pendingAcks := nonInvalidHolderCount n i s }
               , locals := invalidateSharersLocals s i }))
    | .homeProcessInvAck =>
        (s.locals i).chan3 = .invAck ∧
        ∃ requester kind,
          s.shared.pendingRequester = some requester ∧
          s.shared.pendingKind = some kind ∧
          0 < s.shared.pendingAcks ∧
          (((s.shared.pendingAcks = 1) ∧
            s' = { shared := { s.shared with
                      pendingRequester := none
                      pendingKind := none
                      pendingAcks := 0 }
                 , locals := grantPendingLocals
                     { shared := s.shared
                     , locals := setLocal s.locals i { (s.locals i) with chan3 := .empty } }
                     requester
                     (match kind with
                      | .shared => .gntS
                      | .exclusive => .gntE) }) ∨
           ((1 < s.shared.pendingAcks) ∧
            s' = { shared := { s.shared with pendingAcks := s.shared.pendingAcks - 1 }
                 , locals := setLocal s.locals i { (s.locals i) with chan3 := .empty } }))

def swmr (n : Nat) (s : SymState HomeState ProcState n) : Prop :=
  ∀ i j : Fin n, i ≠ j →
    ((s.locals i).cache = .E → (s.locals j).cache = .I) ∧
    ((s.locals i).cache = .S → (s.locals j).cache ≠ .E)

/-- Clean-copy data invariant: every shared or exclusive copy matches memory. -/
def data_inv (n : Nat) (s : SymState HomeState ProcState n) : Prop :=
  ∀ i : Fin n,
    ((s.locals i).cache = .E → (s.locals i).val = s.shared.mem) ∧
    ((s.locals i).cache = .S → (s.locals i).val = s.shared.mem)

def inv (n : Nat) (s : SymState HomeState ProcState n) : Prop :=
  swmr n s ∧ data_inv n s

/-- Coherence of visible copies: any two non-invalid caches agree on the line value. -/
def coherence (n : Nat) (s : SymState HomeState ProcState n) : Prop :=
  ∀ i j : Fin n,
    (s.locals i).cache ≠ .I →
    (s.locals j).cache ≠ .I →
    (s.locals i).val = (s.locals j).val

theorem german_init_swmr (n : Nat) :
    ∀ s : SymState HomeState ProcState n, (german.toSpec n).init s → swmr n s := by
  intro s hinit i j hij
  rcases hinit with ⟨_, hlocals⟩
  have hi := hlocals i
  have hj := hlocals j
  constructor
  · intro hiE
    rcases hj with ⟨hjI, _, _, _, _⟩
    exact hjI
  · intro hiS hjE
    rcases hi with ⟨hiI, _, _, _, _⟩
    rw [hiI] at hiS
    contradiction

theorem german_init_data_inv (n : Nat) :
    ∀ s : SymState HomeState ProcState n, (german.toSpec n).init s → data_inv n s := by
  intro s hinit i
  rcases hinit with ⟨hshared, hlocals⟩
  rcases hlocals i with ⟨hI, hval, _, _, _⟩
  rcases hshared with ⟨hmem, _, _, _⟩
  constructor
  · intro hE
    rw [hI] at hE
    contradiction
  · intro hS
    rw [hI] at hS
    contradiction

private theorem cache_setLocal_same
    {n : Nat} (s : SymState HomeState ProcState n) (i k : Fin n) (l : ProcState)
    (hcache : l.cache = (s.locals i).cache) :
    (setLocal s.locals i l k).cache = (s.locals k).cache := by
  by_cases hk : k = i
  · subst hk
    simp [setLocal, hcache]
  · simp [setLocal, hk]

private theorem cache_requesterGrant_same
    {n : Nat} (s : SymState HomeState ProcState n) (i k : Fin n) (msg : Msg) :
    (requesterGrantLocals s i msg k).cache = (s.locals k).cache := by
  by_cases hk : k = i
  · subst hk
    simp [requesterGrantLocals]
  · simp [requesterGrantLocals, hk]

private theorem cache_invalidateExclusive_same
    {n : Nat} (s : SymState HomeState ProcState n) (i k : Fin n) :
    (invalidateExclusiveLocals s i k).cache = (s.locals k).cache := by
  by_cases hk : k = i
  · subst hk
    simp [invalidateExclusiveLocals]
  · by_cases hE : (s.locals k).cache = .E
    · simp [invalidateExclusiveLocals, hk, hE]
    · simp [invalidateExclusiveLocals, hk, hE]

private theorem cache_invalidateSharers_same
    {n : Nat} (s : SymState HomeState ProcState n) (i k : Fin n) :
    (invalidateSharersLocals s i k).cache = (s.locals k).cache := by
  by_cases hk : k = i
  · subst hk
    simp [invalidateSharersLocals]
  · by_cases hI : (s.locals k).cache = .I
    · simp [invalidateSharersLocals, hk, hI]
    · simp [invalidateSharersLocals, hk, hI]

private theorem cache_grantPending_same
    {n : Nat} (s : SymState HomeState ProcState n) (requester : Nat) (msg : Msg) (k : Fin n) :
    (grantPendingLocals s requester msg k).cache = (s.locals k).cache := by
  by_cases hk : k.1 = requester
  · simp [grantPendingLocals, hk]
  · simp [grantPendingLocals, hk]

private theorem val_setLocal_same
    {n : Nat} (s : SymState HomeState ProcState n) (i k : Fin n) (l : ProcState)
    (hval : l.val = (s.locals i).val) :
    (setLocal s.locals i l k).val = (s.locals k).val := by
  by_cases hk : k = i
  · subst hk
    simp [setLocal, hval]
  · simp [setLocal, hk]

private theorem val_requesterGrant_same
    {n : Nat} (s : SymState HomeState ProcState n) (i k : Fin n) (msg : Msg) :
    (requesterGrantLocals s i msg k).val = (s.locals k).val := by
  by_cases hk : k = i
  · subst hk
    simp [requesterGrantLocals]
  · simp [requesterGrantLocals, hk]

private theorem val_invalidateExclusive_same
    {n : Nat} (s : SymState HomeState ProcState n) (i k : Fin n) :
    (invalidateExclusiveLocals s i k).val = (s.locals k).val := by
  by_cases hk : k = i
  · subst hk
    simp [invalidateExclusiveLocals]
  · by_cases hE : (s.locals k).cache = .E
    · simp [invalidateExclusiveLocals, hk, hE]
    · simp [invalidateExclusiveLocals, hk, hE]

private theorem val_invalidateSharers_same
    {n : Nat} (s : SymState HomeState ProcState n) (i k : Fin n) :
    (invalidateSharersLocals s i k).val = (s.locals k).val := by
  by_cases hk : k = i
  · subst hk
    simp [invalidateSharersLocals]
  · by_cases hI : (s.locals k).cache = .I
    · simp [invalidateSharersLocals, hk, hI]
    · simp [invalidateSharersLocals, hk, hI]

private theorem val_grantPending_same
    {n : Nat} (s : SymState HomeState ProcState n) (requester : Nat) (msg : Msg) (k : Fin n) :
    (grantPendingLocals s requester msg k).val = (s.locals k).val := by
  by_cases hk : k.1 = requester
  · simp [grantPendingLocals, hk]
  · simp [grantPendingLocals, hk]

private theorem swmr_of_cache_eq {n : Nat}
    (s s' : SymState HomeState ProcState n)
    (hcache : ∀ k, (s'.locals k).cache = (s.locals k).cache)
    (hswmr : swmr n s) :
    swmr n s' := by
  intro i j hij
  constructor
  · intro hiE
    have hiE' : (s.locals i).cache = .E := by rw [← hcache i]; exact hiE
    have hjI := (hswmr i j hij).1 hiE'
    rw [hcache j]
    exact hjI
  · intro hiS
    have hiS' : (s.locals i).cache = .S := by rw [← hcache i]; exact hiS
    have hjNotE := (hswmr i j hij).2 hiS'
    rw [hcache j]
    exact hjNotE

private theorem data_inv_of_mem_cache_val_eq {n : Nat}
    (s s' : SymState HomeState ProcState n)
    (hmem : s'.shared.mem = s.shared.mem)
    (hcache : ∀ k, (s'.locals k).cache = (s.locals k).cache)
    (hval : ∀ k, (s'.locals k).val = (s.locals k).val)
    (hdata : data_inv n s) :
    data_inv n s' := by
  intro i
  constructor
  · intro hiE
    have hiE' : (s.locals i).cache = .E := by rw [← hcache i]; exact hiE
    have hiv := (hdata i).1 hiE'
    rw [hval i, hmem]
    exact hiv
  · intro hiS
    have hiS' : (s.locals i).cache = .S := by rw [← hcache i]; exact hiS
    have hiv := (hdata i).2 hiS'
    rw [hval i, hmem]
    exact hiv

private theorem swmr_preserved (n : Nat)
    (s s' : SymState HomeState ProcState n)
    (hswmr : swmr n s)
    (hnext : (german.toSpec n).next s s') :
    swmr n s' := by
  simp only [SymSharedSpec.toSpec, german] at hnext
  rcases hnext with ⟨i, a, hstep⟩
  match a with
  | .reqShared =>
      rcases hstep with ⟨_, _, _, rfl⟩
      apply swmr_of_cache_eq s
      · intro k
        exact cache_setLocal_same s i k _ rfl
      · exact hswmr
  | .reqExclusive =>
      rcases hstep with ⟨_, _, _, rfl⟩
      apply swmr_of_cache_eq s
      · intro k
        exact cache_setLocal_same s i k _ rfl
      · exact hswmr
  | .store _ =>
      rcases hstep with ⟨_, rfl⟩
      apply swmr_of_cache_eq s
      · intro k
        exact cache_setLocal_same s i k _ rfl
      · exact hswmr
  | .recvInv =>
      rcases hstep with ⟨_, _, rfl⟩
      intro p q hpq
      constructor
      · intro hpE
        by_cases hpi : p = i
        · subst hpi
          simp [setLocal] at hpE
        · have hpE' : (s.locals p).cache = .E := by
            simp [setLocal, hpi] at hpE
            exact hpE
          by_cases hqi : q = i
          · subst hqi
            simp [setLocal]
          · have hqI := (hswmr p q hpq).1 hpE'
            simp [setLocal, hqi, hqI]
      · intro hpS
        by_cases hpi : p = i
        · subst hpi
          simp [setLocal] at hpS
        · have hpS' : (s.locals p).cache = .S := by
            simp [setLocal, hpi] at hpS
            exact hpS
          by_cases hqi : q = i
          · subst hqi
            simp [setLocal]
          · have hqNotE := (hswmr p q hpq).2 hpS'
            simp [setLocal, hqi]
            exact hqNotE
  | .recvGrantShared =>
      rcases hstep with ⟨_, _, hnoE, rfl⟩
      intro p q hpq
      constructor
      · intro hpE
        by_cases hpi : p = i
        · subst hpi
          simp [setLocal] at hpE
        · have hpE' : (s.locals p).cache = .E := by
            simp [setLocal, hpi] at hpE
            exact hpE
          exact False.elim (hnoE p hpi hpE')
      · intro hpS
        by_cases hpi : p = i
        · subst hpi
          have hqi : q ≠ p := by
            intro hq
            exact hpq hq.symm
          have hqNotE' : (s.locals q).cache ≠ .E := hnoE q hqi
          simp [setLocal, hqi]
          exact hqNotE'
        · have hpS' : (s.locals p).cache = .S := by
            simp [setLocal, hpi] at hpS
            exact hpS
          by_cases hqi : q = i
          · subst hqi
            simp [setLocal]
          · have hqNotE := (hswmr p q hpq).2 hpS'
            simp [setLocal, hqi]
            exact hqNotE
  | .recvGrantExclusive =>
      rcases hstep with ⟨_, _, hallI, rfl⟩
      intro p q hpq
      constructor
      · intro hpE
        by_cases hpi : p = i
        · subst hpi
          have hqi : q ≠ p := by
            intro hq
            exact hpq hq.symm
          have hqI := hallI q hqi
          simp [setLocal, hqi, hqI]
        · have hpI := hallI p hpi
          have hpE' : (s.locals p).cache = .E := by
            simp [setLocal, hpi] at hpE
            exact hpE
          rw [hpI] at hpE'
          contradiction
      · intro hpS
        by_cases hpi : p = i
        · subst hpi
          simp [setLocal] at hpS
        · have hpI := hallI p hpi
          have hpS' : (s.locals p).cache = .S := by
            simp [setLocal, hpi] at hpS
            exact hpS
          rw [hpI] at hpS'
          contradiction
  | .homeProcessReqShared =>
      rcases hstep with ⟨_, _, hcase⟩
      rcases hcase with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · apply swmr_of_cache_eq s
        · intro k
          exact cache_requesterGrant_same s i k .gntS
        · exact hswmr
      · apply swmr_of_cache_eq s
        · intro k
          exact cache_invalidateExclusive_same s i k
        · exact hswmr
  | .homeProcessReqExclusive =>
      rcases hstep with ⟨_, _, hcase⟩
      rcases hcase with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · apply swmr_of_cache_eq s
        · intro k
          exact cache_requesterGrant_same s i k .gntE
        · exact hswmr
      · apply swmr_of_cache_eq s
        · intro k
          exact cache_invalidateSharers_same s i k
        · exact hswmr
  | .homeProcessInvAck =>
      rcases hstep with ⟨_, requester, kind, _, _, _, hcase⟩
      rcases hcase with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · apply swmr_of_cache_eq s
        · intro k
          cases kind with
          | shared =>
              simpa using
                (cache_grantPending_same
                  { shared := s.shared
                  , locals := setLocal s.locals i { (s.locals i) with chan3 := .empty } }
                  requester
                  .gntS
                  k).trans
                (cache_setLocal_same s i k _ rfl)
          | exclusive =>
              simpa using
                (cache_grantPending_same
                  { shared := s.shared
                  , locals := setLocal s.locals i { (s.locals i) with chan3 := .empty } }
                  requester
                  .gntE
                  k).trans
                (cache_setLocal_same s i k _ rfl)
        · exact hswmr
      · apply swmr_of_cache_eq s
        · intro k
          exact cache_setLocal_same s i k _ rfl
        · exact hswmr

theorem german_swmr_invariant (n : Nat) :
    pred_implies (german.toSpec n).safety [tlafml| □ ⌜ swmr n ⌝] := by
  apply init_invariant
  · intro s hinit
    exact german_init_swmr n s hinit
  · intro s s' hnext hswmr
    exact swmr_preserved n s s' hswmr hnext

private theorem data_inv_preserved (n : Nat)
    (s s' : SymState HomeState ProcState n)
    (hswmr : swmr n s) (hdata : data_inv n s)
    (hnext : (german.toSpec n).next s s') :
    data_inv n s' := by
  simp only [SymSharedSpec.toSpec, german] at hnext
  rcases hnext with ⟨i, a, hstep⟩
  match a with
  | .reqShared =>
      rcases hstep with ⟨_, _, _, rfl⟩
      apply data_inv_of_mem_cache_val_eq s
      · rfl
      · intro k; exact cache_setLocal_same s i k _ rfl
      · intro k; exact val_setLocal_same s i k _ rfl
      · exact hdata
  | .reqExclusive =>
      rcases hstep with ⟨_, _, _, rfl⟩
      apply data_inv_of_mem_cache_val_eq s
      · rfl
      · intro k; exact cache_setLocal_same s i k _ rfl
      · intro k; exact val_setLocal_same s i k _ rfl
      · exact hdata
  | .store v =>
      rcases hstep with ⟨hiE, rfl⟩
      intro p
      constructor
      · intro hpE
        by_cases hpi : p = i
        · subst hpi
          simp [setLocal] at hpE ⊢
        · have hpI := (hswmr i p (Ne.symm hpi)).1 hiE
          have hpE' : (s.locals p).cache = .E := by
            simp [setLocal, hpi] at hpE
            exact hpE
          rw [hpI] at hpE'
          contradiction
      · intro hpS
        by_cases hpi : p = i
        · subst hpi
          simp [setLocal] at hpS
          exfalso
          rw [hiE] at hpS
          contradiction
        · have hpI := (hswmr i p (Ne.symm hpi)).1 hiE
          have hpS' : (s.locals p).cache = .S := by
            simp [setLocal, hpi] at hpS
            exact hpS
          rw [hpI] at hpS'
          contradiction
  | .recvInv =>
      rcases hstep with ⟨_, _, rfl⟩
      intro p
      constructor
      · intro hpE
        by_cases hpi : p = i
        · subst hpi
          simp [setLocal] at hpE
        · have hpE' : (s.locals p).cache = .E := by
            simp [setLocal, hpi] at hpE
            exact hpE
          have hpv := (hdata p).1 hpE'
          simp [setLocal, hpi, hpv]
      · intro hpS
        by_cases hpi : p = i
        · subst hpi
          simp [setLocal] at hpS
        · have hpS' : (s.locals p).cache = .S := by
            simp [setLocal, hpi] at hpS
            exact hpS
          have hpv := (hdata p).2 hpS'
          simp [setLocal, hpi, hpv]
  | .recvGrantShared =>
      rcases hstep with ⟨_, _, _, rfl⟩
      intro p
      constructor
      · intro hpE
        by_cases hpi : p = i
        · subst hpi
          simp [setLocal] at hpE
        · have hpE' : (s.locals p).cache = .E := by
            simp [setLocal, hpi] at hpE
            exact hpE
          have hpv := (hdata p).1 hpE'
          simp [setLocal, hpi, hpv]
      · intro hpS
        by_cases hpi : p = i
        · subst hpi
          simp [setLocal]
        · have hpS' : (s.locals p).cache = .S := by
            simp [setLocal, hpi] at hpS
            exact hpS
          have hpv := (hdata p).2 hpS'
          simp [setLocal, hpi, hpv]
  | .recvGrantExclusive =>
      rcases hstep with ⟨_, _, _, rfl⟩
      intro p
      constructor
      · intro hpE
        by_cases hpi : p = i
        · subst hpi
          simp [setLocal]
        · have hpE' : (s.locals p).cache = .E := by
            simp [setLocal, hpi] at hpE
            exact hpE
          have hpv := (hdata p).1 hpE'
          simp [setLocal, hpi, hpv]
      · intro hpS
        by_cases hpi : p = i
        · subst hpi
          simp [setLocal] at hpS
        · have hpS' : (s.locals p).cache = .S := by
            simp [setLocal, hpi] at hpS
            exact hpS
          have hpv := (hdata p).2 hpS'
          simp [setLocal, hpi, hpv]
  | .homeProcessReqShared =>
      rcases hstep with ⟨_, _, hcase⟩
      rcases hcase with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · apply data_inv_of_mem_cache_val_eq s
        · rfl
        · intro k; exact cache_requesterGrant_same s i k .gntS
        · intro k; exact val_requesterGrant_same s i k .gntS
        · exact hdata
      · apply data_inv_of_mem_cache_val_eq s
        · rfl
        · intro k; exact cache_invalidateExclusive_same s i k
        · intro k; exact val_invalidateExclusive_same s i k
        · exact hdata
  | .homeProcessReqExclusive =>
      rcases hstep with ⟨_, _, hcase⟩
      rcases hcase with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · apply data_inv_of_mem_cache_val_eq s
        · rfl
        · intro k; exact cache_requesterGrant_same s i k .gntE
        · intro k; exact val_requesterGrant_same s i k .gntE
        · exact hdata
      · apply data_inv_of_mem_cache_val_eq s
        · rfl
        · intro k; exact cache_invalidateSharers_same s i k
        · intro k; exact val_invalidateSharers_same s i k
        · exact hdata
  | .homeProcessInvAck =>
      rcases hstep with ⟨_, requester, kind, _, _, _, hcase⟩
      rcases hcase with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · apply data_inv_of_mem_cache_val_eq s
        · rfl
        · intro k
          cases kind with
          | shared =>
              simpa using
                (cache_grantPending_same
                  { shared := s.shared
                  , locals := setLocal s.locals i { (s.locals i) with chan3 := .empty } }
                  requester
                  .gntS
                  k).trans
                (cache_setLocal_same s i k _ rfl)
          | exclusive =>
              simpa using
                (cache_grantPending_same
                  { shared := s.shared
                  , locals := setLocal s.locals i { (s.locals i) with chan3 := .empty } }
                  requester
                  .gntE
                  k).trans
                (cache_setLocal_same s i k _ rfl)
        · intro k
          cases kind with
          | shared =>
              simpa using
                (val_grantPending_same
                  { shared := s.shared
                  , locals := setLocal s.locals i { (s.locals i) with chan3 := .empty } }
                  requester
                  .gntS
                  k).trans
                (val_setLocal_same s i k _ rfl)
          | exclusive =>
              simpa using
                (val_grantPending_same
                  { shared := s.shared
                  , locals := setLocal s.locals i { (s.locals i) with chan3 := .empty } }
                  requester
                  .gntE
                  k).trans
                (val_setLocal_same s i k _ rfl)
        · exact hdata
      · apply data_inv_of_mem_cache_val_eq s
        · rfl
        · intro k; exact cache_setLocal_same s i k _ rfl
        · intro k; exact val_setLocal_same s i k _ rfl
        · exact hdata

theorem german_inv_invariant (n : Nat) :
    pred_implies (german.toSpec n).safety [tlafml| □ ⌜ inv n ⌝] := by
  apply init_invariant
  · intro s hinit
    exact ⟨german_init_swmr n s hinit, german_init_data_inv n s hinit⟩
  · intro s s' hnext hinv
    exact ⟨
      swmr_preserved n s s' hinv.1 hnext,
      data_inv_preserved n s s' hinv.1 hinv.2 hnext
    ⟩

theorem german_data_invariant (n : Nat) :
    pred_implies (german.toSpec n).safety [tlafml| □ ⌜ data_inv n ⌝] := by
  intro e hs k
  exact (german_inv_invariant n e hs k).2

theorem coherence_of_data_inv (n : Nat) :
    ∀ s : SymState HomeState ProcState n, data_inv n s → coherence n s := by
  intro s hdata i j hi hj
  have hi_cases : (s.locals i).cache = .E ∨ (s.locals i).cache = .S := by
    cases hci : (s.locals i).cache <;> simp [hci] at hi ⊢
  have hj_cases : (s.locals j).cache = .E ∨ (s.locals j).cache = .S := by
    cases hcj : (s.locals j).cache <;> simp [hcj] at hj ⊢
  rcases hi_cases with hiE | hiS
  · rcases hj_cases with hjE | hjS
    · rw [(hdata i).1 hiE, (hdata j).1 hjE]
    · rw [(hdata i).1 hiE, (hdata j).2 hjS]
  · rcases hj_cases with hjE | hjS
    · rw [(hdata i).2 hiS, (hdata j).1 hjE]
    · rw [(hdata i).2 hiS, (hdata j).2 hjS]

theorem german_coherence_invariant (n : Nat) :
    pred_implies (german.toSpec n).safety [tlafml| □ ⌜ coherence n ⌝] := by
  intro e hs k
  exact coherence_of_data_inv n (e k) ((german_data_invariant n) e hs k)

/-
  What we prove now is enough for coherence:

  - any clean cached copy matches memory via data_inv
  - any two non-I caches agree via coherence

  We do not prove a linearizability spec. For example, the property “every read returns the latest written value” is a client-visible behavioral property,
  not just a state invariant. To state it properly, the model needs at least one of these:

  - explicit read-completion actions carrying a return value
  - an operation history / trace projection for reads and writes
  - a refinement mapping to an abstract single-register spec, with a chosen linearization point for reads

  Right now the model has request/grant/channel transitions, but no event that says “client i completed a read and observed value v”. So there is nothing to quantify over for “returns”.

  If we want a client-visible property, we can do the following:

  1. Add a simple read-return event to the model and prove every completed read returns mem.
  2. Define an abstract single-register spec and prove German refines it.
  3. State a weaker state property now: “whenever a cache is in S or E, its local value is the latest written value.” This is already essentially what data_inv gives, assuming mem is the latest write.
-/
end German
