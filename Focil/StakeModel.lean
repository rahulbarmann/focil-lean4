/-
  Focil/StakeModel.lean

  PoS-derived `ForkChoice` instantiation.

  This module discharges the two propositional obligations of
  `Focil.ForkChoice` (`quorum_has_honest_voter` and
  `honest_attester_compliance`) from a more primitive ">2/3
  honest validators" assumption: the same assumption that
  underlies every other Ethereum PoS safety result.

  The headline theorem `Focil.focil_one_of_n_protection` was
  previously conditional on a consumer asserting both
  `ForkChoice` obligations. With this layer, both obligations
  are *derived* from:

  1. A `StakeModel` carrying a per-validator honesty predicate
     and a strict-supermajority honesty assumption.
  2. An `AttesterRun` over that model, carrying the per-validator
     vote relation and a single per-attester compliance rule
     ("honest validators only vote for FOCIL-compliant blocks").

  The constructive function `AttesterRun.toForkChoice` packages
  these into a `ForkChoice` value, discharging both structural
  obligations. The headline safety theorem then applies to any
  `(StakeModel, AttesterRun)` pair without further postulates.

  ## Counting argument

  The load-bearing step is a pigeonhole lemma:
  `filter_count_overlap` says that if two Bool predicates each
  select a strict majority of a finite list (i.e., their
  filtered counts sum to strictly more than the list length),
  some element of the list satisfies both. We apply this with
  the validator list, the honesty predicate, and the vote
  predicate: each is >2/3, so they sum to >4/3 > 1, hence the
  intersection is non-empty.

  ## Bool versus Prop

  `StakeModel.honest` and `AttesterRun.voted` are `Bool`-valued
  rather than `Prop`-valued. This is so the counting argument
  can use `List.filter` directly without threading
  `DecidablePred` instances. The lift to the `Prop`-valued
  fields of `ForkChoice` is via `_ = true`.

  ## Axiom dependencies

  This module's `AttesterRun.toForkChoice` uses standard Lean
  arithmetic automation (`omega`) and `simp` lemmas about
  `List.filter` and `List.length`. These tactics rely on
  `propext` and `Quot.sound`, two foundational kernel axioms
  that ship with every Lean installation and are accepted
  without controversy across the Lean community. They do *not*
  give classical logic (no excluded middle, no choice).

  The headline safety theorems in `Focil.Safety`
  (`focil_one_of_n_protection`,
  `focil_censorship_resistance`,
  `censoring_block_not_canonical`) remain provably free of
  *all* kernel axioms, because their proofs are pure
  case analysis on inductive eliminators and do not reach this
  module. End-to-end PoS-derived safety theorems that compose
  these with `toForkChoice` inherit `propext` and `Quot.sound`
  from the counting argument; this is disclosed honestly in
  README.md and FINDINGS.md.

  This file uses only the Lean 4 core library: no Mathlib
  dependency.
-/

import Focil.Types
import Focil.Protocol
import Focil.ForkChoice
import Focil.Safety

namespace Focil

-- =========================================================================
-- Counting lemma: pigeonhole over `List.filter`
-- =========================================================================

/--
  Pigeonhole over Bool-filtered list counts.

  If two Bool predicates each select more elements of `L` than
  `L` has total elements minus the other predicate's selection
  (equivalently, their filtered counts sum to strictly more than
  `L.length`), then some element of `L` satisfies both
  predicates.

  This is the load-bearing step for deriving
  `quorum_has_honest_voter` from honest-supermajority plus
  voting-supermajority.

  Proof: induction on `L`, case-split on `(P hd, Q hd)`.
-/
private theorem filter_count_overlap
    {α : Type} (L : List α) (P Q : α → Bool)
    (h : L.length < (L.filter P).length + (L.filter Q).length) :
    ∃ x, x ∈ L ∧ P x = true ∧ Q x = true := by
  induction L with
  | nil =>
    -- 0 < 0 + 0 is false; the hypothesis is unsatisfiable.
    simp at h
  | cons hd tl ih =>
    -- Decide the head's membership in each filter.
    cases hP : P hd
    · -- P hd = false
      cases hQ : Q hd
      · -- P hd = false, Q hd = false: both filters skip hd.
        rw [List.filter_cons, hP, List.filter_cons, hQ,
            List.length_cons] at h
        simp at h
        obtain ⟨x, hx, hxP, hxQ⟩ := ih (by omega)
        exact ⟨x, List.mem_cons_of_mem _ hx, hxP, hxQ⟩
      · -- P hd = false, Q hd = true: only Q's filter keeps hd.
        rw [List.filter_cons, hP, List.filter_cons, hQ,
            List.length_cons] at h
        simp at h
        obtain ⟨x, hx, hxP, hxQ⟩ := ih (by omega)
        exact ⟨x, List.mem_cons_of_mem _ hx, hxP, hxQ⟩
    · -- P hd = true
      cases hQ : Q hd
      · -- P hd = true, Q hd = false: only P's filter keeps hd.
        rw [List.filter_cons, hP, List.filter_cons, hQ,
            List.length_cons] at h
        simp at h
        obtain ⟨x, hx, hxP, hxQ⟩ := ih (by omega)
        exact ⟨x, List.mem_cons_of_mem _ hx, hxP, hxQ⟩
      · -- P hd = true, Q hd = true: hd itself is the witness.
        exact ⟨hd, List.mem_cons_self, hP, hQ⟩

-- =========================================================================
-- StakeModel
-- =========================================================================

/--
  A model of the underlying PoS validator set with a
  honest-supermajority assumption.

  Fields:

  - `numValidators`: total number of validators. Validators are
    identified by their index in `List.range numValidators`.
  - `honest`: per-validator honesty (`Bool`-valued for
    decidability of counting).
  - `honest_majority`: strictly more than 2/3 of validators are
    honest, i.e., `3 * |honest| > 2 * numValidators`.

  This is the abstraction layer at which Ethereum's standard
  PoS safety assumption is stated. We make no claims about
  stake weighting in this version: each validator is treated
  as one stake unit. A weighted variant would replace
  `(filter ...).length` with `(filter ...).map weight |>.sum`
  and adjust the supermajority condition accordingly.
-/
structure StakeModel where
  /-- Total number of validators. -/
  numValidators : Nat
  /-- Per-validator honesty (Bool for decidability of counts). -/
  honest        : ValidatorIndex → Bool
  /--
    More than two-thirds of validators are honest:
    `3 * |honest| > 2 * numValidators`.
  -/
  honest_majority :
    3 * (((List.range numValidators).filter honest).length) >
      2 * numValidators

-- =========================================================================
-- AttesterRun: per-attestation context relative to a StakeModel
-- =========================================================================

/--
  A single attestation run relative to a `StakeModel`: the
  context an honest attester observes when they decide whether
  to vote for a block.

  Fields:

  - `state`: the fork-choice store snapshot.
  - `full`: the block-fullness model.
  - `voted`: per-validator/block vote relation (Bool).
  - `honest_rule`: the protocol-level invariant that an honest
    validator who voted for `b` saw `b` as FOCIL-compliant
    against `state` under `full`. This is the per-attester rule
    EIP-7805 specifies.

  Note: `honest_rule` is the *only* substantive assumption an
  `AttesterRun` adds on top of its `StakeModel`. The structural
  `quorum_has_honest_voter` obligation of `ForkChoice` is
  *not* a field here; it is derived from `s.honest_majority`
  plus a quorum hypothesis on `voted`, in
  `AttesterRun.toForkChoice` below.
-/
structure AttesterRun (s : StakeModel) where
  /-- The fork-choice store at attestation time. -/
  state : FocilState
  /-- The block-fullness model in force. -/
  full  : Block → Prop
  /-- Per-validator/block vote relation (Bool). -/
  voted : ValidatorIndex → Block → Bool
  /--
    Honest-attester compliance: validators flagged honest in
    the underlying `StakeModel` only vote for blocks that are
    FOCIL-compliant against `state` under `full`. This is the
    only substantive assumption beyond honest-supermajority.
  -/
  honest_rule :
    ∀ (v : ValidatorIndex) (b : Block),
      s.honest v = true →
      voted v b = true →
      FocilCompliant full b state

/--
  Quorum predicate: more than two-thirds of validators voted
  for `b` in this attestation run. Stated arithmetically as
  `3 * |voters| > 2 * numValidators`.
-/
def AttesterRun.hasQuorum {s : StakeModel} (r : AttesterRun s)
    (b : Block) : Prop :=
  3 * (((List.range s.numValidators).filter
        (fun v => r.voted v b)).length) >
    2 * s.numValidators

-- =========================================================================
-- The constructive lift: AttesterRun → ForkChoice
-- =========================================================================

/--
  **PoS-derived `ForkChoice` instance.**

  Given a stake model with `>2/3` honest validators and an
  attester run satisfying the per-attester compliance rule,
  this function constructs a `ForkChoice` value whose two
  structural obligations (`quorum_has_honest_voter` and
  `honest_attester_compliance`) are *proven*, not postulated.

  The `quorum_has_honest_voter` proof is the load-bearing
  step. It combines `StakeModel.honest_majority` with the
  attester run's quorum hypothesis (`hasQuorum b`) via the
  pigeonhole lemma `filter_count_overlap`: each fraction
  exceeds 2/3, their sum exceeds 4/3, the intersection is
  non-empty, and the witness is an honest validator who voted
  for `b`.

  The `honest_attester_compliance` proof is direct: the
  field `honest_rule` of `AttesterRun` is the same statement
  the `ForkChoice` field requires, modulo the
  `Bool`-to-`Prop` lift.

  Once this lift exists, the headline safety theorem
  `focil_one_of_n_protection` applies to any
  `(StakeModel, AttesterRun)` pair *without further
  postulates*. The only remaining axioms-of-faith are
  Ethereum's standard ">2/3 honest" assumption and the
  faithfulness of `CanAppend`.
-/
def AttesterRun.toForkChoice {s : StakeModel} (r : AttesterRun s) :
    ForkChoice where
  state     := r.state
  full      := r.full
  IsHonest  := fun v => s.honest v = true
  HasQuorum := fun b => r.hasQuorum b
  Voted     := fun v b => r.voted v b = true
  quorum_has_honest_voter := by
    intro b hQuorum
    -- We have:
    --   s.honest_majority : 3 * |honest| > 2 * N
    --   hQuorum            : 3 * |voters| > 2 * N
    -- Adding: 3 * (|honest| + |voters|) > 4 * N.
    -- So |honest| + |voters| > N (for any N ≥ 0; omega handles
    -- the integer arithmetic). Apply filter_count_overlap on
    -- `List.range N` with predicates `s.honest` and
    -- `(fun v => r.voted v b)` to extract a witness.
    have hLen :
        (List.range s.numValidators).length <
        ((List.range s.numValidators).filter s.honest).length +
        ((List.range s.numValidators).filter
          (fun v => r.voted v b)).length := by
      have hH := s.honest_majority
      have hV : 3 * (((List.range s.numValidators).filter
                     (fun v => r.voted v b)).length) >
                2 * s.numValidators := hQuorum
      simp [List.length_range]
      omega
    obtain ⟨v, _hMem, hHonestV, hVotedV⟩ :=
      filter_count_overlap _ _ _ hLen
    exact ⟨v, hHonestV, hVotedV⟩
  honest_attester_compliance := by
    -- Direct from `r.honest_rule`, which is exactly this
    -- statement once the Bool/Prop lift is unfolded.
    intro b v hHonest hVoted
    exact r.honest_rule v b hHonest hVoted

-- =========================================================================
-- End-to-end PoS-derived safety theorem
-- =========================================================================

/--
  **End-to-end PoS-derived FOCIL censorship resistance.**

  This is the marquee result of the project. It composes
  `AttesterRun.toForkChoice` with the headline theorem
  `focil_one_of_n_protection` to give the chain:

      >2/3 honest validators
        ∧ honest validators only vote for compliant blocks
        ∧ ≥2/3 voted for `b`
        ∧ some non-equivocating IL listed `tx`
        ∧ `tx` is appendable to `b` and `b` is not full
      ⟹ `tx ∈ b.transactions`.

  No `ForkChoice` postulates remain. The only axioms-of-faith
  are Ethereum's standard ">2/3 honest" assumption (encoded as
  `s.honest_majority`), the spec's "honest attesters refuse
  non-compliant blocks" rule (encoded as `r.honest_rule`), and
  the faithfulness of the abstract `CanAppend` predicate.

  Axiom dependencies: this theorem depends on `propext` and
  `Quot.sound` (transitively, via the counting argument's use
  of `omega` and `simp`). Both are standard kernel axioms;
  `Classical.choice` is *not* used. The headline theorem
  `focil_one_of_n_protection` itself remains zero-axiom.
-/
theorem focil_pos_derived_safety
    {s : StakeModel} (r : AttesterRun s)
    (b : Block) (tx : Transaction)
    (h_listed_by_some_honest_member :
      ∃ il, il ∈ r.state.stored_ils
            ∧ IsConsidered r.state il
            ∧ tx ∈ il.transactions)
    (h_can_append    : CanAppend tx b)
    (h_block_not_full: ¬ r.full b)
    (h_canonical     : IsCanonical r.toForkChoice b) :
    tx ∈ b.transactions :=
  focil_one_of_n_protection
    r.toForkChoice b tx
    h_listed_by_some_honest_member
    h_can_append h_block_not_full h_canonical

end Focil
