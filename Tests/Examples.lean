/-
  Tests/Examples.lean

  Worked examples that exercise the FOCIL data model and the
  safety theorem on small, paper-checkable scenarios.

  Each example below is a Lean `theorem` or `example` whose
  successful kernel check is its test result. If `lake build
  Tests` succeeds, every example here has been independently
  verified by the kernel.

  The file is organised into four groups:

  - **Compliance scenarios** (Scenarios 1–4): exercise
    `IsConsidered`, `FocilCompliant`, and the conditional-
    inclusion exemption directly, with no fork-choice involved.
  - **Vacuous fork-choice** (Scenario 5): `emptyForkChoice`
    type-checks the safety theorem against an instance that
    discharges its soundness obligations vacuously. Useful as a
    minimal sanity check; not a meaningful demonstration of the
    theorem firing.
  - **Non-vacuous fork-choice** (Scenarios 6–8):
    `threeValidatorForkChoice` is a 3-validator instance where
    both soundness obligations are discharged by genuine case
    analysis. Scenarios 6–8 show the main theorem and its
    corollary firing on actual blocks.
  - **Equivocator scenarios** (Scenarios 9–10): demonstrate
    FINDINGS.md §2.4 by example. When an IL author is in the
    equivocator set, the inclusion guarantee for transactions
    listed only by them is intentionally voided.
  - **Headline 1-of-N theorem** (Scenario 11): fires
    `focil_one_of_n_protection` against the 3-validator
    instance, with the witness IL produced existentially.
  - **PoS-derived end-to-end** (Scenario 12): builds a
    `StakeModel` and `AttesterRun` from scratch, derives both
    `ForkChoice` obligations from a >2/3 honest validator
    assumption via `AttesterRun.toForkChoice`, and fires
    `focil_pos_derived_safety` with no postulates remaining.
-/

import FocilLean4

namespace Focil
namespace Examples

-- =========================================================================
-- Toy data shared across scenarios
-- =========================================================================

/-- A toy transaction. -/
def tx1 : Transaction :=
  { id := 1, sender := 100, nonce := 0, gas := 21000 }

/-- Another toy transaction with a different `id`. -/
def tx2 : Transaction :=
  { id := 2, sender := 200, nonce := 0, gas := 21000 }

/-- A single committee member's IL containing only `tx1`. -/
def ilHonest : InclusionList :=
  { slot := 10, validator_index := 7, transactions := [tx1] }

/-- A block that *includes* `tx1`. -/
def blockIncludes : Block :=
  { slot := 11, proposer := 99, transactions := [tx1], gasLimit := 30000000 }

/-- A block that *omits* `tx1` (includes only `tx2` instead). -/
def blockOmits : Block :=
  { slot := 11, proposer := 99, transactions := [tx2], gasLimit := 30000000 }

/-- Store with `ilHonest` available, no equivocators. -/
def stateHonest : FocilState :=
  { current_slot := 11, stored_ils := [ilHonest], equivocators := [] }

/-- A block-fullness model where blocks are never full. -/
def neverFull : Block → Prop := fun _ => False

-- =========================================================================
-- Scenario 1: equivocator filter
-- =========================================================================

/--
  An IL whose author is not in the equivocator set is considered
  by the compliance check.

  Trivial sanity check on `IsConsidered` / `IsHonestlyAttributed`.
-/
example : IsConsidered stateHonest ilHonest := by
  -- `IsConsidered` reduces to `validator_index ∉ equivocators`,
  -- and `equivocators = []` makes membership impossible.
  simp [IsConsidered, IsHonestlyAttributed, stateHonest]

-- =========================================================================
-- Scenario 2: a compliant block
-- =========================================================================

/--
  A block that includes the IL transaction is FOCIL-compliant.

  There is exactly one stored IL (`ilHonest`) containing exactly
  one transaction (`tx1`). Since `tx1 ∈ blockIncludes.transactions`,
  the first disjunct of compliance is satisfied immediately.
-/
example : FocilCompliant neverFull blockIncludes stateHonest := by
  intro il hIl _hConsidered tx hTx
  -- `stored_ils = [ilHonest]`, so `il = ilHonest`.
  simp [stateHonest] at hIl
  subst hIl
  -- `ilHonest.transactions = [tx1]`, so `tx = tx1`.
  simp [ilHonest] at hTx
  subst hTx
  -- The first disjunct `tx1 ∈ blockIncludes.transactions` holds.
  left
  simp [blockIncludes]

-- =========================================================================
-- Scenario 3: non-compliant block omitting a valid tx
-- =========================================================================

/--
  A block that omits a valid, appendable IL transaction is not
  FOCIL-compliant. Direct refutation of compliance.

  This is the precondition for `censoring_block_not_canonical`:
  a builder constructing such a block has their block ruled out
  by the fork choice.
-/
example
    (h_can_append : CanAppend tx1 blockOmits) :
    ¬ FocilCompliant neverFull blockOmits stateHonest := by
  intro hCompl
  -- Apply compliance to (ilHonest, tx1).
  have hConsidered : IsConsidered stateHonest ilHonest := by
    simp [IsConsidered, IsHonestlyAttributed, stateHonest]
  have hIlMem : ilHonest ∈ stateHonest.stored_ils := by
    simp [stateHonest]
  have hTxMem : tx1 ∈ ilHonest.transactions := by
    simp [ilHonest]
  have h := hCompl ilHonest hIlMem hConsidered tx1 hTxMem
  -- Case-split on the disjunction. Each case fails.
  cases h with
  | inl h_in =>
    -- `tx1 ∈ blockOmits.transactions` is false; the only tx
    -- in `blockOmits` is `tx2`, and `tx1.id ≠ tx2.id`.
    simp [blockOmits, tx1, tx2] at h_in
  | inr h_rest =>
    cases h_rest with
    | inl h_not_app =>
      -- `¬ CanAppend tx1 blockOmits` contradicts `h_can_append`.
      exact h_not_app h_can_append
    | inr h_full =>
      -- `neverFull blockOmits` is `False`.
      exact h_full

-- =========================================================================
-- Scenario 4: conditional-inclusion exemption
-- =========================================================================

/--
  If `tx1` has become invalid (`¬ CanAppend tx1 blockOmits`),
  then omitting `tx1` from the block is OK: the block remains
  FOCIL-compliant via the conditional-inclusion exemption.

  Models EIP-7805's "either present, or invalid, or block is full"
  rule on its second branch.
-/
example
    (h_invalid : ¬ CanAppend tx1 blockOmits) :
    FocilCompliant neverFull blockOmits stateHonest := by
  intro il hIl _hConsidered tx hTx
  simp [stateHonest] at hIl
  subst hIl
  simp [ilHonest] at hTx
  subst hTx
  -- Compliance via the second disjunct.
  right
  left
  exact h_invalid

-- =========================================================================
-- Scenario 5: vacuous fork-choice instance (sanity only)
-- =========================================================================

/--
  A vacuous fork-choice instance.

  **Note (see also FINDINGS.md §5):** This instance discharges
  the two soundness obligations of `ForkChoice` *vacuously*:

  - `HasQuorum := fun _ => False`: no block ever has a quorum.
  - `Voted     := fun _ _ => False`: nobody ever votes.

  Both `quorum_has_honest_voter` and `honest_attester_compliance`
  hold because their hypotheses are unsatisfiable. The instance
  is consistent and lets the main theorem type-check against a
  real `ForkChoice` value, but it does *not* model an actual
  attester-voting process. For a meaningful demonstration of the
  theorem firing, see `threeValidatorForkChoice` below.
-/
def emptyForkChoice : ForkChoice where
  state       := stateHonest
  full        := neverFull
  IsHonest    := fun _ => True
  HasQuorum   := fun _ => False
  Voted       := fun _ _ => False
  quorum_has_honest_voter := by
    -- Vacuous: `HasQuorum b = False`, so the antecedent is
    -- unsatisfiable.
    intro _ h
    cases h
  honest_attester_compliance := by
    -- Vacuous: `Voted v b = False`, so the antecedent is
    -- unsatisfiable.
    intro _ _ _ hVoted
    cases hVoted

/--
  The main censorship-resistance theorem instantiates against a
  concrete `ForkChoice` value.

  Because `emptyForkChoice.HasQuorum = (fun _ => False)`, the
  hypothesis `IsCanonical emptyForkChoice b` is unsatisfiable in
  any concrete scenario. The point of this example is structural:
  the theorem accepts a real `ForkChoice` value, not just its
  abstract type. For the theorem firing on a *non-vacuous*
  scenario, see Scenario 7 below.
-/
example
    (b : Block) (il : InclusionList) (tx : Transaction)
    (h_tx_in_il      : tx ∈ il.transactions)
    (h_il_stored     : il ∈ emptyForkChoice.state.stored_ils)
    (h_il_considered : IsConsidered emptyForkChoice.state il)
    (h_can_append    : CanAppend tx b)
    (h_block_not_full: ¬ emptyForkChoice.full b)
    (h_canonical     : IsCanonical emptyForkChoice b) :
    tx ∈ b.transactions :=
  focil_censorship_resistance
    emptyForkChoice b il tx
    h_tx_in_il h_il_stored h_il_considered
    h_can_append h_block_not_full h_canonical

-- =========================================================================
-- A non-vacuous 3-validator scenario
-- =========================================================================

/-
  ## Scenario design

  - Three validators: indices 0, 1, 2.
  - Honest set: {0, 1}.  Validator 2 is Byzantine.
  - One inclusion list `ilHonest` authored by validator 7
    (intentionally a different index, since committee
    membership is abstract; what matters is non-equivocator
    status), containing transaction `tx1`.
  - Two candidate blocks:
      * `blockIncludes` includes `tx1` and is FOCIL-compliant.
      * `blockOmits` omits `tx1` and (under the assumption that
        `tx1` is appendable) is non-compliant.
  - `Voted v b` holds iff `v ∈ {0, 1}` and `b = blockIncludes`.
    The honest validators voted for `blockIncludes` and only
    `blockIncludes`. Validator 2 abstains.
  - `HasQuorum b` holds iff `b = blockIncludes`.

  Under this design:

  - `quorum_has_honest_voter`: for the only block reaching a
    quorum (`blockIncludes`), validator 0 is a witness honest
    voter.
  - `honest_attester_compliance`: the only block honest
    validators ever voted for is `blockIncludes`, and
    `blockIncludes` is FOCIL-compliant against `stateHonest`
    (Scenario 2 already proved this).

  Both obligations are discharged by *real case analysis*, not
  by emptying out their antecedents.
-/

/-- Predicate identifying the honest validators in our scenario. -/
def isHonest3v (v : ValidatorIndex) : Prop :=
  v = 0 ∨ v = 1

/--
  Vote relation: honest validators voted for `blockIncludes` only.
  Validator 2 (Byzantine) and any other index never voted for
  anything.
-/
def voted3v (v : ValidatorIndex) (b : Block) : Prop :=
  isHonest3v v ∧ b = blockIncludes

/--
  Quorum predicate: only `blockIncludes` has reached a quorum.
  In this toy scenario "quorum" is just "blockIncludes was
  attested to by honest validators"; a richer model would tally
  votes against a stake-weighted threshold.
-/
def hasQuorum3v (b : Block) : Prop :=
  b = blockIncludes

/--
  **Non-vacuous fork-choice instance for the 3-validator
  scenario.**

  Both soundness obligations are discharged by genuine reasoning:

  - `quorum_has_honest_voter`: given `b = blockIncludes`, witness
    validator 0 (honest, voted).
  - `honest_attester_compliance`: given `voted3v v b`, decompose
    to learn `b = blockIncludes`, then prove `blockIncludes` is
    FOCIL-compliant against `stateHonest` by direct case analysis
    on `stored_ils.[ilHonest].transactions = [tx1]`.

  This is the instance Scenarios 6–8 fire the main theorem
  against.
-/
def threeValidatorForkChoice : ForkChoice where
  state       := stateHonest
  full        := neverFull
  IsHonest    := isHonest3v
  HasQuorum   := hasQuorum3v
  Voted       := voted3v
  quorum_has_honest_voter := by
    -- Given `hasQuorum3v b`, we get `b = blockIncludes`.
    -- Witness validator 0: it is honest and voted for the block.
    intro b hQ
    -- Unfold `hasQuorum3v` to learn `b = blockIncludes`.
    have hb : b = blockIncludes := hQ
    refine ⟨0, ?_, ?_⟩
    · -- `isHonest3v 0` is `0 = 0 ∨ 0 = 1`, satisfied by the
      -- left disjunct.
      left; rfl
    · -- `voted3v 0 b` requires `isHonest3v 0 ∧ b = blockIncludes`.
      refine ⟨?_, hb⟩
      left; rfl
  honest_attester_compliance := by
    -- Decompose `voted3v v b` to recover `b = blockIncludes`,
    -- then prove `blockIncludes` is FocilCompliant against
    -- `stateHonest`.
    intro b v _hHonest hVoted
    -- `voted3v v b = isHonest3v v ∧ b = blockIncludes`.
    obtain ⟨_hVHon, hb⟩ := hVoted
    -- Substitute `b = blockIncludes`.
    subst hb
    -- Now prove `FocilCompliant neverFull blockIncludes stateHonest`.
    -- The only stored IL is `ilHonest`, and `tx1` (its only
    -- transaction) is in `blockIncludes.transactions`.
    intro il hIl _hCons tx hTx
    -- `stored_ils = [ilHonest]`, so `il = ilHonest`.
    simp [stateHonest] at hIl
    subst hIl
    -- `ilHonest.transactions = [tx1]`, so `tx = tx1`.
    simp [ilHonest] at hTx
    subst hTx
    -- First disjunct: `tx1 ∈ blockIncludes.transactions`.
    left
    simp [blockIncludes]

-- =========================================================================
-- Scenario 6: blockIncludes is canonical under the 3v instance
-- =========================================================================

/--
  Sanity check: `blockIncludes` is canonical under
  `threeValidatorForkChoice`.

  This unfolds `IsCanonical` to `hasQuorum3v blockIncludes`,
  which holds by definition.
-/
example : IsCanonical threeValidatorForkChoice blockIncludes := by
  -- `IsCanonical fc b` is `fc.HasQuorum b`, which here is
  -- `hasQuorum3v blockIncludes = (blockIncludes = blockIncludes)`.
  show hasQuorum3v blockIncludes
  rfl

-- =========================================================================
-- Scenario 7: main theorem firing on a non-vacuous scenario
-- =========================================================================

/--
  **The main theorem firing on a real scenario.**

  Under `threeValidatorForkChoice`, given that `tx1` is in the
  stored honest IL, is appendable, and the canonical block is
  `blockIncludes`, the theorem concludes `tx1 ∈
  blockIncludes.transactions`.

  This is what `emptyForkChoice` could not demonstrate: here the
  fork-choice rule has a real quorum, real honest voters, and a
  real soundness story relating votes to compliance.
-/
example
    (h_can_append : CanAppend tx1 blockIncludes) :
    tx1 ∈ blockIncludes.transactions := by
  -- Build the hypotheses the main theorem expects, all of which
  -- are decidable / reflexive in this concrete instance.
  have h_tx_in_il      : tx1 ∈ ilHonest.transactions := by
    simp [ilHonest]
  have h_il_stored     : ilHonest ∈ threeValidatorForkChoice.state.stored_ils := by
    -- `threeValidatorForkChoice.state = stateHonest`,
    -- whose `stored_ils = [ilHonest]`.
    simp [threeValidatorForkChoice, stateHonest]
  have h_il_considered : IsConsidered threeValidatorForkChoice.state ilHonest := by
    simp [threeValidatorForkChoice, IsConsidered, IsHonestlyAttributed,
          stateHonest]
  have h_block_not_full: ¬ threeValidatorForkChoice.full blockIncludes := by
    -- `full = neverFull = (fun _ => False)`.
    intro h
    exact h
  have h_canonical     : IsCanonical threeValidatorForkChoice blockIncludes := by
    show hasQuorum3v blockIncludes
    rfl
  -- Apply the main theorem.
  exact focil_censorship_resistance
    threeValidatorForkChoice blockIncludes ilHonest tx1
    h_tx_in_il h_il_stored h_il_considered
    h_can_append h_block_not_full h_canonical

-- =========================================================================
-- Scenario 8: censoring block is not canonical (contrapositive)
-- =========================================================================

/--
  **Builder-side incentive, demonstrated.**

  Under `threeValidatorForkChoice`, the censoring block
  `blockOmits` (which excludes `tx1`) cannot be the canonical
  chain head, given that `tx1` is appendable.

  This fires the contrapositive corollary
  `censoring_block_not_canonical` on a real instance. Because
  `threeValidatorForkChoice.HasQuorum` holds only of
  `blockIncludes`, the conclusion `¬ IsCanonical fc blockOmits`
  is in fact provable directly, but the *route* through the
  corollary demonstrates that the safety theorem rules out
  censoring blocks structurally, not just by accidental
  underspecification of the quorum.
-/
example
    (h_can_append : CanAppend tx1 blockOmits) :
    ¬ IsCanonical threeValidatorForkChoice blockOmits := by
  have h_tx_in_il      : tx1 ∈ ilHonest.transactions := by
    simp [ilHonest]
  have h_il_stored     : ilHonest ∈ threeValidatorForkChoice.state.stored_ils := by
    simp [threeValidatorForkChoice, stateHonest]
  have h_il_considered : IsConsidered threeValidatorForkChoice.state ilHonest := by
    simp [threeValidatorForkChoice, IsConsidered, IsHonestlyAttributed,
          stateHonest]
  have h_block_not_full: ¬ threeValidatorForkChoice.full blockOmits := by
    intro h; exact h
  have h_tx_excluded   : tx1 ∉ blockOmits.transactions := by
    -- `blockOmits.transactions = [tx2]`, and `tx1 ≠ tx2`.
    simp [blockOmits, tx1, tx2]
  exact censoring_block_not_canonical
    threeValidatorForkChoice blockOmits ilHonest tx1
    h_tx_in_il h_il_stored h_il_considered
    h_can_append h_block_not_full h_tx_excluded

-- =========================================================================
-- Equivocator scenario: demonstrating Finding §2.4 by example
-- =========================================================================

/-
  ## The equivocator-as-censorship-channel, demonstrated

  FINDINGS.md §2.4 observes that a Byzantine IL committee member
  who controls one seat can void their own contribution by
  publishing two distinct ILs. Once the validator is recorded as
  an equivocator, *all* their ILs are ignored, including
  honestly-listed transactions in their first IL.

  This block of scenarios demonstrates that consequence
  concretely. The setup:

  - The store still has `ilHonest` (authored by validator 7).
  - But validator 7 is in `state.equivocators` (presumably they
    were caught equivocating after publishing `ilHonest`).
  - Therefore `IsConsidered state ilHonest` is *false*.
  - A block omitting `tx1` is now FOCIL-compliant: the
    obligation imposed by `ilHonest` is filtered out.
  - The safety theorem's hypothesis `h_il_considered` fails for
    `ilHonest`, so the theorem makes no claim about `tx1`.

  This is intentional protocol behaviour, not a soundness gap in
  the formalization. The Lean model captures it precisely.
-/

/--
  Same fork-choice store as `stateHonest`, but with validator 7
  marked as an equivocator. Used to demonstrate FINDINGS.md §2.4.
-/
def stateWithEquivocator : FocilState :=
  { current_slot := 11, stored_ils := [ilHonest], equivocators := [7] }

/--
  **Scenario 9: equivocator censorship.**

  When `ilHonest`'s author is in the equivocator set, a block
  that *omits* the IL transaction `tx1` is FOCIL-compliant
  against the store, because the only stored IL is filtered
  out by `IsConsidered`.

  This demonstrates how a single equivocating committee member
  removes the inclusion guarantee for any transaction they alone
  listed. With more than one honest IL listing `tx1`, compliance
  would still hold via the other ILs (the "1-of-N" guarantee
  would degrade to "1-of-(N − equivocators)").
-/
example : FocilCompliant neverFull blockOmits stateWithEquivocator := by
  intro il hIl hConsidered _tx _hTx
  -- Only `ilHonest` is in the store, but it has been filtered
  -- out by the equivocator guard before we reach the per-tx check.
  -- We refute `hConsidered` directly.
  simp [stateWithEquivocator] at hIl
  subst hIl
  -- `IsConsidered stateWithEquivocator ilHonest` reduces to
  -- `ilHonest.validator_index ∉ stateWithEquivocator.equivocators`,
  -- i.e. `7 ∉ [7]`, which is false.
  exact absurd hConsidered (by
    simp [IsConsidered, IsHonestlyAttributed, stateWithEquivocator,
          ilHonest])

/--
  **Scenario 10: the safety theorem is silent under
  equivocation.**

  Under `stateWithEquivocator`, the safety theorem's hypothesis
  `h_il_considered` fails for `ilHonest`, so the theorem cannot
  be applied with `il := ilHonest` to constrain any block.

  We demonstrate this by showing the hypothesis fails: any
  attempt to invoke `focil_censorship_resistance` with this IL
  and state must fail at type-checking, because
  `IsConsidered stateWithEquivocator ilHonest` is false.

  This is the mirror image of Scenario 9: the same protocol
  reality (equivocator removes protection) is visible from both
  the compliance-rule side (Scenario 9) and the safety-theorem
  side (this scenario).
-/
example : ¬ IsConsidered stateWithEquivocator ilHonest := by
  -- `IsConsidered` reduces to `ilHonest.validator_index ∉
  -- equivocators = [7]`. The validator index is 7, so
  -- membership holds and the negation is false.
  simp [IsConsidered, IsHonestlyAttributed, stateWithEquivocator,
        ilHonest]

-- =========================================================================
-- The 1-of-N headline theorem firing on a concrete witness
-- =========================================================================

/--
  **Scenario 11: the headline 1-of-N theorem firing.**

  Whereas Scenario 7 fires the per-IL building block
  (`focil_censorship_resistance`) by passing `ilHonest`
  explicitly, this scenario fires the headline theorem
  `focil_one_of_n_protection`. The witness IL is *existentially*
  produced inside the hypothesis, matching how the theorem
  would be used in practice: the consumer asserts that *some*
  honest committee member listed `tx`, without naming which.

  This is what EIP-7805's marquee 1-of-N claim looks like in
  formal form. Adversaries controlling some committee seats and
  equivocating others do not defeat the guarantee, as long as at
  least one seat publishes a non-equivocating IL containing
  `tx`.
-/
example
    (h_can_append : CanAppend tx1 blockIncludes) :
    tx1 ∈ blockIncludes.transactions := by
  -- Build the existential witness: at least one stored,
  -- non-equivocating IL contains `tx1`.
  have h_witness :
      ∃ il, il ∈ threeValidatorForkChoice.state.stored_ils
            ∧ IsConsidered threeValidatorForkChoice.state il
            ∧ tx1 ∈ il.transactions := by
    refine ⟨ilHonest, ?_, ?_, ?_⟩
    · -- ilHonest ∈ stored_ils
      simp [threeValidatorForkChoice, stateHonest]
    · -- ilHonest is considered (author not in equivocators)
      simp [threeValidatorForkChoice, IsConsidered,
            IsHonestlyAttributed, stateHonest]
    · -- tx1 ∈ ilHonest.transactions
      simp [ilHonest]
  -- Block-not-full and canonical hypotheses, as before.
  have h_block_not_full :
      ¬ threeValidatorForkChoice.full blockIncludes := by
    intro h
    exact h
  have h_canonical :
      IsCanonical threeValidatorForkChoice blockIncludes := by
    show hasQuorum3v blockIncludes
    rfl
  -- Apply the headline theorem.
  exact focil_one_of_n_protection
    threeValidatorForkChoice blockIncludes tx1
    h_witness h_can_append h_block_not_full h_canonical

-- =========================================================================
-- The PoS-derived end-to-end theorem firing on a concrete stake model
-- =========================================================================

/-
  ## Scenario design (Scenario 12)

  Where Scenarios 6–11 use the pre-built
  `threeValidatorForkChoice` and postulate the two `ForkChoice`
  obligations directly, this scenario constructs a `StakeModel`
  and `AttesterRun` from scratch, derives the obligations from
  Ethereum's standard ">2/3 honest validators" assumption, and
  fires the end-to-end safety theorem
  `focil_pos_derived_safety`.

  - 3 validators (indices 0, 1, 2).
  - validators 0 and 1 are honest, validator 2 is Byzantine.
  - 2 of 3 honest is *not* > 2/3 of 3, so we use 4 validators
    instead: indices 0, 1, 2 honest, validator 3 Byzantine.
    3 of 4 > 2/3 * 4 = 8/3, satisfied since 3 * 3 = 9 > 8.
  - All three honest validators voted for `blockIncludes`.
    3 of 4 > 2/3 again, so quorum is achieved by the same
    counting.
-/

/-- Honesty predicate for the 4-validator scenario. -/
def isHonest4v (v : ValidatorIndex) : Bool :=
  v = 0 ∨ v = 1 ∨ v = 2

/-- The 4-validator stake model. -/
def stakeModel4v : StakeModel where
  numValidators   := 4
  honest          := isHonest4v
  honest_majority := by
    -- 3 * |honest| > 2 * 4, i.e., 3 * 3 > 8.
    decide

/-- Vote relation for the 4-validator scenario: the three honest
    validators voted for `blockIncludes`. -/
def voted4v (v : ValidatorIndex) (b : Block) : Bool :=
  isHonest4v v ∧ b = blockIncludes

/--
  The 4-validator attester run.

  `honest_rule` is discharged by the same case analysis used in
  Scenario 5 (`emptyForkChoice`'s richer cousin
  `threeValidatorForkChoice`): the only block honest validators
  voted for is `blockIncludes`, and `blockIncludes` is
  FOCIL-compliant against `stateHonest`.
-/
def attesterRun4v : AttesterRun stakeModel4v where
  state       := stateHonest
  full        := neverFull
  voted       := voted4v
  honest_rule := by
    intro v b _hHonest hVoted
    -- voted4v unfolds to (isHonest4v v ∧ b = blockIncludes),
    -- where conjunction is `Bool.and`. Decompose to learn
    -- b = blockIncludes.
    have hb : b = blockIncludes := by
      simp [voted4v, Bool.and_eq_true] at hVoted
      exact hVoted.2
    subst hb
    -- Compliance of `blockIncludes` against `stateHonest`,
    -- exactly as proven in Scenario 2.
    intro il hIl _hCons tx hTx
    simp [stateHonest] at hIl
    subst hIl
    simp [ilHonest] at hTx
    subst hTx
    left
    simp [blockIncludes]

/--
  **Scenario 12: end-to-end PoS-derived FOCIL safety.**

  This is the marquee result of the project, demonstrated on a
  concrete 4-validator scenario.

  Starting points:
  - `stakeModel4v.honest_majority`: 3 of 4 validators are
    honest, > 2/3 (proven by `decide`).
  - `attesterRun4v.honest_rule`: honest validators only vote
    for FOCIL-compliant blocks.
  - A quorum hypothesis: `blockIncludes` was voted for by all
    three honest validators (3 of 4 > 2/3, proven below).
  - The standard 1-of-N witness: `ilHonest` lists `tx1` and is
    not equivocating.
  - `tx1` is appendable to `blockIncludes` and the block is
    not full.

  Conclusion: `tx1 ∈ blockIncludes.transactions`.

  No `ForkChoice` obligations are postulated. Both are derived
  by `AttesterRun.toForkChoice` from the supermajority and
  honest-rule assumptions above.
-/
example
    (h_can_append : CanAppend tx1 blockIncludes) :
    tx1 ∈ blockIncludes.transactions := by
  have h_witness :
      ∃ il, il ∈ attesterRun4v.state.stored_ils
            ∧ IsConsidered attesterRun4v.state il
            ∧ tx1 ∈ il.transactions := by
    refine ⟨ilHonest, ?_, ?_, ?_⟩
    · simp [attesterRun4v, stateHonest]
    · simp [attesterRun4v, IsConsidered, IsHonestlyAttributed,
            stateHonest]
    · simp [ilHonest]
  have h_block_not_full :
      ¬ attesterRun4v.full blockIncludes := by
    intro h
    exact h
  have h_canonical :
      IsCanonical attesterRun4v.toForkChoice blockIncludes := by
    -- Quorum hypothesis: 3 of 4 voted for blockIncludes.
    -- IsCanonical fc b ≡ fc.HasQuorum b ≡ attesterRun4v.hasQuorum b
    -- which is 3 * |voters| > 2 * 4. With three honest voters
    -- voting for blockIncludes, |voters| = 3, so 9 > 8.
    show attesterRun4v.hasQuorum blockIncludes
    show 3 * (((List.range 4).filter
              (fun v => voted4v v blockIncludes)).length) > 8
    decide
  exact focil_pos_derived_safety
    attesterRun4v blockIncludes tx1
    h_witness h_can_append h_block_not_full h_canonical

end Examples
end Focil
