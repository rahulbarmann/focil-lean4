/-
  Focil/ForkChoice.lean

  The slice of LMD-GHOST that FOCIL touches, captured as a small
  Lean structure with two propositional obligations.

  We model only what the safety argument needs:

  1. There is a notion of a block being the *canonical chain head*.
     For our purposes the only structural fact about it is that
     canonicality requires a quorum of attestations.

  2. Honest attesters refuse to vote for non-compliant blocks.
     Therefore a non-compliant block cannot accumulate a quorum
     of honest votes, and therefore cannot be canonical.

  This file *does not* model: the LMD weight tally, proposer
  boost, timeliness boosts, justification/finalisation, or
  reorg dynamics across slots. None of these participate in the
  FOCIL-specific compliance check.

  ## Why state and fullness are fields of the structure

  An honest attester votes relative to *their* fork-choice store
  snapshot at attestation time. A `ForkChoice` value therefore
  bundles the entire attestation context:

  - the fork-choice store snapshot (`state`),
  - the block-fullness model in force (`full`),
  - the set of honest validators (`IsHonest`),
  - the quorum predicate (`HasQuorum`),
  - the vote relation (`Voted`),
  - and the two soundness obligations relating these.

  An earlier draft of this file pulled `state` and `full` out as
  parameters of the obligation field `honest_attester_compliance`
  itself, universally quantifying over them. That signature was
  *unsatisfiable non-vacuously*: an honest validator who votes for
  block `b` cannot be required to make `b` compliant against
  every conceivable state, only against the state at attestation
  time. With `CanAppend` opaque, the universally-quantified form
  was discharge-able only by emptying out the antecedent. The
  current signature lets the discharge proof be proportionate to
  what an honest attester actually does. See FINDINGS.md §5 for
  the full discussion.

  The two soundness obligations remain propositional fields of
  the `ForkChoice` structure. Concrete instances must discharge
  them; `Tests/Examples.lean` provides one vacuous and one
  non-vacuous instance.
-/

import Focil.Types
import Focil.Protocol

namespace Focil

-- =========================================================================
-- The ForkChoice abstraction
-- =========================================================================

/--
  The minimal fork-choice interface FOCIL needs.

  An instance of `ForkChoice` captures a single attestation
  context: a fork-choice store snapshot, a block-fullness model,
  a set of honest validators, a quorum predicate, and a vote
  relation, together with two soundness obligations relating
  them.

  **Context fields:**

  - `state`: the fork-choice store at attestation time. The
    safety argument reads `stored_ils` and `equivocators` from
    here.
  - `full`: the block-fullness model. The safety argument
    requires the candidate block to *not* satisfy this.

  **Predicate fields:**

  - `IsHonest`: which validators behave honestly in this run.
  - `HasQuorum`: whether a candidate block has accumulated
    enough attestations to be eligible to become the canonical
    head.
  - `Voted`: a per-validator/block vote relation. Concrete
    instantiations would derive it from the attestation pool.

  **Soundness obligations** (the two propositional fields any
  concrete instance must discharge):

  - `quorum_has_honest_voter`: any block reaching a quorum has
    at least one validator who is `IsHonest` and who `Voted` for
    it. This is *strictly weaker* than the >2/3 honest
    supermajority assumption Ethereum PoS relies on; it is the
    only BFT-flavoured assumption needed for the
    censorship-resistance safety property.
  - `honest_attester_compliance`: the protocol-level invariant
    that an honest attester voting for a block guarantees the
    block is FOCIL-compliant relative to *this* fork-choice
    store. This is the *normative* behaviour of an honest
    attester per EIP-7805.

  **Disclosure:** `Tests/Examples.lean` ships two instances:

  - `emptyForkChoice` discharges both obligations vacuously by
    making `HasQuorum` and `Voted` constantly false.
  - `threeValidatorForkChoice` is a non-vacuous 3-validator
    scenario where the obligations are discharged by genuine
    case analysis.

  A future refinement that derives the obligations from a more
  primitive PoS / LMD-GHOST model is the largest piece of
  follow-on work; see CONTRIBUTING.md.
-/
structure ForkChoice where
  /-- The fork-choice store snapshot at attestation time. -/
  state       : FocilState
  /--
    Validity predicate (formal counterpart of "EVM-valid
    appendability"). Bundled here so concrete instances can
    pin a specific model (e.g. nonce/balance proxy from
    `Focil/AccountState.lean`) and the safety chain reads the
    same predicate everywhere.
  -/
  canAppend   : Transaction → Block → Prop
  /-- The block-fullness model in force for this run. -/
  full        : Block → Prop
  /-- Validators who behave honestly in this run. -/
  IsHonest    : ValidatorIndex → Prop
  /-- Predicate: this block has a quorum of attestations. -/
  HasQuorum   : Block → Prop
  /-- Per-validator/block vote relation. -/
  Voted       : ValidatorIndex → Block → Prop
  /--
    Soundness obligation: a block with a quorum has at least one
    validator who is honest *and* voted for it.
  -/
  quorum_has_honest_voter :
    ∀ b : Block, HasQuorum b →
      ∃ v : ValidatorIndex, IsHonest v ∧ Voted v b
  /--
    Soundness obligation: honest validators only vote for blocks
    that are FOCIL-compliant against the bundled `state` under
    the bundled `canAppend` and `full` models.
  -/
  honest_attester_compliance :
    ∀ (b : Block) (v : ValidatorIndex),
      IsHonest v →
      Voted v b →
      FocilCompliant canAppend full b state

-- =========================================================================
-- Canonicality
-- =========================================================================

/--
  In FOCIL's modified LMD-GHOST rule, a block is the *canonical
  chain head* iff it has accumulated a quorum.

  This is a deliberate simplification: real LMD-GHOST is much more
  intricate (proposer boost, equivocation handling, timeliness),
  but only the quorum requirement is load-bearing for the
  censorship-resistance argument. Any richer fork-choice rule that
  preserves "canonical implies quorum" admits the same safety
  theorem unchanged.
-/
def IsCanonical (fc : ForkChoice) (b : Block) : Prop :=
  fc.HasQuorum b

-- =========================================================================
-- Cornerstone lemma: canonicality forces compliance
-- =========================================================================

/--
  **Cornerstone lemma.** A canonical block under `fc` is
  FOCIL-compliant against `fc.state` under `fc.full`.

  Argument:

  1. Canonicality unfolds to `HasQuorum b`.
  2. By `quorum_has_honest_voter`, there exists an honest
     validator `v` who voted for `b`.
  3. By `honest_attester_compliance`, that vote forces FOCIL
     compliance against `fc.state`.

  This is the load-bearing step the safety theorem rests on.
-/
theorem canonical_implies_compliant
    (fc : ForkChoice) (b : Block)
    (h_canon : IsCanonical fc b) :
    FocilCompliant fc.canAppend fc.full b fc.state := by
  have hQuorum : fc.HasQuorum b := h_canon
  obtain ⟨v, hHonest, hVoted⟩ :=
    fc.quorum_has_honest_voter b hQuorum
  exact fc.honest_attester_compliance b v hHonest hVoted

/--
  Direct contrapositive of `canonical_implies_compliant`: a block
  that fails to be FOCIL-compliant against `fc`'s context cannot
  be canonical under `fc`.

  Useful as a builder-side incentive statement: "if I propose a
  block that misses an obligation, my block is not canonical."
-/
theorem noncompliant_block_not_canonical
    (fc : ForkChoice) (b : Block)
    (h_noncompliant : ¬ FocilCompliant fc.canAppend fc.full b fc.state) :
    ¬ IsCanonical fc b := by
  intro h_canon
  exact h_noncompliant
    (canonical_implies_compliant fc b h_canon)

end Focil
