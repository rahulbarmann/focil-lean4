/-
  Focil/EndToEnd.lean

  End-to-end FOCIL safety against a concrete EVM-validity model.

  ## What this module provides

  Until this module, the safety theorems in `Focil/Safety.lean`
  and the PoS-derived theorem in `Focil/StakeModel.lean` were
  parameterised over the validity predicate. Concrete
  censorship-resistance claims required the consumer to plug in
  a faithful realization of `CanAppend`.

  This module supplies one such realization, end-to-end. It
  pins `canAppend` to `canAppendToBlock initial` from
  `Focil/AccountState.lean` (the cheap nonce proxy faithful to
  the EOA case described by EIP-7805 lead author Thomas Thiery
  in his Mar 16 2026 ethereum-magicians post on FOCIL handshake
  Native Account Abstraction) and proves censorship resistance
  with no opaque predicates anywhere in the chain.

  ## What is proven

  - `focil_concrete_safety`: the headline 1-of-N theorem fires
    against a concrete `ForkChoice` whose `canAppend` is the
    nonce-only `canAppendToBlock`. The conclusion
    `tx ∈ b.transactions` holds whenever every hypothesis is
    discharged using *only* concrete account-state arithmetic.

  - `focil_concrete_pos_safety`: the same end-to-end safety
    claim derived from the standard ">2/3 honest validators"
    PoS assumption, with no `ForkChoice` postulates and no
    opaque predicates remaining.

  Both theorems are corollaries of the parameterised theorems
  in `Focil/Safety.lean` and `Focil/StakeModel.lean`,
  specialized to the concrete validity model. The composition
  is direct.

  ## What axioms are involved

  These theorems compose `focil_one_of_n_protection` (zero
  axioms) and the PoS-derivation chain (which uses
  `propext` and `Quot.sound` via the counting argument).
  No `Classical.choice`, no placeholder-proof axiom. The CI's
  `#print axioms` step records the axiom dependency
  precisely.

  ## Scope of the concrete claim

  The concrete model tracks per-sender nonces only. This is
  exactly the proxy soispoke describes for the EOA case
  ("This proxy is cheap... and works well for EOAs"). It does
  not cover:

  - Balance-aware EVM validity (a colluding party who drains
    a sender's balance below the base-fee minimum can
    invalidate IL transactions; FINDINGS §2.3 lists this as
    a separate attack vector).
  - EIP-7702 delegations.
  - EIP-8141 Frame Transactions, where validity requires
    executing VERIFY frames against post-state. Those need
    the bounded-validation-prefix replay rule from soispoke's
    Mar 16 post.

  The concrete safety claim in this module is therefore
  precise: under the EOA nonce proxy, one non-equivocating IL
  containing a transaction whose nonce matches its sender's
  expected nonce in the post-state forces inclusion in any
  canonical block (modulo the block-fullness exemption).

  Extending the concrete model to balance-awareness is the
  natural next contribution; see CONTRIBUTING.md and
  FINDINGS §4.3.
-/

import Focil.Types
import Focil.Protocol
import Focil.ForkChoice
import Focil.Helpers
import Focil.Safety
import Focil.StakeModel
import Focil.AccountState

namespace Focil

-- =========================================================================
-- End-to-end safety, against a concrete `ForkChoice`
-- =========================================================================

/--
  **End-to-end FOCIL censorship resistance against a concrete
  EVM-validity model.**

  This is the headline theorem at full concreteness: the
  validity predicate is pinned to the nonce-only
  `canAppendToBlock initial` from `Focil/AccountState.lean`,
  which is the EOA proxy described by EIP-7805's lead author
  in his Mar 16 2026 ethereum-magicians post. Every hypothesis
  is checkable using concrete account-state arithmetic; no
  opaque predicate appears anywhere.

  Hypotheses:

  - `h_canAppend_pin`: the fork-choice rule's bundled
    `canAppend` predicate is the concrete
    `canAppendToBlock initial`. This is how a deployment
    would commit to the EOA proxy at instance-construction
    time.
  - `h_listed_by_some_honest_member`: at least one
    non-equivocating IL in the store contains `tx`
    (the 1-of-N witness).
  - `h_can_append`: `tx`'s nonce equals its sender's
    next-expected nonce after `b`'s transactions have been
    applied to `initial`. Concrete arithmetic, decidable.
  - `h_block_not_full`: `b` is not full under `fc.full`.
  - `h_canonical`: `b` is canonical under `fc`.

  Conclusion: `tx ∈ b.transactions`.

  This is the result EIP-7805's marquee "1-of-N honesty"
  claim looks like in fully-concrete form: all four
  abstractions of the original theorem (`CanAppend`,
  `ForkChoice` obligations, fullness, IL bookkeeping) are
  discharged by code or by the explicit hypotheses, and
  inclusion is forced as a Lean kernel-checked consequence.
-/
theorem focil_concrete_safety
    (fc : ForkChoice) (b : Block) (tx : Transaction)
    (initial : AccountState)
    (h_canAppend_pin :
      fc.canAppend = fun tx' b' => canAppendToBlock initial b' tx')
    (h_listed_by_some_honest_member :
      ∃ il, il ∈ fc.state.stored_ils
            ∧ IsConsidered fc.state il
            ∧ tx ∈ il.transactions)
    (h_can_append    : canAppendToBlock initial b tx)
    (h_block_not_full: ¬ fc.full b)
    (h_canonical     : IsCanonical fc b) :
    tx ∈ b.transactions := by
  apply focil_one_of_n_protection fc b tx
    h_listed_by_some_honest_member ?_ h_block_not_full h_canonical
  rw [h_canAppend_pin]
  exact h_can_append

-- =========================================================================
-- End-to-end safety, derived from PoS ">2/3 honest" assumption
-- =========================================================================

/--
  **End-to-end FOCIL censorship resistance, derived from PoS,
  against a concrete EVM-validity model.**

  The marquee result of the project at full concreteness.
  Composes two prior derivations:

  1. The `ForkChoice` structural obligations
     (`quorum_has_honest_voter`, `honest_attester_compliance`)
     are derived from Ethereum's standard ">2/3 honest"
     assumption via `AttesterRun.toForkChoice`
     (`Focil/StakeModel.lean`).
  2. The validity predicate is pinned to the concrete
     nonce-only `canAppendToBlock initial`
     (`Focil/AccountState.lean`).

  Read end-to-end:

      >2/3 honest validators
        ∧ honest validators only vote for compliant blocks
          (compliance computed against the concrete nonce model)
        ∧ ≥2/3 voted for `b`
        ∧ some non-equivocating IL listed `tx`
        ∧ `tx`'s nonce matches its sender's next-expected
          nonce in `b`'s post-state
        ∧ `b` is not full
      ⟹ `tx ∈ b.transactions`.

  No `ForkChoice` postulates remain. No opaque predicates
  appear in the conclusion's reasoning. The only remaining
  axioms-of-faith are:

  - Ethereum's standard ">2/3 honest" assumption (encoded as
    `s.honest_majority`).
  - The spec's "honest attesters refuse non-compliant blocks"
    rule (encoded as `r.honest_rule`, where compliance is
    computed against the concrete nonce model).

  Both are inputs the user must supply. The concrete validity
  predicate is fully realised in Lean; nothing about the
  EVM-validity layer is opaque.

  ## Scope reminder

  The concrete model tracks per-sender nonces only. The same
  proof shape lifts to a balance-aware model (see
  CONTRIBUTING.md §3 for the next contribution opportunity).
  EIP-8141 Frame Transactions are out of scope until the
  bounded-validation-prefix rule from soispoke's Mar 16 post
  is formalised.
-/
theorem focil_concrete_pos_safety
    {s : StakeModel} (r : AttesterRun s)
    (b : Block) (tx : Transaction)
    (initial : AccountState)
    (h_canAppend_pin :
      r.canAppend = fun tx' b' => canAppendToBlock initial b' tx')
    (h_listed_by_some_honest_member :
      ∃ il, il ∈ r.state.stored_ils
            ∧ IsConsidered r.state il
            ∧ tx ∈ il.transactions)
    (h_can_append    : canAppendToBlock initial b tx)
    (h_block_not_full: ¬ r.full b)
    (h_canonical     : IsCanonical r.toForkChoice b) :
    tx ∈ b.transactions := by
  apply focil_concrete_safety r.toForkChoice b tx initial
    ?_ h_listed_by_some_honest_member h_can_append
    h_block_not_full h_canonical
  exact h_canAppend_pin

-- =========================================================================
-- Concrete builder-side contrapositive
-- =========================================================================

/--
  **Concrete builder-side contrapositive.**

  The contrapositive of `focil_concrete_pos_safety`: a block
  that omits an IL transaction whose nonce concretely matches
  the sender's next-expected nonce (against
  `AccountState.initial`) cannot become the canonical chain
  head under the PoS-derived `ForkChoice`.

  Useful as a builder-incentive statement at full
  concreteness: "if I propose a block that omits a
  nonce-valid IL transaction, my block is orphaned by the
  fork-choice rule." Every hypothesis is decidable on
  concrete account-state data; no opaque predicate appears.
-/
theorem focil_concrete_pos_censoring_block_not_canonical
    {s : StakeModel} (r : AttesterRun s)
    (b : Block) (tx : Transaction)
    (initial : AccountState)
    (h_canAppend_pin :
      r.canAppend = fun tx' b' => canAppendToBlock initial b' tx')
    (h_listed_by_some_honest_member :
      ∃ il, il ∈ r.state.stored_ils
            ∧ IsConsidered r.state il
            ∧ tx ∈ il.transactions)
    (h_can_append    : canAppendToBlock initial b tx)
    (h_block_not_full: ¬ r.full b)
    (h_tx_excluded   : tx ∉ b.transactions) :
    ¬ IsCanonical r.toForkChoice b := by
  intro h_canonical
  exact h_tx_excluded
    (focil_concrete_pos_safety r b tx initial
      h_canAppend_pin h_listed_by_some_honest_member
      h_can_append h_block_not_full h_canonical)

end Focil
