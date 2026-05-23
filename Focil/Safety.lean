/-
  Focil/Safety.lean

  The main safety theorem of FOCIL: censorship resistance.

  Statement, in plain English:

  > Fix any `ForkChoice` value (which bundles a fork-choice store
  > snapshot, a block-fullness model, and the two soundness
  > obligations on attester voting). For any block, any inclusion
  > list containing a transaction: if the inclusion list is in
  > the bundled store, its author is not in the equivocator set,
  > the transaction could be validly appended to the block, the
  > block is not full, and the block is the canonical chain head,
  > then the transaction must be in the block.

  Argument:

  1. Canonicality forces compliance against `fc`'s bundled
     context (`canonical_implies_compliant`).
  2. Compliance applied to the specific (IL, tx) pair gives a
     three-way disjunction: the transaction is included, or it
     cannot be appended, or the block is full.
  3. The latter two are excluded by hypothesis. Only inclusion
     remains.

  Caveats and disclosures (FINDINGS.md §7):

  - The theorem is conditional on the two soundness obligations
    of `ForkChoice` being supplied by the consumer. It does not
    derive censorship resistance from PoS first principles.
  - It is also conditional on a faithful realisation of
    `CanAppend` (FINDINGS.md §4.3) and on `state.stored_ils` /
    `state.equivocators` being correctly populated by an honest
    execution of `on_inclusion_list` (§2.6).
  - The compliance check `CompliantWith` does not capture
    sequential dependence between IL transactions (§2.5).
-/

import Focil.Types
import Focil.Protocol
import Focil.ForkChoice
import Focil.Helpers

namespace Focil

-- =========================================================================
-- The main safety theorem
-- =========================================================================

/--
  **FOCIL censorship resistance (main theorem).**

  Hypotheses:

  - `h_tx_in_il`:        `tx` is in some inclusion list `il`.
  - `h_il_stored`:       `il` is in `fc.state.stored_ils`.
  - `h_il_considered`:   `il`'s author is not in
                         `fc.state.equivocators` (so attesters
                         consider this IL).
  - `h_can_append`:      `tx` could be validly appended to `b`'s
                         end-state (`CanAppend tx b`).
  - `h_block_not_full`:  `b` does not satisfy `fc.full`.
  - `h_canonical`:       `b` is the canonical chain head under
                         the fork-choice rule `fc`.

  Conclusion: `tx ∈ b.transactions`.

  See the file-level comment for caveats. In particular, the
  hypothesis `h_il_considered` is "not yet observed equivocating,"
  not "honest in the colloquial sense" (FINDINGS.md §2.4).
-/
theorem focil_censorship_resistance
    (fc : ForkChoice) (b : Block) (il : InclusionList) (tx : Transaction)
    (h_tx_in_il      : tx ∈ il.transactions)
    (h_il_stored     : il ∈ fc.state.stored_ils)
    (h_il_considered : IsConsidered fc.state il)
    (h_can_append    : CanAppend tx b)
    (h_block_not_full: ¬ fc.full b)
    (h_canonical     : IsCanonical fc b) :
    tx ∈ b.transactions := by
  -- Step 1: canonicality forces FOCIL compliance against the
  -- bundled context (this is where both ForkChoice obligations
  -- are used).
  have hCompl : FocilCompliant fc.full b fc.state :=
    canonical_implies_compliant fc b h_canonical
  -- Step 2: instantiate compliance at our specific IL and tx,
  -- yielding the per-tx three-way disjunction.
  have h := hCompl il h_il_stored h_il_considered tx h_tx_in_il
  -- Step 3: case-split on the disjunction. Only the first case
  -- can survive the remaining hypotheses.
  cases h with
  | inl h_in =>
    -- `tx ∈ b.transactions`: this is the goal.
    exact h_in
  | inr h_rest =>
    cases h_rest with
    | inl h_not_appendable =>
      -- `¬ CanAppend tx b` directly contradicts `h_can_append`.
      exact (h_not_appendable h_can_append).elim
    | inr h_full =>
      -- `fc.full b` directly contradicts `h_block_not_full`.
      exact (h_block_not_full h_full).elim

-- =========================================================================
-- Builder-side contrapositive
-- =========================================================================

/--
  **Contrapositive corollary** of `focil_censorship_resistance`.

  Reading: a candidate block `b` that omits a transaction `tx`
  satisfying the standard inclusion preconditions cannot become
  the canonical chain head.

  This is the form a builder reasoning about block construction
  cares about: "if I exclude this transaction, my block gets
  orphaned by the fork-choice rule."
-/
theorem censoring_block_not_canonical
    (fc : ForkChoice) (b : Block) (il : InclusionList) (tx : Transaction)
    (h_tx_in_il      : tx ∈ il.transactions)
    (h_il_stored     : il ∈ fc.state.stored_ils)
    (h_il_considered : IsConsidered fc.state il)
    (h_can_append    : CanAppend tx b)
    (h_block_not_full: ¬ fc.full b)
    (h_tx_excluded   : tx ∉ b.transactions) :
    ¬ IsCanonical fc b := by
  intro h_canonical
  -- If the block were canonical the main theorem would force
  -- `tx ∈ b.transactions`, contradicting `h_tx_excluded`.
  exact h_tx_excluded
    (focil_censorship_resistance fc b il tx
      h_tx_in_il h_il_stored h_il_considered
      h_can_append h_block_not_full h_canonical)

end Focil
