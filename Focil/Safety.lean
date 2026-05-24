/-
  Focil/Safety.lean

  The safety theorems of FOCIL: censorship resistance.

  This file states FOCIL's safety claim at two levels of generality.

  - `focil_one_of_n_protection` is the **headline theorem**: it
    matches the 1-of-N honesty claim that EIP-7805 actually makes.
    Read: if any non-equivocating IL in the fork-choice store
    contains an appendable transaction `tx`, and the candidate
    block is canonical and not full, then `tx` is in the block.
    The witness IL is existentially quantified, so the theorem
    fires whenever *at least one* honest committee member listed
    `tx`.

  - `focil_censorship_resistance` is the per-IL building block.
    It takes the witness IL as an explicit parameter. The 1-of-N
    headline theorem is a thin corollary of this one.

  - `censoring_block_not_canonical` is the builder-side
    contrapositive of `focil_censorship_resistance`.

  Argument structure (shared by both forward theorems):

  1. Canonicality forces compliance against `fc`'s bundled
     context (`canonical_implies_compliant`).
  2. Compliance applied to the witness (IL, tx) pair gives a
     three-way disjunction: the transaction is included, or it
     cannot be appended, or the block is full.
  3. The latter two are excluded by hypothesis. Only inclusion
     remains.

  Caveats and disclosures (FINDINGS.md §7):

  - Both theorems are conditional on the two soundness
    obligations of `ForkChoice` being supplied by the consumer.
    They do not derive censorship resistance from PoS first
    principles.
  - They are also conditional on a faithful realisation of
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
-- Per-IL building block
-- =========================================================================

/--
  **Per-IL censorship resistance.**

  Building block for the headline 1-of-N theorem
  (`focil_one_of_n_protection` below). Given an *explicit*
  witness IL, this theorem says the transaction must be in the
  canonical block.

  Hypotheses:

  - `h_tx_in_il`:        `tx` is in inclusion list `il`.
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

  Note: `h_il_considered` is "not yet observed equivocating,"
  not "honest in the colloquial sense" (FINDINGS.md §2.4).
-/
theorem focil_censorship_resistance
    (fc : ForkChoice) (b : Block) (il : InclusionList) (tx : Transaction)
    (h_tx_in_il      : tx ∈ il.transactions)
    (h_il_stored     : il ∈ fc.state.stored_ils)
    (h_il_considered : IsConsidered fc.state il)
    (h_can_append    : fc.canAppend tx b)
    (h_block_not_full: ¬ fc.full b)
    (h_canonical     : IsCanonical fc b) :
    tx ∈ b.transactions := by
  have hCompl : FocilCompliant fc.canAppend fc.full b fc.state :=
    canonical_implies_compliant fc b h_canonical
  have h := hCompl il h_il_stored h_il_considered tx h_tx_in_il
  cases h with
  | inl h_in => exact h_in
  | inr h_rest =>
    cases h_rest with
    | inl h_not_appendable => exact (h_not_appendable h_can_append).elim
    | inr h_full           => exact (h_block_not_full h_full).elim

-- =========================================================================
-- Headline theorem: FOCIL's 1-of-N censorship-resistance guarantee
-- =========================================================================

/--
  **FOCIL's 1-of-N censorship-resistance guarantee.**

  This is the formal counterpart of EIP-7805's marquee claim:
  it suffices that *at least one* non-equivocating IL committee
  member listed the transaction for it to be force-included in
  any canonical block (modulo invalidity and block fullness).

  The witness IL is existentially quantified inside
  `h_listed_by_some_honest_member`: the theorem fires whenever
  the fork-choice store contains *some* non-equivocating IL
  carrying `tx`. The other ILs in the store are irrelevant; an
  adversary controlling some committee seats and equivocating
  the rest does not defeat the guarantee, as long as at least
  one seat publishes a non-equivocating IL containing `tx`.

  Hypotheses:

  - `h_listed_by_some_honest_member`:
                         there exists a stored, non-equivocating
                         IL `il` with `tx ∈ il.transactions`.
  - `h_can_append`:      `tx` could be validly appended to `b`.
  - `h_block_not_full`:  `b` does not satisfy `fc.full`.
  - `h_canonical`:       `b` is the canonical chain head.

  Conclusion: `tx ∈ b.transactions`.

  Caveats:

  - "Honest member" here means "not in the equivocator set,"
    which captures the 1-of-N guarantee as the EIP states it.
    A Byzantine member who has not yet been caught equivocating
    still satisfies the precondition; the guarantee degrades to
    "1-of-(N − equivocators)" once equivocators have been
    detected. See FINDINGS.md §2.4 and `Tests/Examples.lean`
    Scenarios 9–10 for concrete demonstrations.
  - All caveats from `focil_censorship_resistance` apply.
-/
theorem focil_one_of_n_protection
    (fc : ForkChoice) (b : Block) (tx : Transaction)
    (h_listed_by_some_honest_member :
      ∃ il, il ∈ fc.state.stored_ils
            ∧ IsConsidered fc.state il
            ∧ tx ∈ il.transactions)
    (h_can_append    : fc.canAppend tx b)
    (h_block_not_full: ¬ fc.full b)
    (h_canonical     : IsCanonical fc b) :
    tx ∈ b.transactions := by
  obtain ⟨il, h_il_stored, h_il_considered, h_tx_in_il⟩ :=
    h_listed_by_some_honest_member
  exact focil_censorship_resistance fc b il tx
    h_tx_in_il h_il_stored h_il_considered
    h_can_append h_block_not_full h_canonical

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
    (h_can_append    : fc.canAppend tx b)
    (h_block_not_full: ¬ fc.full b)
    (h_tx_excluded   : tx ∉ b.transactions) :
    ¬ IsCanonical fc b := by
  intro h_canonical
  exact h_tx_excluded
    (focil_censorship_resistance fc b il tx
      h_tx_in_il h_il_stored h_il_considered
      h_can_append h_block_not_full h_canonical)

end Focil
