# Walkthrough: reading the main theorem

This is a guided tour of `Focil.focil_censorship_resistance`:
what each hypothesis means, what the conclusion gives you, and
how to read the proof.

If you have read the README and want the _conceptual_ angle, the
[Design notes](DESIGN.md) are a better starting point. This file
is for the reader who wants to look at the theorem statement and
understand it line by line.

## The statement

```lean
theorem focil_censorship_resistance
    (fc : ForkChoice) (b : Block) (il : InclusionList) (tx : Transaction)
    (h_tx_in_il      : tx ∈ il.transactions)
    (h_il_stored     : il ∈ fc.state.stored_ils)
    (h_il_considered : IsConsidered fc.state il)
    (h_can_append    : CanAppend tx b)
    (h_block_not_full: ¬ fc.full b)
    (h_canonical     : IsCanonical fc b) :
    tx ∈ b.transactions
```

## Parameters

- **`fc : ForkChoice`**: the per-attestation context. Bundles a
  fork-choice store snapshot (`fc.state`), a block-fullness
  predicate (`fc.full`), the set of honest validators
  (`fc.IsHonest`), the quorum predicate (`fc.HasQuorum`), the
  vote relation (`fc.Voted`), and the two soundness obligations.
  Every concrete fork-choice rule corresponds to one such value.
- **`b : Block`**: the candidate block whose canonicality is at
  issue.
- **`il : InclusionList`**: a single inclusion list. We talk
  about _one_ IL, not the whole committee. The "1-of-N honesty"
  guarantee from EIP-7805 is a meta-statement about _which_ IL
  you can apply this theorem to.
- **`tx : Transaction`**: the specific transaction we want to
  protect.

## Hypotheses

| Hypothesis         | Plain English                                                                                                                                                                     |
| ------------------ | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `h_tx_in_il`       | The transaction is in the inclusion list.                                                                                                                                         |
| `h_il_stored`      | The inclusion list is in the fork-choice store at attestation time; equivalently, it arrived before `VIEW_FREEZE_DEADLINE`.                                                       |
| `h_il_considered`  | The inclusion list's author has not been observed equivocating in this slot. (Note: this is _not_ "the validator is honest"; it is "we have no evidence they are Byzantine yet.") |
| `h_can_append`     | The transaction is EVM-valid as an append to the block. (`CanAppend` is opaque; any concrete refinement of EVM validity instantiates this.)                                       |
| `h_block_not_full` | The block has room for the transaction.                                                                                                                                           |
| `h_canonical`      | The block is the canonical chain head under this fork choice.                                                                                                                     |

## Conclusion

`tx ∈ b.transactions`. The transaction must be in the block.

Equivalently (`censoring_block_not_canonical`): if the block
_omits_ the transaction, the block cannot be canonical.

## How the proof unfolds

```
focil_censorship_resistance
   │
   ├─ canonical_implies_compliant fc b h_canonical
   │     │
   │     ├─ unfold IsCanonical to fc.HasQuorum b
   │     ├─ apply fc.quorum_has_honest_voter to extract
   │     │   an honest validator who voted for b
   │     └─ apply fc.honest_attester_compliance to that
   │         vote, yielding `FocilCompliant fc.full b fc.state`
   │
   └─ apply that compliance fact to (il, tx)
         │
         └─ obtain `tx ∈ b.transactions ∨ ¬ CanAppend tx b ∨ fc.full b`
              ├─ `tx ∈ b.transactions` → done
              ├─ `¬ CanAppend tx b`     → contradicts h_can_append
              └─ `fc.full b`            → contradicts h_block_not_full
```

The two soundness obligations on `fc` (`quorum_has_honest_voter`
and `honest_attester_compliance`) are consumed inside
`canonical_implies_compliant`. The theorem itself just plugs that
result into the per-transaction compliance unfolding.

## What this guarantees, precisely

- A specific transaction `tx` listed in a stored,
  non-equivocating IL is present.
- Modulo two carve-outs that the EIP grants the proposer:
  invalidity (`¬ CanAppend tx b`) and block fullness (`fc.full
b`).
- Modulo a fork-choice rule satisfying the two soundness
  obligations baked into `fc`.

## What this does _not_ guarantee

- **It does not protect transactions from a colluding party who
  invalidates them.** If an adversary can construct `b` such
  that `CanAppend tx b` is false, the hypothesis fails and the
  theorem is silent. See FINDINGS.md §2.3.
- **It does not protect transactions listed _only_ by an
  equivocator.** If `il`'s author is in `fc.state.equivocators`,
  `IsConsidered` is false, and the theorem cannot be applied to
  that IL. With more than one honest IL listing `tx`, the
  theorem still fires on _another_ IL. This is the "1-of-N
  honesty" guarantee in formal form, and it degrades to "1-of-(N
  − equivocators)." See FINDINGS.md §2.4 and `Tests/Examples.lean`
  Scenarios 9–10.
- **It does not say anything about whether `b` exists.** This
  is a safety result (bad blocks are ruled out), not a liveness
  result. The complementary "a compliant block always exists"
  claim is out of scope.
- **It does not hold against an adversary who can stop ILs from
  reaching the store.** If `il ∉ fc.state.stored_ils`, the
  theorem is silent. See FINDINGS.md §2.2.

## Trying it yourself

Open `Tests/Examples.lean` and look at Scenario 7. It builds
each of the six hypotheses against `threeValidatorForkChoice`
(a concrete fork-choice with three validators, two of them
honest, voting for `blockIncludes` which contains `tx1`) and
applies the theorem to conclude `tx1 ∈ blockIncludes.transactions`.

Then look at Scenario 8: same setup but the block is
`blockOmits` (which excludes `tx1`), and the corollary
`censoring_block_not_canonical` rules out canonicality.

Scenarios 9–10 demonstrate the equivocator degradation
described above: under a state where the IL author is an
equivocator, the inclusion guarantee for `tx1` is voided.
