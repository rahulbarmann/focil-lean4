/-
  Focil/Protocol.lean

  The protocol-layer rules of FOCIL: when a block satisfies an
  inclusion list, and when it satisfies the whole fork-choice
  store of inclusion lists.

  We follow the description of `validate_inclusion_lists` in
  `consensus-specs/specs/_features/eip7805/fork-choice.md`. The
  Python function body is literally `...` (FINDINGS.md §2.1); the
  only normative description is its docstring:

  > "verify if the `execution_payload` satisfies
  >  `inclusion_list_transactions` validity conditions either when
  >  all transactions are present in payload or when any missing
  >  transactions are found to be invalid when appended to the end
  >  of the payload unless the block is full."

  In Lean: for every IL transaction `tx`, either
    (a) `tx` is already in the block,
    (b) `tx` cannot be appended to the end of the block, or
    (c) the block is full.

  Disclosed model limitations:

  - Sequential dependence between IL transactions
    (FINDINGS.md §2.5). `CompliantWith` evaluates each
    transaction's appendability independently against the final
    block, not against a tentative post-state with prior IL
    transactions appended.
  - The EVM is not modelled; `CanAppend` is opaque (§4.3).
  - Block fullness is parameterised, not computed (§2.1 case 2).
-/

import Focil.Types

namespace Focil

-- =========================================================================
-- Abstract predicates: block fullness and EVM appendability
-- =========================================================================

/-
  ## On block fullness

  Compliance predicates below take a `full : Block → Prop`
  parameter rather than fixing one definition. Reasons:

  - The EIP is ambiguous about whether "full" means *literally*
    at the gas limit or *too full to fit even the smallest
    possible transaction* (FINDINGS.md §2.1 case 2). The two
    readings diverge for blocks with leftover gas under 21 000.
  - Different example scenarios want different fullness models;
    `Tests/Examples.lean` uses a constantly-false `neverFull` to
    isolate other rule branches.

  A future refinement could compute fullness from `gasLimit`
  minus the cumulative `gas` of `transactions`. We chose not to
  bake that in here so the safety argument remains independent
  of the gas-arithmetic layer.
-/

/--
  Whether transaction `tx` could be validly appended to the end
  of block `b`'s transactions, given `b`'s post-state.

  Formal counterpart of the EL check described in EIP-7805
  §"Execution Layer":

  > "Validate T against S by checking the nonce and balance of
  >  T.origin."

  We do not reproduce this check. Reproducing it would require
  modelling the EVM, which is far outside scope (FINDINGS.md
  §4.3). Instead we expose `CanAppend` as the abstraction the rest
  of the formalisation works with.

  The polarity matters: a transaction `tx` for which `CanAppend tx
  b` *holds* is one the proposer is *forbidden* from omitting
  (modulo block fullness). The proposer's legitimate-omission
  exemption is exactly `¬ CanAppend tx b`.

  The proof is universally quantified over `CanAppend`. Concrete
  censorship-resistance claims against a real Ethereum
  implementation require a faithful `CanAppend` realization, which
  this repository does not provide.
-/
opaque CanAppend : Transaction → Block → Prop

-- =========================================================================
-- Per-IL compliance
-- =========================================================================

/--
  Compliance of a block with a single inclusion list.

  Reads the EIP-7805 conditional inclusion rule directly. For each
  transaction `tx ∈ il.transactions`, *one* of the following holds:

  - `tx ∈ b.transactions` (already included), or
  - `¬ CanAppend tx b` (cannot be appended → legitimate omission),
    or
  - `full b` (block is full → legitimate omission).

  The `full` predicate is a parameter so that callers can plug in
  whatever fullness model fits their setting. The example
  scenarios in `Tests/Examples.lean` use a constantly-false
  `neverFull` to isolate the other rule branches; a richer
  model would compute fullness from `gasLimit` and the
  cumulative gas of `transactions`.

  Disclosed limitation (FINDINGS.md §2.5): this predicate
  quantifies over IL transactions independently. Sequential
  dependence (where IL tx `A` becoming valid requires IL tx `B`
  to have been appended first) is not captured.
-/
def CompliantWith
    (full : Block → Prop)
    (b : Block) (il : InclusionList) : Prop :=
  ∀ tx ∈ il.transactions,
    tx ∈ b.transactions ∨ ¬ CanAppend tx b ∨ full b

-- =========================================================================
-- Store-wide compliance
-- =========================================================================

/--
  A block is *FOCIL-compliant against a fork-choice store* iff it
  is `CompliantWith` every IL whose author is not a known
  equivocator.

  This is exactly what an honest attester checks before voting.
  It encodes both:

  - the per-IL compliance check `CompliantWith`, and
  - the equivocator filter from EIP-7805's fork-choice changes
    ("ignore further ILs from a known equivocator").

  An IL stored in the state but whose author is an equivocator
  imposes *no* obligation on the block. This is captured by the
  guard `IsConsidered state il`.
-/
def FocilCompliant
    (full : Block → Prop)
    (b : Block) (state : FocilState) : Prop :=
  ∀ il ∈ state.stored_ils,
    IsConsidered state il → CompliantWith full b il

-- =========================================================================
-- Auxiliary lemmas
-- =========================================================================

/--
  Direct unfolding of `FocilCompliant` at a specific
  (IL, transaction) pair.

  The safety theorem in `Focil/Safety.lean` uses this exact
  calling convention; stating it as a lemma makes that proof read
  more cleanly.
-/
theorem compliant_includes_or_excused
    {full : Block → Prop} {b : Block} {state : FocilState}
    {il : InclusionList} {tx : Transaction}
    (hCompl : FocilCompliant full b state)
    (hIl    : il ∈ state.stored_ils)
    (hConsidered : IsConsidered state il)
    (hTx    : tx ∈ il.transactions) :
    tx ∈ b.transactions ∨ ¬ CanAppend tx b ∨ full b :=
  hCompl il hIl hConsidered tx hTx

end Focil
