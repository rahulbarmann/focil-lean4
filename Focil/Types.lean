/-
  Focil/Types.lean

  Core data model for the FOCIL formalization.

  Every type in this file fixes part of the *vocabulary* in which
  every later definition and theorem about the protocol is stated.
  Each declaration's docstring explains:

  - what the corresponding artefact is in EIP-7805 / consensus-specs,
  - what was kept and what was abstracted away,
  - why that choice was made for the safety proof.

  Reference material consulted, all pinned at consensus-specs commit
  `e678deb772fe83edd1ea54cb6d2c1e4b1e45cec6`:

  - EIP-7805 (https://eips.ethereum.org/EIPS/eip-7805).
  - `consensus-specs/specs/_features/eip7805/beacon-chain.md`.
  - `consensus-specs/specs/_features/eip7805/fork-choice.md`.
  - `consensus-specs/specs/_features/eip7805/validator.md`.

  We deliberately do not depend on Mathlib (FINDINGS.md §4.1). The
  safety proof needs only `List` membership, and avoiding Mathlib
  keeps the build reproducible from a stock Lean toolchain.
-/

namespace Focil

-- =========================================================================
-- Validator and transaction primitives
-- =========================================================================

/--
  A validator's stable index inside the beacon-state validator
  registry.

  In `consensus-specs` Python this is `ValidatorIndex`, defined as
  `uint64`. We use `Nat` because the safety theorem never reasons
  about index bounds; we only ever compare indices for equality
  (membership in the IL committee, equivocator set, ...).
-/
abbrev ValidatorIndex : Type := Nat

/--
  A transaction, abstracted to exactly the fields the safety
  theorem needs to talk about.

  Field rationale:

  - `id`: uniquely identifies the transaction. Stands in for the
    RLP hash that the EL would compute. Used to talk about "the
    same transaction" appearing in different lists.
  - `sender`: the EOA that signed the transaction. Needed because
    nonce/balance based invalidation is per-sender (EIP-7805
    §"Payload Construction").
  - `nonce`: needed to model the conditional inclusion rule. The
    proposer may legitimately drop an IL tx whose nonce no longer
    matches the post-state.
  - `gas`: needed to model the "block is full" carve-out. An IL
    tx may be omitted if its gas exceeds `gas_left`.

  The alternative we considered was `structure Transaction where
  hash : Nat`, leaving sender/nonce/gas opaque. We rejected it
  because even an abstract safety statement has to mention the
  conditional inclusion rule, which mentions nonce and gas. Having
  those fields visible in the data model lets test scenarios in
  `Tests/Examples.lean` build concrete witnesses without extra
  axioms.

  Note: balance is *not* a field. Per-sender balance lives on the
  post-state of a `Block` and is captured indirectly by the abstract
  `CanAppend` predicate in `Focil/Protocol.lean`.
-/
structure Transaction where
  /-- A unique identifier; stands in for the RLP hash. -/
  id     : Nat
  /-- The EOA address that signed this transaction. -/
  sender : Nat
  /-- The transaction's nonce relative to its sender. -/
  nonce  : Nat
  /-- The transaction's gas limit. -/
  gas    : Nat
  deriving DecidableEq, Repr

-- =========================================================================
-- Inclusion list and block containers
-- =========================================================================

/--
  An inclusion list as constructed by a single member of the IL
  committee.

  This mirrors the Python `InclusionList` container in
  `beacon-chain.md`:

  ```python
  class InclusionList(Container):
      slot: Slot
      validator_index: ValidatorIndex
      inclusion_list_committee_root: Root
      transactions: List[Transaction, MAX_TRANSACTIONS_PER_INCLUSION_LIST]
  ```

  We drop `inclusion_list_committee_root` from the formalization.
  In the Python spec it is a sanity check used by
  `on_inclusion_list` to match an IL to its committee; it is not
  load-bearing for the safety argument once we assume the validator
  was on the committee.

  The validator-guide document additionally mentions
  `inclusion_list.parent_hash` and `inclusion_list.parent_root`,
  but these fields do not appear on the `InclusionList` container
  in `beacon-chain.md`. This discrepancy is recorded in
  FINDINGS.md §1.2.
-/
structure InclusionList where
  /-- The slot whose IL committee this list contributes to. -/
  slot            : Nat
  /-- The committee member who authored this list. -/
  validator_index : ValidatorIndex
  /-- The transactions the author wants force-included. -/
  transactions    : List Transaction
  deriving DecidableEq, Repr

/--
  The minimal block model needed to talk about FOCIL compliance.

  Field rationale:

  - `slot`: so we can talk about which slot a block was produced
    for.
  - `proposer`: the validator who proposed this block.
  - `transactions`: the ordered list of transactions actually
    included in the execution payload.
  - `gasLimit`: the block's gas ceiling.

  `DecidableEq` is derived so that concrete examples can compare
  blocks without extra axioms; this is purely a convenience for
  `Tests/Examples.lean`.

  We deliberately do not embed:

  - The post-state (account nonces and balances). Modelling that
    fully would require an EVM model, which is far outside the
    scope of a censorship-resistance proof. Instead we expose the
    abstract `CanAppend : Transaction → Block → Prop` predicate
    in `Focil/Protocol.lean`.
  - Execution-payload metadata (parent hash, withdrawals, etc.).
    None of it participates in the FOCIL safety argument.
-/
structure Block where
  /-- The slot this block was proposed for. -/
  slot         : Nat
  /-- The validator who proposed this block. -/
  proposer     : ValidatorIndex
  /-- The ordered transactions included in the execution payload. -/
  transactions : List Transaction
  /-- The block's gas-limit ceiling. -/
  gasLimit     : Nat
  deriving DecidableEq, Repr

-- =========================================================================
-- Fork-choice store projection
-- =========================================================================

/--
  The fork-choice store, projected onto the parts that FOCIL
  touches.

  In `consensus-specs` the modified `Store` adds two fields:

  ```python
  inclusion_lists           : Dict[Tuple[Slot, Root], List[InclusionList]]
  inclusion_list_equivocators : Dict[Tuple[Slot, Root], Set[ValidatorIndex]]
  ```

  We collapse the dictionary keyed on `(slot, committee_root)` into
  a single flat list of `stored_ils`, because the safety argument
  is always parameterised by *one specific slot* (the slot whose
  ILs constrain the next block). An attester reasoning about a
  block at slot `N+1` only cares about the bucket
  `(N, committee_root_for_N)`, so a single list suffices. We
  capture the slot via `current_slot`.

  The `equivocators` field stores, by index, the validators who
  have been observed to publish two distinct ILs for this slot.
  In the Python spec these validators are completely ignored when
  checking compliance; we encode that exclusion via `IsConsidered`
  below.

  Caveats and disclosed model limits:

  - This model assumes a single canonical "honest stored set"
    (FINDINGS.md §2.2). Different attesters can in reality have
    different stored sets.
  - We do not model the construction of `stored_ils` and
    `equivocators` from the underlying gossip stream; they are
    inputs (FINDINGS.md §2.6).
-/
structure FocilState where
  /-- The slot to which this state's IL bucket belongs. -/
  current_slot : Nat
  /-- ILs accepted into the store before the view freeze deadline. -/
  stored_ils   : List InclusionList
  /-- Committee members observed to have equivocated. -/
  equivocators : List ValidatorIndex
  deriving Repr

-- =========================================================================
-- Equivocator filter
-- =========================================================================

/--
  A validator is *honestly attributed* in a given store iff they
  are not in the equivocator set for that store.

  This is *not* the same as "the validator is honest." A Byzantine
  validator who has not yet been caught equivocating would still
  satisfy this predicate. The name reflects what the spec actually
  cares about: whether the validator's *attribution* (the IL we
  received from them) is trusted by the fork-choice store.
-/
def IsHonestlyAttributed (state : FocilState) (v : ValidatorIndex) : Prop :=
  v ∉ state.equivocators

/--
  An IL is *considered* by the compliance check iff its author is
  honestly attributed in the current store.

  Per the EIP-7805 fork-choice changes:

  > "If more than one IL is observed from the same IL committee
  >  member, mark the committee member as an equivocator and
  >  ignore any further ILs from them."

  This wraps `IsHonestlyAttributed` to keep the protocol-layer
  definitions free of `il.validator_index ∉ state.equivocators`
  noise.
-/
def IsConsidered (state : FocilState) (il : InclusionList) : Prop :=
  IsHonestlyAttributed state il.validator_index

end Focil
