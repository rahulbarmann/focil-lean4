# FOCIL formalization: research findings

This document records spec ambiguities, gaps, and abstraction
choices encountered while building the Lean 4 formalization in
`Focil/`. It is intended for protocol researchers and
consensus-layer developers; many of these items are open
questions that the formalization makes precise but does not
resolve.

Sources cross-referenced throughout:

- **EIP-7805** at <https://eips.ethereum.org/EIPS/eip-7805>.
- **consensus-specs** `_features/eip7805/` directory, pinned at
  commit `e678deb772fe83edd1ea54cb6d2c1e4b1e45cec6`:
    - `beacon-chain.md`
    - `fork-choice.md`
    - `validator.md`

Each finding carries two tags:

- **Verification status**: `CONFIRMED AGAINST SPEC`, `OPEN
QUESTION`, or `MODEL LIMITATION DISCLOSED`.
- **Engagement**: `OPEN` (a question or issue inviting
  discussion or upstream resolution) or `RESOLVED IN
FORMALIZATION` (the formalization handles it directly).

---

## Executive summary

This formalization proves FOCIL's 1-of-N censorship-resistance
guarantee end-to-end, derived from Ethereum's standard ">2/3
honest validators" assumption. Three of the items below are
substantive observations the formalization surfaced; the rest
are spec-hygiene issues and disclosed model limitations.

### Substantive observations

- **§2.7, The honest-attester invariant in EIP-7805 admits two
  non-equivalent formal readings, and the natural one is
  unsatisfiable.** Reading "honest attesters refuse to vote for
  non-compliant blocks" globally (across all stores) versus
  locally (against the attester's own store) yields formally
  different propositions. The global reading cannot be
  discharged non-vacuously when EVM validity is opaque. The
  spec is correct under the local reading, but informal
  arguments that compose the rule across attesters with
  different stores have a hidden quantifier-scope assumption.

- **§2.4, Equivocation is a free censorship channel for any
  transaction listed by only one IL committee member.** A
  Byzantine member can void their own contribution by signing
  two distinct ILs. The EIP's existing equivocation handling
  (ignoring further ILs from a known equivocator) is correct
  fork-choice safety, but it degrades the "1-of-N honesty"
  guarantee to "1-of-(N − equivocators)" for any transaction
  listed only by an equivocating member. The EIP addresses
  equivocation at the bandwidth level only. Demonstrated by
  example in `Tests/Examples.lean` Scenarios 9–10.

- **§2.3, Adversarial validity changes are formally
  exhibited.** A colluding party sharing an IL transaction's
  `(sender, nonce)` can submit a transaction that, once
  appended by the proposer, makes the IL transaction
  non-appendable. The proposer can then legitimately invoke
  the conditional-inclusion exemption. This is formalized as
  the theorem `front_running_breaks_appendability` in
  `Focil/AccountState.lean`, with `Tests/Examples.lean`
  Scenario 13 demonstrating the attack on concrete data. The
  protocol-level question for the EIP authors: should the EIP
  commit to a per-account-state abstraction the proposer must
  respect, or is the gas cost of the colluding transaction
  considered a sufficient deterrent?

### Spec-hygiene issues

- **§1.3, `MAX_TRANSACTIONS_PER_INCLUSION_LIST = 1`** is
  marked `# TODO: Placeholder` in `beacon-chain.md` and
  contradicts the 8 KiB per-IL byte cap quoted by the EIP body.
- **§2.1, `validate_inclusion_lists` has no body** in
  `fork-choice.md` (literally `...`). The only normative
  description is a one-sentence docstring that leaves three
  substantive questions open (ordering, fullness semantics,
  deduplication).
- **§1.2, `parent_hash` and `parent_root`** are referenced in
  `validator.md` but are not fields of the `InclusionList`
  container in `beacon-chain.md`.

### Disclosed model limitations

- **§2.5**, sequential dependence between IL transactions is
  not captured by the current `CompliantWith` predicate.
- **§2.6**, equivocator detection (`on_inclusion_list`) is not
  modelled; `state.equivocators` is taken as input.

The remaining items in §1 and §2 are smaller observations
useful as cross-references but not load-bearing for the safety
argument.

---

## 1. Discrepancies between spec sources

### 1.1 IL committee size

**Verification status:** CONFIRMED AGAINST SPEC.
**Engagement:** OPEN.

The EIP-7805 EIP table says:

> `IL_COMMITTEE_SIZE | uint64(2**4)` (=16)

Several mainstream write-ups of the Hegotá fork have used "17
validators." Two readings of the discrepancy are possible:
(a) a writer counting the slot's proposer alongside the 16 IL
committee members and arriving at 17, or (b) an off-by-one.
Either way, the authoritative `IL_COMMITTEE_SIZE` constant in
both the EIP table and `beacon-chain.md` is **16**.

The Lean formalization treats committee size as an unspecified
`Nat` rather than hard-coding 16, so it is unaffected. The
finding is included for the benefit of readers of informal
write-ups who may be uncertain which figure to trust.

### 1.2 `parent_hash` / `parent_root` on `InclusionList`

**Verification status:** CONFIRMED AGAINST SPEC.
**Engagement:** OPEN.

`validator.md` describes constructing a signed inclusion list as
follows:

> - Set `inclusion_list.parent_hash` to the block hash of the fork
>   choice head.
> - Set `inclusion_list.parent_root` to the block root of the fork
>   choice head.

But the `InclusionList` container defined in `beacon-chain.md` has
no `parent_hash` or `parent_root` field:

```python
class InclusionList(Container):
    slot: Slot
    validator_index: ValidatorIndex
    inclusion_list_committee_root: Root
    transactions: List[Transaction, MAX_TRANSACTIONS_PER_INCLUSION_LIST]
```

This is either (a) an oversight in `validator.md` (the validator
was supposed to use the parent fields locally to construct
`transactions` but not store them in the container), or (b) a
planned extension not yet reflected in `beacon-chain.md`. Either
way it is a real gap a reviewer should resolve before the spec
stabilises.

The Lean formalization follows `beacon-chain.md` and omits these
fields. Adding them later is a non-breaking change: the safety
theorem does not reference them.

### 1.3 `MAX_TRANSACTIONS_PER_INCLUSION_LIST = 1` (placeholder)

**Verification status:** CONFIRMED AGAINST SPEC.
**Engagement:** OPEN.

`beacon-chain.md` sets:

```
MAX_TRANSACTIONS_PER_INCLUSION_LIST | uint64(1) # TODO: Placeholder
```

A maximum of _one transaction per IL_ is wildly inconsistent with
the 8 KiB per-IL byte cap quoted by the EIP-7805 EIP text:

> `MAX_BYTES_PER_INCLUSION_LIST = uint64(2**13)` (=8192)

8 KiB is roughly enough for ~50 small transactions; capping list
length at 1 would undercut that completely. The `1` is clearly a
placeholder, but EIP readers may take it at face value.

The Lean model uses an unbounded `List Transaction`, so the choice
of cap does not affect the proof. It does affect the
_interpretation_ of the censorship-resistance guarantee: if each
IL holds only one transaction, then the "honest 1-of-N" guarantee
in any given slot is about a single transaction's-worth of bytes,
not about an arbitrary 8 KiB payload.

**Cross-reference:** §2.1 below depends on this placeholder being
resolved before the body of `validate_inclusion_lists` can be
written precisely; the loop in that function is over the per-slot
union of IL transactions, whose maximum size is
`MAX_TRANSACTIONS_PER_INCLUSION_LIST * IL_COMMITTEE_SIZE`.

### 1.4 View freeze deadline: 8 s vs 9 s

**Verification status:** CONFIRMED AGAINST SPEC.
**Engagement:** OPEN.

The EIP introductory prose mentions IL gossip "between t=0 and
t=8s", but the actual fork-choice constant is **9 seconds**:

```
VIEW_FREEZE_DEADLINE | uint64(9) | seconds
```

The 8-second figure may refer to the moment honest committee
members **stop building** their ILs, with one extra second budgeted
for propagation before the freeze. The Lean model abstracts timing
entirely (see §4.2 below); this discrepancy only affects which
network conditions cause an IL to be ignored.

---

## 2. Spec ambiguities surfaced by the formalization

### 2.1 `validate_inclusion_lists` is `...` (unimplemented)

**Verification status:** CONFIRMED AGAINST SPEC.
**Engagement:** OPEN.

In `fork-choice.md`:

```python
def validate_inclusion_lists(store, inclusion_list_transactions, execution_payload):
    """ ... """
    ...
```

The body is literally `...`. The only normative description is the
docstring:

> "verify if the `execution_payload` satisfies
> `inclusion_list_transactions` validity conditions either when all
> transactions are present in payload or when any missing
> transactions are found to be invalid when appended to the end of
> the payload unless the block is full."

A close reading raises three substantive questions the
formalization had to commit to a position on:

1. **Order sensitivity.** "When appended to the end" suggests a
   specific test ordering, but if there are multiple missing IL
   transactions and they can affect each other's validity (one's
   execution making the next valid, as discussed in EIP-7805
   §"Payload Construction"), the order in which they are tested
   matters. Should the attester try every permutation? Just one?
   Use the IL's published order? The spec is silent.

    The Lean model resolves this by abstracting the
    `CanAppend tx b` predicate to a single per-(tx, block) judgement.
    This effectively says "there is _some_ attempt-to-append" that
    succeeds or fails, without committing to an ordering. See §2.5
    for the resulting model limitation.

2. **"The block is full" semantics.** Does "full" mean _literally_
   at the gas limit, or _too full to fit even the smallest possible
   tx_? The two notions diverge for blocks with leftover gas less
   than 21 000. EIP-7805 §"Execution Layer" point 2 implies the
   second reading (`if T.gas > gas_left`, skip), but the prose uses
   the unqualified word "full".

    We treat fullness as an abstract `Block → Prop`, leaving the
    implementer free to choose either reading.

3. **Across-IL deduplication.** Two committee members can list the
   same transaction. If the proposer includes it once, both ILs
   are satisfied. Both `validate_inclusion_lists` and the
   fork-choice store treat ILs as a flat per-slot set; nothing in
   the spec says the proposer must include duplicates. The Lean
   model gets this right because compliance is "for every IL, for
   every tx, the transaction is present _or_ excused"; present
   once is enough.

### 2.2 Network adversary against IL propagation

**Verification status:** OPEN QUESTION.
**Engagement:** OPEN.

An honest committee member is supposed to publish an IL by the
inclusion-list cutoff, but the network is asynchronous.
`on_inclusion_list` rejects ILs that arrive after
`VIEW_FREEZE_DEADLINE`. If an attester never receives an IL from a
particular committee member, the attester treats that member as
having published nothing.

This is operationally fine, but it weakens the formal guarantee in
a subtle way. The "1-of-N honesty" property the EIP advertises
holds only _for IL committee members whose IL reached enough
attesters before the freeze_. An adversary that can selectively
delay one honest committee member's IL effectively reduces the
committee size by 1 from the perspective of those attesters.

The Lean model captures this by demanding `il ∈ state.stored_ils`.
If the IL is not in the store, the safety theorem says nothing.
The _precondition_ of the theorem already encodes the attacker's
opportunity space: they win by stopping ILs from entering the
store.

This is the strongest open question: how robust is FOCIL under
network-level adversaries? The formalization doesn't answer it; it
makes it crisp.

### 2.3 Adversarial validity changes

**Verification status:** CONFIRMED AGAINST SPEC (concrete
attack formalized).
**Engagement:** OPEN (slashing/mitigation policy is the
unresolved question).

Conditional inclusion is the most subtle part of FOCIL. A proposer
may legitimately omit IL transaction `tx` if `tx` is no longer
valid at block-production time. A _malicious_ proposer would like
to arrange for `tx` to become invalid right before they build the
block.

Concrete attack vectors EIP-7805 does not (yet) explicitly rule
out:

- **Front-running with a no-op.** The proposer or a colluding
  party submits a transaction that bumps `sender(tx)`'s nonce
  without changing `tx`'s economic effect. When the proposer goes
  to build the block, `tx` has the wrong nonce and is "invalid".
- **Balance drain.** A colluding party sends a balance-changing
  transaction that leaves `sender(tx)` unable to pay `tx`'s base
  fee.
- **AA / 7702 interactions.** An EOA's authorisation can be
  revoked, rendering an IL'd 7702 transaction invalid.

In each case, the proposer can plausibly claim
conditional-inclusion exemption for a transaction the IL committee
believed was includable. EIP-7805 §"Payload Construction" addresses
the _efficiency_ of compliance checking but does not address
whether this manipulation is itself a censorship attack.

The Lean formalization captures this issue formally on two
levels:

1. The main safety theorems take `h_can_append` as a hypothesis
   universally quantified over `CanAppend`. Under any concrete
   realization, the hypothesis can be made false by an
   adversary who picks `b` adversarially. The safety theorem
   then says nothing.

2. `Focil/AccountState.lean` instantiates one such concrete
   realization (a nonce-only account-state model) and proves
   the front-running attack as a theorem:

    ```lean
    theorem front_running_breaks_appendability
        (initial : AccountState) (b : Block)
        (tx_il tx_evil : Transaction)
        (h_same_sender    : tx_evil.sender = tx_il.sender)
        (h_il_appendable  : canAppendToBlock initial b tx_il)
        (h_evil_appendable: canAppendToBlock initial b tx_evil) :
        ¬ canAppendToBlock initial
            { b with transactions := b.transactions ++ [tx_evil] }
            tx_il
    ```

    Read: if the IL transaction `tx_il` is appendable to `b`,
    and a colluding transaction `tx_evil` sharing `tx_il`'s
    sender is also appendable, then extending `b` with `tx_evil`
    makes `tx_il` no longer appendable. (Note that the
    same-sender hypothesis combined with both being appendable
    to the same state already forces nonce collision; we do not
    need to assume same-nonce explicitly.)

    Tests/Examples.lean Scenario 13 fires this theorem on
    concrete data: `tx_il` is the IL transaction at sender 100,
    nonce 0; `tx_evil` is a colluding tx sharing the same
    sender; the proposer extends an empty block with `tx_evil`
    and `tx_il` becomes non-appendable.

The cost of this attack is one gas-fee payment for `tx_evil`,
with no slashing penalty (the attacker is not equivocating;
they are just transacting). The protocol-level question for
the EIP authors:

- Should the EIP commit to a per-account-state abstraction
  that the proposer must respect (e.g., snapshot the
  pre-state before any transaction the proposer submits in
  the same slot)? Or
- Is the cost of broadcasting a zero-effect transaction
  considered prohibitive enough that the attack is not worth
  preventing?

**Cross-reference:** §4.3 explains why `CanAppend` in the main
safety chain is opaque; §2.5 explains why even a refined
`CanAppend` would not, on its own, recover sequential
dependence between IL transactions.

### 2.4 Equivocation as a censorship channel

**Verification status:** OPEN QUESTION.
**Engagement:** OPEN.

When two distinct ILs from the same committee member are observed,
the spec says: **ignore all ILs from that member**, including the
member's first, presumably honest, IL.

This is correct from a fork-choice safety perspective (you cannot
trust a Byzantine signer), but it is a free censorship channel for
an adversary who controls one IL committee seat:

- Sign an honest IL that includes `tx`.
- Sign a second IL that omits `tx`.
- Gossip both in opposite halves of the network.
- Outcome: the entire committee member's contribution is voided,
  so `tx` is not protected by _that_ member.

If `tx` was only listed by one committee member, the adversary has
successfully censored it at the cost of one validator's slashing
risk (if any). The EIP text mentions equivocation evidence is
_recorded_ but does not say it is _slashed_.

The Lean model captures this exactly: the predicate
`IsConsidered state il` evaluates to false once the author is in
`state.equivocators`, so the safety theorem's hypothesis fails for
`il`. The theorem still goes through for any _other_ honest IL
that listed `tx`, recovering the "1-of-N honesty" guarantee, but
only as long as `N ≥ 2` for that particular transaction.

### 2.5 Sequential dependence in the compliance check (model limitation)

**Verification status:** MODEL LIMITATION DISCLOSED.
**Engagement:** RESOLVED IN FORMALIZATION.

EIP-7805 §"Payload Construction" explicitly notes that an IL
transaction can become valid _because_ an earlier IL transaction
was appended. Concretely:

> "given a set of n IL transactions, one might end up needing to
> do n + (n-1) + (n-2) + … validity checks ... For example, the
> nth tx might be valid while all others are not, but its
> execution sends balance to the sender of the (n-1)th tx, making
> it valid, and in turn, the (n-1)th sends balance to the sender
> of the (n-2)th tx, etc."

The Lean predicate `CompliantWith` quantifies over `tx ∈
il.transactions` _independently_: each per-transaction obligation
is `tx ∈ b.transactions ∨ ¬ CanAppend tx b ∨ full b`, where
`CanAppend tx b` depends only on the final state of `b`. There is
no notion of "tentative state after appending some prefix of the
IL list."

**What this means:** a sequence of IL transactions that is
_jointly_ appendable, but where no single transaction is
individually appendable to `b` as it stands, is not modelled
correctly by `CompliantWith`. The Lean predicate would mark such a
sequence as compliantly omittable (each tx is excused by `¬
CanAppend tx b`), even though the spec's intent is that the
proposer should have appended them in the right order.

The fix is a refined compliance predicate that takes the IL
transactions in order and threads a hypothetical post-state
through the appendability check. This is non-trivial because the
spec itself does not specify the order. The honest description is
that the Lean model captures the _necessary_ condition for
compliance but a _sufficient_ one only when sequential dependence
is absent.

**Cross-reference:** §1.3 (the placeholder `1` makes this issue
moot in current spec drafts because there is at most one IL tx per
list); §2.1 (the spec does not specify an ordering).

### 2.6 Equivocator detection is not modelled (model limitation)

**Verification status:** MODEL LIMITATION DISCLOSED.
**Engagement:** RESOLVED IN FORMALIZATION.

The fork-choice rule's `on_inclusion_list` actively detects
equivocation: when a second distinct IL arrives from the same
validator, the validator is added to
`inclusion_list_equivocators`. The Lean model takes
`state.equivocators` as a given input and does not model the
detection process.

This means the safety theorem says nothing about whether
`state.equivocators` contains the correct set of equivocators at
attestation time. If an honest implementation has buggy
equivocation detection (say, fails to add a true equivocator to
the set), the Lean theorem still holds trivially. It just
doesn't constrain anything useful for that validator.

The right way to read the theorem is: _given_ a faithful execution
of `on_inclusion_list` that has correctly populated
`state.stored_ils` and `state.equivocators` from the wire-level IL
gossip, the safety property follows.

**Cross-reference:** §3 (this is the "honesty assumption" boundary
between IL-construction and fork-choice enforcement).

### 2.7 The honest-attester invariant must be relativized to the attester's store

**Verification status:** CONFIRMED AGAINST SPEC.
**Engagement:** RESOLVED IN FORMALIZATION.

EIP-7805's fork-choice changes specify, in English, that
"attesters only vote for the proposer's block if it includes
transactions from all stored ILs." The natural informal reading
of this rule, paraphrased: _honest attesters refuse to vote for
FOCIL-non-compliant blocks_.

This informal statement is ambiguous in a way that becomes
visible only when one tries to write it as a formal predicate.
Compliance is defined relative to a fork-choice store (the set
of stored ILs determines what the block is being measured
against). So the informal rule has two readings:

1. **Globally quantified.** _For every conceivable fork-choice
   store, honest attesters who voted for `b` make `b` compliant
   against that store._
2. **Locally relativized.** _Honest attesters who voted for `b`
   make `b` compliant against the fork-choice store they
   themselves observed at attestation time._

These readings are not equivalent. Reading (1) is strictly
stronger and is what a careful formalization would write down
first, since it does not require any auxiliary notion of
"the store the attester observed."

**Reading (1) is unsatisfiable non-vacuously.** Once `CanAppend`
is opaque (§4.3), there is no concrete `(b, attester)` pair
where a non-vacuous proof of (1) is possible. To see this: pick
any transaction `tx` not in `b.transactions`, and consider the
adversarial store whose only stored IL contains `tx`. The
compliance obligation for that store reduces to
`tx ∈ b.transactions ∨ ¬ CanAppend tx b ∨ full b`, none of
whose disjuncts is discharge-able for an arbitrary `b`. The
only escape is to make the antecedent (the attester's vote)
unsatisfiable, which empties the rule of content.

**Implication for the spec.** The informal English sentence is
sensible only under reading (2). Any informal argument that
implicitly invokes reading (1), for instance by composing
"honest attesters refuse non-compliant blocks" across attesters
with different fork-choice store snapshots, is over-claiming.
This does not affect the EIP's safety claim _as the EIP states
it_ (under reading (2), which is what real attesters actually
do). It does mean that any informal proof sketch that treats
the rule as a single global invariant has a hidden assumption
about which store is being referred to.

**How the formalization captures this.** The `ForkChoice`
structure in `Focil/ForkChoice.lean` bundles the attester's
store snapshot (`state`) and fullness model (`full`) as
_fields_, fixing reading (2) at the type level. The soundness
obligation reads:

```lean
honest_attester_compliance :
    ∀ (b : Block) (v : ValidatorIndex),
      IsHonest v → Voted v b →
      FocilCompliant full b state
```

where `state` and `full` are the structure's own fields. An
attester is, in this formalization, _defined by_ the store they
observed. Cross-attester reasoning (e.g., counting honest votes
across validators with different stores) becomes impossible to
state at this level of abstraction without explicit
quantification.

**Why this is a finding rather than a refactor.** The naive
formalization that takes reading (1) does not type-check against
any non-trivial concrete fork-choice rule. A researcher who
writes down the natural English-prose obligation in Lean and
then attempts to provide a witness instance is forced to
discover this. The formalization makes precise a subtle
implicit assumption in the spec text, which is one of the
primary reasons to do this kind of work. See the `ForkChoice`
docstring in `Focil/ForkChoice.lean` for the in-source
explanation of the design choice.

The corrected formalization admits a non-vacuous concrete
instance, `threeValidatorForkChoice` in `Tests/Examples.lean`,
which Scenarios 6–8 and 11 use to fire the safety theorems on a
real (if small) scenario.

---

## 3. Quorum and honesty thresholds

**Verification status:** OPEN QUESTION.
**Engagement:** RESOLVED IN FORMALIZATION.

The EIP's claim "FOCIL requires only a 1-out-of-N honesty
assumption from IL committee members" is, strictly speaking, true
only of the IL _construction_ layer. The fork-choice enforcement
still relies on the broader >2/3 honest supermajority assumption
from Ethereum PoS: attesters must in aggregate have a quorum of
honest validators willing to refuse non-compliant blocks.

The Lean formalization splits these two assumptions:

- IL honesty is captured by `il ∈ state.stored_ils ∧ IsConsidered
state il`. One non-equivocating IL anywhere in the store
  suffices.
- Attester honesty is captured by `ForkChoice.HasQuorum b → ∃ v,
ForkChoice.IsHonest v ∧ ForkChoice.Voted v b`. This is _much_
  weaker than ">2/3 honest"; it says only that "having a quorum"
  implies "at least one honest voter exists".

The latter is intentionally weak. The safety theorem's
contradiction only needs _one_ honest dissenter for any
non-compliant block to fail to accumulate a fully-honest quorum.
Stronger thresholds (1/3 dishonest tolerance, etc.) would be
appropriate for liveness arguments, not for censorship-resistance
safety.

This is one of the more interesting structural facts the
formalization makes precise: **FOCIL censorship resistance does
not require a 2/3 honest supermajority among attesters**. It
requires that "becoming canonical" entails "having at least one
honest vote", which is implied by but strictly weaker than the
full BFT assumption.

**Caveat:** the "1 honest voter exists" assumption is a propositional
field of the `ForkChoice` structure (§5 below). The formalization
does not derive it from a more primitive model of attester
behaviour and slot-by-slot vote tallying. The safety theorem
should be read as "censorship resistance reduces to two
specifically stated properties of the underlying fork-choice
rule," not "censorship resistance follows from PoS first
principles."

---

## 4. Abstraction choices

### 4.1 Why no Mathlib?

**Verification status:** MODEL LIMITATION DISCLOSED.

We considered importing Mathlib for `Finset` and richer list
lemmas. We decided against it because:

1. The safety proof needs only `List` membership.
2. Mathlib pulls a multi-minute build that would make every
   reviewer's first encounter with the repo a coffee break.
3. A future refinement that _does_ need Finset can add Mathlib
   without breaking any existing definitions.

### 4.2 Why no timing model?

**Verification status:** MODEL LIMITATION DISCLOSED.

The protocol is intrinsically time-dependent (`t=0`, `t=8s`,
`t=9s`, `t=11s`, etc.). We folded all timing into a single binary
fact: "the IL is in the store" (`il ∈ state.stored_ils`).

This is an aggressive abstraction. Justification:

- The fork-choice rule never reads the wall-clock time; it reads
  the store. Anything that does not appear in the store at the
  time of attestation is irrelevant to compliance.
- Time only matters for the _transitions_: when does an IL enter
  the store, when do we stop accepting new ones, when do we
  discard old ones. These are pre-conditions on
  `state.stored_ils`, not part of the fork-choice rule itself.

A future extension could refine `FocilState` to track timestamps
and prove the discrete transition rules; that is genuine extra
protocol modelling, not a missing piece of the safety argument.

### 4.3 Why is `CanAppend` opaque?

**Verification status:** MODEL LIMITATION DISCLOSED.

`CanAppend tx b` is the formal counterpart of "the EVM can validly
execute `tx` after `b`". Reproducing the EVM is far out of scope.
The opacity makes the safety theorem read as:

> _Modulo a faithful implementation of EVM-validity_, FOCIL's
> fork-choice rule guarantees censorship resistance.

Refining `CanAppend` to an explicit semantics (e.g., a per-account
nonce/balance abstraction in the spirit of `consensus-specs`'
"Payload Construction" section) would let us prove additional
properties; for example, that conditional inclusion does not
introduce false positives. This is the most natural next step.

**Cross-reference:** §2.3 (refining `CanAppend` is also the entry
point to a formal threat model for adversarial validity changes);
§2.5 (sequential dependence is a structural change that goes
_beyond_ refining `CanAppend`); §2.7 (the opacity of `CanAppend`
is what forced the per-attester store relativisation).

---

## 5. Where the formalization is conditional

The safety theorems are stated at two levels:

### 5.1 The headline 1-of-N theorem and its building blocks

`Focil.focil_one_of_n_protection`,
`Focil.focil_censorship_resistance`,
`Focil.censoring_block_not_canonical`, and
`Focil.canonical_implies_compliant` (all in `Focil/Safety.lean`
and `Focil/ForkChoice.lean`) prove _implication_: given two
propositional obligations of the `ForkChoice` structure
(`quorum_has_honest_voter` and `honest_attester_compliance`),
censorship resistance follows. The Lean kernel reports that
all four theorems depend on **zero** kernel axioms.

These obligations are properties any concrete `ForkChoice`
value must discharge. `Tests/Examples.lean` ships two
hand-crafted instances:

- **`emptyForkChoice`** discharges both vacuously by setting
  `HasQuorum` and `Voted` to constantly-false predicates.
  Useful only as a structural sanity check.

- **`threeValidatorForkChoice`** is a non-vacuous 3-validator
  scenario where both obligations are discharged by genuine
  case analysis. Scenarios 6–11 fire the safety theorems
  against this instance.

### 5.2 The PoS-derived end-to-end theorem

`Focil.focil_pos_derived_safety` in `Focil/StakeModel.lean`
discharges _both_ `ForkChoice` obligations from a more
primitive ">2/3 honest validators" assumption, the same
assumption that underlies every other Ethereum PoS safety
result.

The construction uses two structures:

- `StakeModel`, carrying a per-validator honesty predicate
  and the strict-supermajority assumption
  `3 * |honest| > 2 * numValidators`.
- `AttesterRun s`, carrying the per-attestation context (store
  snapshot, fullness model, vote relation) and the per-attester
  rule "honest validators only vote for FOCIL-compliant
  blocks".

A constructive function `AttesterRun.toForkChoice` packages
these into a `ForkChoice` value, deriving
`quorum_has_honest_voter` from a counting-pigeonhole argument
(if both honest stake and quorum stake exceed 2/3, the
intersection is non-empty) and `honest_attester_compliance`
directly from the per-attester rule.

The end-to-end safety theorem `focil_pos_derived_safety`
composes this with `focil_one_of_n_protection` to give:

> Under Ethereum's standard >2/3 honest-validator assumption
> and the per-attester compliance rule, any non-equivocating
> IL listing `tx` forces `tx` into any canonical block
> (modulo invalidity and block fullness).

`Tests/Examples.lean` Scenario 12 fires this theorem against a
concrete 4-validator scenario.

### 5.3 Axiom dependencies

The four theorems in §5.1 depend on zero kernel axioms.
`AttesterRun.toForkChoice` and `focil_pos_derived_safety` in
§5.2 depend on `propext` and `Quot.sound` (transitively, via
the counting argument's use of `omega` and `simp` on
`List.length` lemmas). Both are foundational kernel axioms
that ship with every Lean installation; neither gives
classical logic. `Classical.choice` and `sorryAx` are not
used anywhere in the project.

### 5.4 Remaining axioms-of-faith

After the §5.2 derivation, the only remaining substantive
assumptions are:

- **Ethereum's standard ">2/3 honest" supermajority**, encoded
  as `StakeModel.honest_majority`. This is the same assumption
  underlying every other Ethereum PoS safety result.
- **The per-attester compliance rule**, encoded as
  `AttesterRun.honest_rule`. This is the normative rule
  EIP-7805 specifies for honest attester behaviour.
- **Faithfulness of the abstract `CanAppend` predicate**, the
  formal counterpart of "EVM-valid appendability." The theorem
  is universally quantified over `CanAppend`; a real claim
  against a real Ethereum implementation requires a faithful
  concrete `CanAppend`. See §4.3.
- **Faithful population of `state.stored_ils` and
  `state.equivocators`** by an honest execution of
  `on_inclusion_list`. See §2.6.

---

## 6. What this formalization does _not_ cover

To set expectations precisely:

- **No EVM model.** Validity is opaque (`CanAppend`).
- **No proof of liveness or progress.** We prove non-canonicality
  of bad blocks; we do not prove a compliant block always exists.
- **No IL gossip / network model.** Network adversaries that
  delay IL propagation are not modelled; their attack surface is
  captured by the precondition `il ∈ state.stored_ils`.
- **No cross-slot reasoning.** The safety theorems talk about
  a single block at a single slot. Long-range censorship
  across many slots is not modelled.
- **No stake-weighted PoS.** `StakeModel.honest_majority`
  treats each validator as one stake unit. A weighted variant
  would multiply each `filter` count by `weight` and adjust
  the supermajority condition accordingly. The counting
  argument generalises but is left as follow-on work.
- **No slashing or rewards.** Economic incentives, attester
  rewards, and the underlying BFT proof of `>2/3 honest stake`
  itself are absent.
- **No model of equivocator detection.** `state.equivocators`
  is taken as input (§2.6).
- **No model of sequential validity dependence among IL
  transactions.** `CompliantWith` reads `CanAppend` against
  the block as proposed, not against a tentative post-state
  (§2.5).

Each of these is a candidate for a follow-on formalisation.

---

## 7. Summary

The contribution of this repository is:

1. A **type-checked** Lean 4 model of FOCIL's data structures
   and compliance rule, faithful to `consensus-specs`
   `eip7805/` modulo the simplifications disclosed in §2.5,
   §2.6, §4.1–§4.3, and §6.
2. A **type-checked** end-to-end PoS-derived safety theorem,
   `Focil.focil_pos_derived_safety`, deriving FOCIL's 1-of-N
   censorship-resistance guarantee from Ethereum's standard
   ">2/3 honest validators" assumption. No `ForkChoice`
   postulates remain; both structural obligations are derived
   via the counting-pigeonhole argument in
   `Focil/StakeModel.lean`.
3. A **type-checked** headline 1-of-N theorem,
   `Focil.focil_one_of_n_protection`, that states the same
   guarantee against an abstract `ForkChoice`. The
   PoS-derived theorem in (2) is a corollary.
4. A **per-IL building block**,
   `Focil.focil_censorship_resistance`, which takes the
   witness IL as an explicit parameter. The 1-of-N theorem in
   (3) is a thin existential-elimination corollary.
5. A **completed proof** of all four theorems plus the
   contrapositive `Focil.censoring_block_not_canonical`. No
   `sorry`. The Lean kernel reports that the four pure safety
   theorems depend on **zero** kernel axioms; the PoS-derived
   theorem additionally depends on `propext` and `Quot.sound`
   (used by the counting argument). `Classical.choice` and
   `sorryAx` are not used anywhere.
6. A **non-vacuous concrete `ForkChoice` instance**
   (`threeValidatorForkChoice`) and a **PoS-derived `StakeModel`
   plus `AttesterRun`** (`stakeModel4v`/`attesterRun4v`),
   demonstrating each theorem firing on a real scenario.
   Building the abstract `ForkChoice` instance surfaced
   finding §2.7: the honest-attester invariant must be
   relativized to the attester's local store, not universally
   quantified.
7. A **nonce-only account-state model**
   (`Focil/AccountState.lean`) and a theorem
   `front_running_breaks_appendability` that formalizes the
   adversarial-validity attack from §2.3 on a concrete
   realization of EVM-validity. Scenario 13 fires the attack
   on concrete data. This is a _companion_ result to the main
   safety theorems, not a refinement of them.
8. This `FINDINGS.md`, with **three substantive observations**
   (§2.3, §2.4, and §2.7) that the formalization surfaced,
   plus spec-hygiene issues (§1.2, §1.3, §2.1) and disclosed
   model limitations (§2.5, §2.6). Smaller cross-references
   in §1.1, §1.4, and §2.2 round out the document.

What the safety theorems do **not** prove:

- They do not prove correctness against a real EVM.
  `CanAppend` is opaque.
- They do not prove correctness in the presence of sequential
  validity dependence between IL transactions (§2.5).
- They do not derive the >2/3 honest-validator assumption
  itself; that is the standard Ethereum PoS axiom-of-faith
  the entire ecosystem rests on.

These are the natural seams along which the formalisation should
grow. Each is a concrete invitation for follow-on work; see
`CONTRIBUTING.md`.
