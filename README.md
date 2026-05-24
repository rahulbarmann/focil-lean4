# focil-lean4

[![CI](https://github.com/rahulbarmann/focil-lean4/actions/workflows/ci.yml/badge.svg)](https://github.com/rahulbarmann/focil-lean4/actions/workflows/ci.yml)
[![License: CC0-1.0](https://img.shields.io/badge/License-CC0_1.0-blue.svg)](LICENSE)
[![Lean](https://img.shields.io/badge/Lean-4.29.1-blueviolet)](lean-toolchain)

A Lean 4 formalization of FOCIL, the consensus-layer
censorship-resistance mechanism specified in
[EIP-7805](https://eips.ethereum.org/EIPS/eip-7805) (the headline
feature of Ethereum's late-2026 Hegotá hard fork). Proves that
under Ethereum's standard ">2/3 honest validators" assumption, a
transaction listed in a stored, non-equivocating inclusion list
cannot be excluded from a canonical block (modulo invalidity and
block fullness). Ships with both an abstract version of the
theorem and a fully concrete end-to-end version against a
nonce-only account-state model, with no opaque predicates
remaining. Build is green on Lean 4.29.1; the safety proofs are
`sorry`-free, and the five pure safety theorems depend on zero
kernel axioms.

---

## Quick start

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
lake build
```

The toolchain is pinned by `lean-toolchain`; `elan` will fetch
the right Lean version automatically. There are no external Lean
dependencies.

---

## What is proven

**End-to-end PoS-derived theorem against a concrete
EVM-validity model**
(`Focil.focil_concrete_pos_safety`, in
[`Focil/EndToEnd.lean`](Focil/EndToEnd.lean)):

> Fix any `StakeModel` with strictly more than 2/3 honest
> validators (the standard Ethereum PoS supermajority
> assumption), any `AttesterRun` over that model whose
> `canAppend` is pinned to a concrete account-state predicate,
> and an `initial : AccountState` representing the genesis
> account state. For any block `b` and transaction `tx`: if
> some inclusion list stored in `r.state` and not in
> `r.state.equivocators` contains `tx`, the block has
> accumulated a strict 2/3 quorum of votes, `tx`'s nonce
> matches its sender's next-expected nonce in `b`'s
> post-state, and `b` is not full, then
> `tx ∈ b.transactions`.

This is the marquee result of the project. No `ForkChoice`
postulates remain. No opaque predicates remain. The validity
predicate is the cheap nonce proxy described by EIP-7805 lead
author Thomas Thiery in his
[Mar 16 2026 ethereum-magicians post](https://ethereum-magicians.org/t/focil-native-account-abstraction/27999)
on FOCIL handshake Native Account Abstraction:
"This proxy is cheap... and works well for EOAs and EIP-7702."
The same module also exposes the builder-side contrapositive
`Focil.focil_concrete_pos_censoring_block_not_canonical`: a
block omitting a nonce-valid IL transaction cannot be the
canonical chain head.

The only remaining axioms-of-faith are Ethereum's standard
">2/3 honest" assumption (encoded as `s.honest_majority`) and
the spec's "honest attesters refuse non-compliant blocks" rule
(encoded as `r.honest_rule`).

**End-to-end PoS-derived theorem (abstract validity)**
(`Focil.focil_pos_derived_safety`, in
[`Focil/StakeModel.lean`](Focil/StakeModel.lean)):

The same end-to-end claim against an abstract opaque validity
predicate, for callers who do not wish to commit to the
concrete account-state model. The concrete theorem is a
specialization of this one.

**Headline 1-of-N theorem (parameterised over validity)**
(`Focil.focil_one_of_n_protection`,
in [`Focil/Safety.lean`](Focil/Safety.lean)):

> Fix any `ForkChoice` value `fc`. For any block `b` and
> transaction `tx`: if some inclusion list in
> `fc.state.stored_ils` whose author is not in
> `fc.state.equivocators` contains `tx`, `tx` is appendable
> under `fc.canAppend`, `b` is not full, and `b` is canonical
> under `fc`, then `tx ∈ b.transactions`.

This is the formal counterpart of EIP-7805's marquee 1-of-N
honesty claim against an abstract `ForkChoice`: it suffices
that _at least one_ non-equivocating IL committee member listed
`tx`. Adversaries controlling some committee seats and
equivocating others do not defeat the guarantee, as long as at
least one seat publishes a non-equivocating IL containing
`tx`. The end-to-end PoS-derived theorems above are corollaries
(instantiate `fc` with `AttesterRun.toForkChoice`).

**Per-IL building block**
(`Focil.focil_censorship_resistance`): same statement but takes
the witness IL as an explicit parameter. The 1-of-N theorem is
a thin existential-elimination corollary.

**Builder-side contrapositive**
(`Focil.censoring_block_not_canonical`): a block that omits an
"appendable, listed, non-equivocating, room-available"
transaction cannot become canonical. Useful as a builder-side
incentive statement.

**Adversarial-validity attack, formalized**
(`Focil.front_running_breaks_appendability`, in
[`Focil/AccountState.lean`](Focil/AccountState.lean)). One
specific way the `CanAppend` hypothesis can be defeated by an
adversary: a colluding party submits a transaction sharing an
IL transaction's sender; once the proposer appends it, the IL
transaction's nonce is stale and it is no longer appendable.
The theorem captures this attack at the level of the
appendability predicate, on a nonce-only account-state
realization. This is _separate from_ the main safety theorem;
the main theorem still quantifies over arbitrary `CanAppend`.
What this companion theorem formalizes is one specific
realization of the threat model in FINDINGS.md §2.3.

**The proof depends on:**

1. The validity predicate, parameterised by the safety chain
   so that callers can plug in either an abstract opaque
   predicate or a concrete EVM-validity model. The default
   abstract predicate `CanAppend : Transaction → Block → Prop`
   is opaque; the concrete realization
   [`Focil.canAppendToBlock`](Focil/AccountState.lean) is a
   nonce-only account-state model. The end-to-end concrete
   theorem is universally quantified over the choice of
   `initial : AccountState`.
2. The "honest attesters refuse non-compliant blocks" rule is
   encoded as the `honest_rule` field of `AttesterRun`. This
   is the per-attester rule EIP-7805 specifies as the
   normative behaviour of a correct validator.
3. The ">2/3 honest validators" assumption is encoded as the
   `honest_majority` field of `StakeModel`. This is the
   standard PoS safety assumption underlying every other
   Ethereum consensus result.

The repository ships four demonstrations:

- `Tests.Examples.emptyForkChoice` discharges the abstract
  `ForkChoice` obligations vacuously (sanity check only).
- `Tests.Examples.threeValidatorForkChoice` is a hand-crafted
  3-validator scenario; Scenarios 6–11 fire the headline
  theorem against it.
- `Tests.Examples.attesterRun4v` builds a 4-validator
  `StakeModel` and `AttesterRun` from scratch and derives
  everything via `AttesterRun.toForkChoice`. Scenario 12 fires
  `focil_pos_derived_safety` against it with no `ForkChoice`
  postulates remaining.
- `Tests.Examples.attesterRun4vConcrete` pins `canAppend` to
  the concrete account-state predicate. Scenario 14 fires
  `focil_concrete_pos_censoring_block_not_canonical` against
  it: every hypothesis is decidable on concrete data, no
  opaque predicate appears anywhere, and the conclusion (a
  block omitting a nonce-valid IL transaction cannot be
  canonical) is forced as a Lean kernel-checked consequence.

**The architectural claim** captured by the proof structure:
FOCIL censorship resistance is a structural consequence of
canonicality _relative to_ a fork-choice rule that filters
non-compliant blocks. The proof of `canonical_implies_compliant`
walks the chain canonical → quorum → honest voter → compliance
directly. See [`docs/DESIGN.md`](docs/DESIGN.md) for the full
architectural rationale.

---

## What is _not_ proven

This formalization is deliberately scoped. It does **not**
model:

- A full EVM. The concrete EVM-validity layer covers
  per-sender nonces only (matching the EOA proxy described
  by EIP-7805's lead author). Balance-aware validity,
  EIP-7702 delegations, and EIP-8141 Frame Transactions are
  out of scope. See FINDINGS.md §2.3 and §4.3 for what this
  excludes.
- Liveness or progress. We prove non-canonicality of bad
  blocks but not the existence of good ones.
- IL gossip or the network layer. Network-level censorship
  attacks are captured only as preconditions of the theorem.
- Sequential validity dependence between IL transactions. The
  EIP's §"Payload Construction" notes that IL transactions can
  affect each other's validity; the Lean `CompliantWith`
  predicate quantifies per-transaction independently and does
  not capture this. See
  [FINDINGS.md §2.5](FINDINGS.md#25-sequential-dependence-in-the-compliance-check-model-limitation).
- Equivocator detection. `state.equivocators` is taken as
  input; the body of `on_inclusion_list` is not modelled. See
  [FINDINGS.md §2.6](FINDINGS.md#26-equivocator-detection-is-not-modelled-model-limitation).
- Proof-of-stake economics, slashing, or stake-weighted
  voting. The fork choice's `HasQuorum` is a binary predicate.
- Cross-slot reasoning. The theorem applies to one block at
  one slot.

The full list with cross-references is in
[FINDINGS.md §6](FINDINGS.md#6-what-this-formalization-does-not-cover).

---

## Repository structure

```
focil-lean4/
├── README.md                    # this file
├── LICENSE                      # CC0-1.0
├── FINDINGS.md                  # research log of spec issues + model limits
├── CONTRIBUTING.md              # how to build, test, and contribute
├── THANKS.md                    # acknowledgments
├── CITATION.cff                 # citation metadata
├── lakefile.lean                # Lake build manifest
├── lean-toolchain               # pinned Lean toolchain version
├── FocilLean4.lean              # library root, re-exports all modules
├── docs/
│   ├── DESIGN.md                # architectural rationale
│   └── walkthrough.md           # guided tour of the main theorem
├── Focil/
│   ├── Types.lean               # data model: Transaction, IL, Block, FocilState
│   ├── Protocol.lean            # CompliantWith, FocilCompliant
│   ├── ForkChoice.lean          # ForkChoice structure + canonicality lemma
│   ├── Helpers.lean             # small reusable lemmas
│   ├── Safety.lean              # parameterised headline theorem and per-IL building block
│   ├── StakeModel.lean          # PoS-derived ForkChoice; >2/3 honest assumption
│   ├── AccountState.lean        # nonce-only EVM-validity model; FINDINGS §2.3
│   └── EndToEnd.lean            # end-to-end safety against the concrete model
├── Tests/
│   └── Examples.lean            # 14 worked scenarios; concrete ForkChoice instances
└── .github/
    ├── workflows/ci.yml         # CI: build, type-check, axiom audit
    └── ISSUE_TEMPLATE/          # issue and PR templates
```

---

## Reading the proofs

For a reviewer encountering this repo for the first time, the
suggested order:

1. **[`docs/DESIGN.md`](docs/DESIGN.md)**: the architectural
   rationale: what we modelled, what we abstracted, why. Eight
   short sections; ten minutes.
2. **[`docs/walkthrough.md`](docs/walkthrough.md)**: a guided
   tour of the main theorem, line by line. What each
   hypothesis means in protocol terms; what the conclusion
   guarantees and what it doesn't.
3. **[`Focil/Types.lean`](Focil/Types.lean)**: the data
   model. Each abstraction choice is justified inline.
4. **[`Focil/Protocol.lean`](Focil/Protocol.lean)**: the
   `CompliantWith` and `FocilCompliant` predicates.
   Cross-reference with `validate_inclusion_lists` in
   `consensus-specs/_features/eip7805/fork-choice.md`.
5. **[`Focil/ForkChoice.lean`](Focil/ForkChoice.lean)**: the
   `ForkChoice` structure (and its two propositional
   obligations) and the cornerstone lemma
   `canonical_implies_compliant`.
6. **[`Focil/Safety.lean`](Focil/Safety.lean)**: the
   headline 1-of-N theorem and the per-IL building block.
   The proofs are short because the conceptual work happened
   in the previous files.
7. **[`Focil/StakeModel.lean`](Focil/StakeModel.lean)**:
   the PoS-derived layer. Defines `StakeModel` and
   `AttesterRun`, proves the counting lemma, and supplies
   `AttesterRun.toForkChoice` plus the end-to-end
   `focil_pos_derived_safety`.
8. **[`Focil/AccountState.lean`](Focil/AccountState.lean)**:
   the nonce-only EVM-validity model. Formalizes the
   front-running attack from FINDINGS §2.3 as the theorem
   `front_running_breaks_appendability`.
9. **[`Focil/EndToEnd.lean`](Focil/EndToEnd.lean)**: the
   end-to-end concrete safety theorems.
   `focil_concrete_safety` discharges the entire safety chain
   against the concrete account-state predicate; the
   PoS-derived corollary `focil_concrete_pos_safety` does the
   same starting from the >2/3 honest assumption. No opaque
   predicates remain.
10. **[`Tests/Examples.lean`](Tests/Examples.lean)**: fourteen
    concrete scenarios. Scenario 14 fires the concrete
    PoS-derived contrapositive on real account-state data;
    Scenario 12 fires the abstract PoS-derived theorem;
    Scenario 13 fires the front-running attack on concrete
    data; Scenario 11 fires the 1-of-N theorem on the
    abstract `ForkChoice`; Scenarios 6–10 fire the per-IL
    building block, the contrapositive, and the equivocator
    degradation.
11. **[`FINDINGS.md`](FINDINGS.md)**: the research log; nine
    items spanning spec gaps, model limits, and the
    abstraction-level discoveries that emerged from building
    the formalization.

---

## Verifying axiom-freeness

Lean's kernel can report which axioms a theorem depends on.
The four pure parameterised safety theorems in
`Focil/Safety.lean` and the end-to-end concrete safety
theorem `Focil.focil_concrete_safety` in `Focil/EndToEnd.lean`
all depend on **zero** kernel axioms (not even
`Classical.choice` or `propext`). The PoS-derived end-to-end
theorems in `Focil/StakeModel.lean` and the concrete
`Focil/EndToEnd.lean` PoS variant additionally depend on
`propext` and `Quot.sound`, two foundational kernel axioms
that ship with every Lean installation and are accepted
without controversy across the Lean community.
`Classical.choice` and `sorryAx` are not used anywhere in the
project.

To reproduce the audit, create a file with:

```lean
import FocilLean4

#print axioms Focil.focil_one_of_n_protection
#print axioms Focil.focil_censorship_resistance
#print axioms Focil.censoring_block_not_canonical
#print axioms Focil.canonical_implies_compliant
#print axioms Focil.AttesterRun.toForkChoice
#print axioms Focil.focil_pos_derived_safety
#print axioms Focil.front_running_breaks_appendability
#print axioms Focil.focil_concrete_safety
#print axioms Focil.focil_concrete_pos_safety
#print axioms Focil.focil_concrete_pos_censoring_block_not_canonical
```

and run:

```bash
lake env lean YourFile.lean
```

You should see:

```
'Focil.focil_one_of_n_protection' does not depend on any axioms
'Focil.focil_censorship_resistance' does not depend on any axioms
'Focil.censoring_block_not_canonical' does not depend on any axioms
'Focil.canonical_implies_compliant' does not depend on any axioms
'Focil.AttesterRun.toForkChoice' depends on axioms: [propext, Quot.sound]
'Focil.focil_pos_derived_safety' depends on axioms: [propext, Quot.sound]
'Focil.front_running_breaks_appendability' depends on axioms: [propext, Quot.sound]
'Focil.focil_concrete_safety' does not depend on any axioms
'Focil.focil_concrete_pos_safety' depends on axioms: [propext, Quot.sound]
'Focil.focil_concrete_pos_censoring_block_not_canonical' depends on axioms: [propext, Quot.sound]
```

CI runs this check on every push (see
[`.github/workflows/ci.yml`](.github/workflows/ci.yml)) and
fails the build if `Classical.choice` or `sorryAx` is
introduced anywhere, or if any of the five pure safety
theorems acquires _any_ axiom dependency.

---

## Spec findings

Three of the items the formalization surfaced are substantive
research observations; the rest are spec-hygiene issues and
disclosed model limitations.

**Substantive observations:**

- **The honest-attester invariant in EIP-7805 admits two
  non-equivalent formal readings, and the natural one is
  unsatisfiable.** The English-prose rule "honest attesters
  refuse to vote for non-compliant blocks" can be read globally
  (across all stores) or locally (against the attester's own
  store). The global reading cannot be discharged non-vacuously
  when EVM validity is opaque. The spec is correct under the
  local reading; informal arguments that compose the rule
  across attesters with different stores have a hidden
  quantifier-scope assumption.
  ([§2.7](FINDINGS.md#27-the-honest-attester-invariant-must-be-relativized-to-the-attesters-store))

- **Equivocation is a free censorship channel for any
  transaction listed by only one IL committee member.** A
  Byzantine member can void their own contribution by signing
  two distinct ILs. The EIP's existing equivocation handling
  is correct fork-choice safety, but it degrades the "1-of-N
  honesty" guarantee to "1-of-(N − equivocators)" for any
  transaction listed only by an equivocating member. The EIP
  addresses equivocation at the bandwidth level only.
  Demonstrated by example in `Tests/Examples.lean` Scenarios
  9–10.
  ([§2.4](FINDINGS.md#24-equivocation-as-a-censorship-channel))

- **Adversarial validity changes are formally exhibited.** A
  colluding party sharing an IL transaction's sender can
  submit a transaction that, once appended by the proposer,
  makes the IL transaction non-appendable. Formalized as
  `front_running_breaks_appendability` in
  [`Focil/AccountState.lean`](Focil/AccountState.lean), with
  Scenario 13 demonstrating the attack on concrete data. The
  attacker pays one gas fee with no slashing penalty.
  ([§2.3](FINDINGS.md#23-adversarial-validity-changes))

**Spec-hygiene issues:**

- **`MAX_TRANSACTIONS_PER_INCLUSION_LIST = 1`** is marked
  `# TODO: Placeholder` in `beacon-chain.md` and contradicts
  the 8 KiB per-IL byte cap quoted by the EIP body.
  ([§1.3](FINDINGS.md#13-max_transactions_per_inclusion_list--1-placeholder))
- **`validate_inclusion_lists` has no body**: only a
  one-sentence docstring that leaves three substantive
  questions open.
  ([§2.1](FINDINGS.md#21-validate_inclusion_lists-is--unimplemented))
- **`parent_hash`/`parent_root`** referenced in `validator.md`
  are not fields of the `InclusionList` container in
  `beacon-chain.md`.
  ([§1.2](FINDINGS.md#12-parent_hash--parent_root-on-inclusionlist))

**Disclosed model limitations:**

- Sequential dependence between IL transactions is not
  captured by `CompliantWith`
  ([§2.5](FINDINGS.md#25-sequential-dependence-in-the-compliance-check-model-limitation)).
- Equivocator detection is not modelled; `state.equivocators`
  is taken as input
  ([§2.6](FINDINGS.md#26-equivocator-detection-is-not-modelled-model-limitation)).

Plus smaller cross-references and threat-model notes; see
[FINDINGS.md](FINDINGS.md) for the full discussion.

---

## Background

FOCIL (Fork-Choice enforced Inclusion Lists, EIP-7805) is a
committee-based mechanism for guaranteeing transaction
inclusion in Ethereum. A small committee of validators per
slot publishes inclusion lists; the next block's proposer must
include those transactions or have their block orphaned by
attesters via the fork-choice rule. The mechanism's claimed
property is "1-out-of-N" honesty among committee members.

FOCIL is the headline feature of Ethereum's late-2026 Hegotá
hard fork, scheduled to follow Glamsterdam. Vitalik Buterin's
[_A shallow dive into formal verification_](https://vitalik.eth.limo/general/2026/05/18/fv.html)
(May 18, 2026) sharpened the case for taking machine-checked
proofs of consensus-layer mechanisms seriously, and was a
direct motivation for this work.

References:

- [EIP-7805](https://eips.ethereum.org/EIPS/eip-7805): primary
  spec.
- [consensus-specs `_features/eip7805/`](https://github.com/ethereum/consensus-specs/tree/e678deb772fe83edd1ea54cb6d2c1e4b1e45cec6/specs/_features/eip7805):
  Python reference implementation, pinned at commit
  `e678deb772fe83edd1ea54cb6d2c1e4b1e45cec6`. The directory
  has since been promoted out of `_features/` and now lives at
  [`specs/heze/`](https://github.com/ethereum/consensus-specs/tree/master/specs/heze)
  on the default branch; the pinned commit is what this
  repository's citations refer to.
- [Ethereum Magicians: EIP-7805 discussion](https://ethereum-magicians.org/t/eip-7805-committee-based-fork-choice-enforced-inclusion-lists-focil/21578).
- [ethresear.ch: original FOCIL proposal](https://ethresear.ch/t/fork-choice-enforced-inclusion-lists-focil-a-simple-committee-based-inclusion-list-proposal/19870).

---

## Contributing and follow-on work

The end-to-end concrete safety theorems
(`Focil/EndToEnd.lean`) discharge the headline 1-of-N claim
against a nonce-only account-state model with no opaque
predicates remaining. The natural next milestones extend the
concrete EVM-validity layer to cover more of EIP-7805's threat
surface.

**Active milestone, balance-aware concrete validity.** The
current concrete model tracks per-sender nonces only. A
balance-aware variant would let us formalize the balance-drain
attack from FINDINGS §2.3 (a colluding party drains a
sender's balance below the base fee, invalidating the IL
transaction) end-to-end against the same PoS-derived chain.
Structurally identical to the nonce model; the case surface
roughly doubles. This directly addresses
[FINDINGS.md §4.3](FINDINGS.md#43-why-is-canappend-opaque).

**Active milestone, refined `CompliantWith` capturing
sequential validity dependence between IL transactions.** The
current `CompliantWith` predicate quantifies per-transaction
independently against the final block, but EIP-7805
§"Payload Construction" notes that an IL transaction can
become valid because an earlier IL transaction was appended.
A refined predicate would thread a hypothetical post-state
through the appendability check. This directly addresses
[FINDINGS.md §2.5](FINDINGS.md#25-sequential-dependence-in-the-compliance-check-model-limitation).

**Other contribution opportunities, ordered by leverage:**

1. **EIP-8141 Frame Transactions and the bounded
   validation-prefix replay rule.** EIP-7805's lead author
   describes a refinement of the FOCIL omission check for
   native AA transactions in his
   [Mar 16 ethereum-magicians post](https://ethereum-magicians.org/t/focil-native-account-abstraction/27999).
   Formalizing the bounded-VERIFY-execution check and the
   per-IL VERIFY-gas budget would extend the concrete safety
   chain to cover EIP-8141 Frame Transactions.
2. **Equivocator-detection model.** Formalize
   `on_inclusion_list` and prove that a faithful execution
   correctly populates `state.equivocators`.
   ([FINDINGS.md §2.6](FINDINGS.md#26-equivocator-detection-is-not-modelled-model-limitation))
3. **IL gossip / network model.** Formalize the threat
   surface for network-level adversaries.
   ([FINDINGS.md §2.2](FINDINGS.md#22-network-adversary-against-il-propagation))

See [CONTRIBUTING.md](CONTRIBUTING.md) for how to build, test,
and submit changes, and [`THANKS.md`](THANKS.md) for
acknowledgments.

---

## License

[CC0-1.0](LICENSE), matching the EIPs. Use freely.
