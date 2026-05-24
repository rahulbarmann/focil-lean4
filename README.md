# focil-lean4

[![CI](https://github.com/rahulbarmann/focil-lean4/actions/workflows/ci.yml/badge.svg)](https://github.com/rahulbarmann/focil-lean4/actions/workflows/ci.yml)
[![License: CC0-1.0](https://img.shields.io/badge/License-CC0_1.0-blue.svg)](LICENSE)
[![Lean](https://img.shields.io/badge/Lean-4.29.1-blueviolet)](lean-toolchain)

A Lean 4 formalization of FOCIL, the consensus-layer
censorship-resistance mechanism specified in
[EIP-7805](https://eips.ethereum.org/EIPS/eip-7805) (the headline
feature of Ethereum's late-2026 Hegotá hard fork). Proves that
under two precisely stated assumptions about the underlying
fork-choice rule, a transaction listed in a stored,
non-equivocating inclusion list cannot be excluded from a
canonical block (modulo invalidity and block fullness). Build is
green on Lean 4.29.1; the safety proof is `sorry`-free and
depends on zero kernel axioms; ships with a non-vacuous
3-validator instance demonstrating the theorem firing on a real
scenario.

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

**End-to-end PoS-derived theorem**
(`Focil.focil_pos_derived_safety`, in
[`Focil/StakeModel.lean`](Focil/StakeModel.lean)):

> Fix any `StakeModel` with strictly more than 2/3 honest
> validators (the standard Ethereum PoS supermajority
> assumption), and any `AttesterRun` over that model where
> honest validators only vote for FOCIL-compliant blocks. For
> any block `b` and transaction `tx`: if some inclusion list
> stored in `r.state` and not in `r.state.equivocators`
> contains `tx`, the block has accumulated a strict 2/3
> quorum of votes, `tx` could be validly appended to `b`, and
> `b` is not full, then `tx ∈ b.transactions`.

This is the marquee result of the project. Both structural
obligations of the underlying fork-choice rule
(`quorum_has_honest_voter`, `honest_attester_compliance`) are
_derived_, not postulated. The only remaining axioms-of-faith
are Ethereum's standard ">2/3 honest" assumption (encoded as
`s.honest_majority`), the spec's "honest attesters refuse
non-compliant blocks" rule (encoded as `r.honest_rule`), and
the faithfulness of the abstract `CanAppend` predicate.

**Headline 1-of-N theorem** (`Focil.focil_one_of_n_protection`,
in [`Focil/Safety.lean`](Focil/Safety.lean)):

> Fix any `ForkChoice` value `fc`. For any block `b` and
> transaction `tx`: if some inclusion list in
> `fc.state.stored_ils` whose author is not in
> `fc.state.equivocators` contains `tx`, `tx` is appendable to
> `b`, `b` is not full, and `b` is canonical under `fc`, then
> `tx ∈ b.transactions`.

This is the formal counterpart of EIP-7805's marquee 1-of-N
honesty claim: it suffices that _at least one_ non-equivocating
IL committee member listed `tx`. Adversaries controlling some
committee seats and equivocating others do not defeat the
guarantee, as long as at least one seat publishes a
non-equivocating IL containing `tx`. The end-to-end PoS-derived
theorem above is a corollary (instantiate `fc` with
`AttesterRun.toForkChoice`).

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

1. The abstract opaque predicate
   `CanAppend : Transaction → Block → Prop`, modelling
   "EVM-valid appendability". The proof is universally
   quantified over all `CanAppend` realizations, but a real
   claim against a real Ethereum implementation requires a
   faithful concrete `CanAppend`.
2. The "honest attesters refuse non-compliant blocks" rule is
   encoded as the `honest_rule` field of `AttesterRun`. This
   is the per-attester rule EIP-7805 specifies as the
   normative behaviour of a correct validator.
3. The ">2/3 honest validators" assumption is encoded as the
   `honest_majority` field of `StakeModel`. This is the
   standard PoS safety assumption underlying every other
   Ethereum consensus result.

The repository ships three demonstrations:

- `Tests.Examples.emptyForkChoice` discharges the abstract
  `ForkChoice` obligations vacuously (sanity check only).
- `Tests.Examples.threeValidatorForkChoice` is a hand-crafted
  3-validator scenario; Scenarios 6–11 fire the headline
  theorem against it.
- `Tests.Examples.attesterRun4v` builds a 4-validator
  `StakeModel` and `AttesterRun` from scratch and derives
  everything via `AttesterRun.toForkChoice`. Scenario 12 fires
  `focil_pos_derived_safety` against it with no postulates
  remaining.

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

- The EVM. Validity is captured by the abstract `CanAppend`.
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
│   ├── Safety.lean              # headline theorem and per-IL building block
│   ├── StakeModel.lean          # PoS-derived ForkChoice; >2/3 honest assumption
│   └── AccountState.lean        # nonce-only EVM-validity model; FINDINGS §2.3
├── Tests/
│   └── Examples.lean            # 13 worked scenarios; concrete ForkChoice instances
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
9. **[`Tests/Examples.lean`](Tests/Examples.lean)**: thirteen
   concrete scenarios. Scenario 12 fires the PoS-derived
   end-to-end theorem; Scenario 13 fires the front-running
   attack on concrete data; Scenario 11 fires the 1-of-N
   theorem on the abstract `ForkChoice`; Scenarios 6–10 fire
   the per-IL building block, the contrapositive, and the
   equivocator degradation.
10. **[`FINDINGS.md`](FINDINGS.md)**: the research log; nine
    items spanning spec gaps, model limits, and the
    abstraction-level discoveries that emerged from building
    the formalization.

---

## Verifying axiom-freeness

Lean's kernel can report which axioms a theorem depends on.
The four pure safety theorems in `Focil/Safety.lean` depend on
**zero** kernel axioms (not even `Classical.choice` or
`propext`). The PoS-derived end-to-end theorem in
`Focil/StakeModel.lean` additionally depends on `propext` and
`Quot.sound`, two foundational kernel axioms that ship with
every Lean installation and are accepted without controversy
across the Lean community. `Classical.choice` and `sorryAx`
are not used anywhere in the project.

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
```

CI runs this check on every push (see
[`.github/workflows/ci.yml`](.github/workflows/ci.yml)) and
fails the build if `Classical.choice` or `sorryAx` is
introduced anywhere, or if any of the four pure safety
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
[_A shallow dive into formal verification_](https://vitalik.eth.limo/)
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

The PoS-derived `ForkChoice` instantiation
(`Focil/StakeModel.lean`) discharges the headline theorem's
two structural obligations from a >2/3 honest-validator
assumption, demonstrated end-to-end by Scenario 12 of
`Tests/Examples.lean`. The natural next milestones tighten
the remaining abstractions.

**Active milestone, refined `CompliantWith` capturing
sequential validity dependence between IL transactions
(target: 2–3 weeks from initial release).** The current
`CompliantWith` predicate quantifies per-transaction
independently against the final block, but EIP-7805
§"Payload Construction" notes that an IL transaction can
become valid because an earlier IL transaction was appended.
A refined predicate would thread a hypothetical post-state
through the appendability check. This directly addresses
[FINDINGS.md §2.5](FINDINGS.md#25-sequential-dependence-in-the-compliance-check-model-limitation).

**Other contribution opportunities, ordered by leverage:**

1. **Refined `CanAppend` covering balance and AA dimensions.**
   The current account-state model in
   [`Focil/AccountState.lean`](Focil/AccountState.lean) tracks
   nonces only. A balance-aware variant would let us formalize
   the balance-drain attack from
   [FINDINGS.md §2.3](FINDINGS.md#23-adversarial-validity-changes);
   an EIP-7702-aware variant would cover the AA-revocation
   attack.
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
