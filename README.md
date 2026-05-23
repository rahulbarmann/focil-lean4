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

**Headline theorem** (`Focil.focil_one_of_n_protection`, in
[`Focil/Safety.lean`](Focil/Safety.lean)):

> Fix any `ForkChoice` value `fc` (which bundles a fork-choice
> store snapshot, a block-fullness model, and two soundness
> obligations on attester voting; see below). For any block
> `b` and transaction `tx`: if
>
> - some inclusion list in `fc.state.stored_ils` whose author
>   is not in `fc.state.equivocators` contains `tx`,
> - `tx` could be validly appended to `b` (`CanAppend tx b`),
> - `b` is not full under `fc.full`,
> - and `b` is the canonical chain head under `fc`,
>
> then `tx ∈ b.transactions`.

This is the formal counterpart of EIP-7805's marquee 1-of-N
honesty claim: it suffices that _at least one_ non-equivocating
IL committee member listed `tx` for `tx` to be force-included
in any canonical block (modulo invalidity and block fullness).

The witness IL is existentially quantified, so adversaries
controlling some committee seats and equivocating others do not
defeat the guarantee, as long as at least one seat publishes a
non-equivocating IL containing `tx`.

The headline theorem is a thin corollary of a per-IL building
block, `Focil.focil_censorship_resistance`, which takes the
witness IL as an explicit parameter. A direct contrapositive,
`Focil.censoring_block_not_canonical`, says that a block
omitting such a `tx` cannot become canonical: the form a
builder reasoning about block construction cares about.

**The proof depends on:**

1. The abstract opaque predicate
   `CanAppend : Transaction → Block → Prop`, modelling
   "EVM-valid appendability". The proof is universally
   quantified over all `CanAppend` realizations, but a real
   claim against a real Ethereum implementation requires a
   faithful concrete `CanAppend`.
2. Two propositional obligations carried as fields of the
   `ForkChoice` structure (in
   [`Focil/ForkChoice.lean`](Focil/ForkChoice.lean)):
    - `quorum_has_honest_voter`: any block reaching a quorum
      has at least one honest validator who voted for it.
    - `honest_attester_compliance`: honest validators only
      vote for FOCIL-compliant blocks (relative to `fc`'s
      bundled store snapshot).

    Both obligations must be discharged by every concrete
    `ForkChoice` value. This repository ships two instances:
    - `Tests.Examples.emptyForkChoice` discharges them
      vacuously by making `HasQuorum` and `Voted` constantly
      false. Structural sanity check only.
    - `Tests.Examples.threeValidatorForkChoice` is a
      non-vacuous 3-validator scenario where both obligations
      are discharged by genuine case analysis. The headline
      theorem fires against this instance in
      [Scenario 11 of `Tests/Examples.lean`](Tests/Examples.lean).
      Scenarios 6–10 cover the per-IL building block, the
      builder-side contrapositive, and the equivocator
      degradation case.

    A `ForkChoice` instance derived from a refined LMD-GHOST
    model (where the soundness obligations are _proven_ from a
    primitive ">2/3 honest stake" assumption rather than
    postulated) is the next milestone for this project; see
    [FINDINGS.md §5](FINDINGS.md#5-where-the-formalization-is-conditional)
    and the sketch in
    [`CONTRIBUTING.md`](CONTRIBUTING.md#1-pos-derived-forkchoice-instantiation-highest-leverage).

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
│   └── Safety.lean              # main theorem and corollary
├── Tests/
│   └── Examples.lean            # 11 worked scenarios; concrete ForkChoice instances
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
6. **[`Focil/Safety.lean`](Focil/Safety.lean)**: the main
   theorem. The proof is short because the conceptual work
   happened in the previous files.
7. **[`Tests/Examples.lean`](Tests/Examples.lean)**: eleven
   concrete scenarios. Scenario 11 fires the headline 1-of-N
   theorem; Scenarios 6–8 fire the per-IL building block and
   its contrapositive; Scenarios 9–10 demonstrate the
   equivocator degradation.
8. **[`FINDINGS.md`](FINDINGS.md)**: the research log; nine
   items spanning spec gaps, model limits, and the
   abstraction-level discovery (§2.7) that emerged from
   building the non-vacuous instance.

---

## Verifying axiom-freeness

Lean's kernel can report which axioms a theorem depends on. To
confirm that the safety theorems depend on zero kernel axioms
(not even `Classical.choice` or `propext`), create a one-line
file:

```lean
import FocilLean4

#print axioms Focil.focil_one_of_n_protection
#print axioms Focil.focil_censorship_resistance
#print axioms Focil.censoring_block_not_canonical
#print axioms Focil.canonical_implies_compliant
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
```

CI runs this check on every push (see
[`.github/workflows/ci.yml`](.github/workflows/ci.yml)) and
fails the build if any axiom dependency is introduced,
including `sorryAx`, which `sorry` would surface as.

Note: the propositional obligations on the `ForkChoice`
structure (`quorum_has_honest_voter` and
`honest_attester_compliance`) are **not** kernel axioms; they
are fields of a Lean structure, supplied by every concrete
instance. The "zero axioms" claim is therefore about the
proof's _internal_ logic, not about the soundness assumptions
on the fork-choice rule itself. See
[FINDINGS.md §5](FINDINGS.md#5-where-the-formalization-is-conditional).

---

## Spec findings

Two of the items the formalization surfaced are substantive
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

This repository is the first part of a planned two-part
research programme. The headline 1-of-N safety theorem proven
here is conditional on two propositional obligations of the
underlying fork-choice rule (see "What is proven" above). The
next milestone is to discharge those obligations from a more
primitive PoS assumption.

**Active milestone, PoS-derived `ForkChoice` instantiation
(target: 4–6 weeks from initial release).** The current
non-vacuous instance `threeValidatorForkChoice` is hand-crafted.
A real refinement would model attester voting at the per-slot
level (committee composition, vote tallying, attester honesty)
and _derive_ the two soundness conditions from a primitive
">2/3 honest stake" assumption. The headline theorem then
becomes free-standing: its only remaining axiom-of-faith is the
same >2/3 honest stake assumption that underlies every other
Ethereum PoS safety result. A Lean structure sketch is in
[CONTRIBUTING.md §1](CONTRIBUTING.md#1-pos-derived-forkchoice-instantiation-highest-leverage).

**Other contribution opportunities, ordered by leverage:**

1. **Refined `CompliantWith`** that handles sequential
   validity dependence between IL transactions.
   ([FINDINGS.md §2.5](FINDINGS.md#25-sequential-dependence-in-the-compliance-check-model-limitation))
2. **Concrete `CanAppend`** built from a per-account
   nonce/balance abstraction, enabling proofs about
   adversarial validity changes.
   ([FINDINGS.md §2.3](FINDINGS.md#23-adversarial-validity-changes))
3. **Equivocator-detection model.** Formalize
   `on_inclusion_list` and prove that a faithful execution
   correctly populates `state.equivocators`.
   ([FINDINGS.md §2.6](FINDINGS.md#26-equivocator-detection-is-not-modelled-model-limitation))
4. **IL gossip / network model.** Formalize the threat
   surface for network-level adversaries.
   ([FINDINGS.md §2.2](FINDINGS.md#22-network-adversary-against-il-propagation))

See [CONTRIBUTING.md](CONTRIBUTING.md) for how to build, test,
and submit changes, and [`THANKS.md`](THANKS.md) for
acknowledgments.

---

## License

[CC0-1.0](LICENSE), matching the EIPs. Use freely.
