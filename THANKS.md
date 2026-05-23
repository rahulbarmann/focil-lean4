# Acknowledgments

This formalization builds directly on the work of the people
listed below. The errors are mine; the foundations are theirs.

## EIP-7805 authors

The protocol formalized in this repository was specified by:

- **Thomas Thiery** (Ethereum Foundation, lead author)
- **Francesco D'Amato** (Ethereum Foundation)
- **Julian Ma** (Ethereum Foundation)
- **Barnabé Monnot** (Ethereum Foundation)
- **Terence Tsao** (Offchain Labs)
- **Jacob Kaufmann** (Ethereum Foundation)
- **Jihoon Song** (Ethereum Foundation)

The Lean model in `Focil/` is a direct translation of their
work. Where the formalization revealed ambiguities or gaps
(see `FINDINGS.md`), it is in the spirit of "let the proof
assistant find what English missed," not as a critique of the
specification effort.

## consensus-specs maintainers

The Python reference implementation in
[`ethereum/consensus-specs`](https://github.com/ethereum/consensus-specs)
was the second source of truth throughout the project,
particularly the `_features/eip7805/` directory. Citations
in this repository are pinned at commit
`e678deb772fe83edd1ea54cb6d2c1e4b1e45cec6`.

## ethresear.ch and Ethereum Magicians

The two threads that shaped FOCIL's design before it became an
EIP:

- [Fork-Choice enforced Inclusion Lists (FOCIL): A simple
  committee-based inclusion list proposal](https://ethresear.ch/t/fork-choice-enforced-inclusion-lists-focil-a-simple-committee-based-inclusion-list-proposal/19870)
  on ethresear.ch.
- [EIP-7805: Committee-based, Fork-choice enforced Inclusion
  Lists (FOCIL)](https://ethereum-magicians.org/t/eip-7805-committee-based-fork-choice-enforced-inclusion-lists-focil/21578)
  on Ethereum Magicians.

## The Lean and Mathlib communities

We do not depend on Mathlib (FINDINGS.md §4.1), but the
Lean 4 core, the elan toolchain manager, and the broader Lean
community's documentation made the formalization possible at
this scope and quality. The
[Lean Zulip](https://leanprover.zulipchat.com) is the most
reliable place to ask Lean-specific questions.

## Vitalik Buterin

The blog post
[_A shallow dive into formal verification_](https://vitalik.eth.limo/general/2026/05/18/fv.html)
(May 18, 2026) sharpened the case for taking
machine-checked proofs of consensus-layer mechanisms
seriously, and was a direct motivation for this work.
