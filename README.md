# zklib

`zklib` is a Lean-first library for machine-checked zk mathematics and verifier specifications.

The project is organized around two ideas:

- Keep the long-lived algebraic core separate from protocol-specific choices.
- Make room for real-world verifier targets without letting any single curve or proving system define the entire repository.
- Keep placeholder theorem boundaries out of the default import surface.

## Layout

```text
Zklib/
  Core/
    Field.lean
    ExtensionField.lean
    Polynomial.lean
    EvaluationDomain.lean
    NTT.lean
    Transcript.lean
    ConstraintSystem.lean
  Instantiations/
    EIP4844.lean
    ZkVM.lean
  Showcase/
    BN254OptimalAte.lean
  Scaffold.lean
docs/
  roadmap.md
```

## Layers

### `Zklib.Core`

Stable algebraic infrastructure that should outlive any single proving system:

- `mathlib` typeclass-based ring, field, and algebra foundations
- polynomials, evaluation, and interpolation
- cyclic evaluation domains, shifted cosets, and roots of unity
- NTT semantics and radix-2 algorithmic correctness
- transcript semantics with explicit challenge observation and sequencing laws
- constraint-system semantics with canonical public-input recovery

### `Zklib.Instantiations`

Concrete verifier-facing targets that make the repository useful to current zk ecosystems:

- `EIP4844`: setup-indexed KZG verifier boundaries with canonical claim/statement-system bridges
- `ZkVM`: verification-key semantics with canonical statement bridges into `ConstraintSystemSpec`

### `Zklib.Showcase`

High-prestige, high-difficulty endgame formalizations that demonstrate the full power of the library:

- `BN254OptimalAte`: an honest pairing-bilinearity boundary today, full optimal-Ate formalization later

## Initial Goal

The first repository milestone is not the full BN254 pairing proof. The first milestone is a reusable algebraic core that makes later protocol formalizations possible.

See [docs/roadmap.md](docs/roadmap.md) for the initial sequence.

## Import Surface

- `import Zklib` brings in the stable core surface.
- `import Zklib.Instantiations` and `import Zklib.Showcase` opt into protocol-facing and endgame targets.
- `import Zklib.Scaffold` brings in placeholder theorem boundaries that may still use `by sorry`.

## Getting Started

This repository expects a standard Lean 4 + `mathlib` workflow:

```powershell
lake exe cache get
lake build
```

`lake exe cache get` is part of the normal setup here. We should lean on the
`mathlib` cache instead of recompiling the world from scratch.

Dependency revisions are pinned through `lake-manifest.json`. Use `lake update`
only when intentionally refreshing those pins and committing the manifest
change.

## Working Style

- keep proofs decomposed across small files and focused modules
- prefer aggregator files that re-export topic-specific submodules
- use `by sorry` to reserve theorem boundaries early, then tighten them gradually
- keep `by sorry` out of the default `import Zklib` surface
- avoid monolithic "everything about X" files

## License

This project is dual-licensed under either:

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE))
- MIT license ([LICENSE-MIT](LICENSE-MIT))

Unless explicitly stated otherwise, any contribution intentionally submitted for
inclusion in `zklib` is dual-licensed as above.
