# Contributing

## Proof Style

- Do not accumulate an entire development inside one file.
- Prefer a small aggregator file plus topic-specific submodules.
- Introduce theorem boundaries early, even if the first pass ends with `by sorry`.
- Keep reusable algebra in `Zklib.Core`.
- Keep protocol-specific details in `Zklib.Instantiations`.
- Keep prestige endgame theorems in `Zklib.Showcase`.

## Early Development Rule

This repository explicitly allows placeholder proofs with `by sorry` during early
scaffolding. The goal is to stabilize module boundaries and statement shapes
before we try to close every theorem. Those placeholders should stay behind
explicit `Scaffold` imports rather than the default `import Zklib` surface.

## Suggested Shape

Good:

- one concept family per directory
- one interface file
- one or more lemma files
- one aggregator file that re-exports the family

Avoid:

- giant files with definitions, semantics, and all proofs mixed together
- protocol-specific assumptions leaking into the algebraic core

## Licensing

By intentionally submitting a contribution to this repository, you agree that
your contribution is dual-licensed under `MIT OR Apache-2.0`.
