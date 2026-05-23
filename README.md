# PrimaryLogic

A personal formalization project in Lean 4, building first-order logic from scratch with a focus on understanding the gap between textbook proofs and machine-checked mathematics.

## What This Is

- **Educational**: A hands-on exploration of FOL syntax, proof theory, and model theory
- **Self-contained**: Custom definitions for terms, formulas, Hilbert-style proofs, and Tarski semantics
- **Work in progress**: Currently working through the completeness theorem (Henkin construction)

## Current Status

- [x] Syntax (terms, formulas, substitution)
- [x] Proof system (Hilbert-style + axiom schemas)
- [x] Soundness
- [x] Deduction theorem, propositional meta-theorems
- [x] Lindenbaum maximal consistent extension
- [x] Term model / Truth lemma
- [-] Henkin construction
- [ ] Completeness

## Key Design Decisions

- **Axiom schemas as typeclass**: `AxiomSchema L α` allows modular extension (e.g., adding equality axioms)
- **Explicit variable management**: Separate tracking of free/bound variables (`fVars`/`bVars`) with `FreeFor` predicates for capture-avoiding substitution
- **Language-agnostic**: Generic over function/predicate symbol types (`LF`, `LP`)

## Build

Build with `lake build`.

## Notes

- Heavily commented for human readability
- `Hom.lean` contains categorical infrastructure for future language extensions
