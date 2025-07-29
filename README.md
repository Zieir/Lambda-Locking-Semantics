# IMP Concur ↔ HOL-CSP Integration

This project was developed during an 8-week research internship at the *Laboratoire de Méthodes Formelles (LMF)*, Université Paris-Saclay.

## Overview

The main goal was to design and implement a simple yet powerful interface between **IMP Concur** — a small concurrent imperative language derived from IMP — and **Isabelle/HOL-CSP**, a formal proof environment based on Isabelle/HOL and Communicating Sequential Processes (CSP).

Isabelle/HOL-CSP supports modeling and reasoning about complex systems, including infinite event structures, dense time, physical state representation, and algebraic structures. Integrating IMP Concur with this environment enables formal verification of concurrent programs through a rigorous semantic foundation.

## Contributions

This repository contains the following key components:

- **Parser**: Converts IMP Concur programs into an internal abstract syntax tree.
- **Context checker**: Validates variable scopes, lock usage, and thread declarations.
- **Static semantic analyzer**: Ensures programs are well-formed and respect typing and concurrency constraints.
- **Semantic encoder**: Translates IMP Concur programs into HOL-CSP specifications (and optionally into a ProcOmata-style automaton format).

These components form a complete toolchain for analyzing and verifying IMP Concur programs using Isabelle/HOL-CSP.

## Highlights

- **Modular architecture** designed for extensibility and clarity.
- **Unidirectional translator** from IMP Concur to CSP process terms in Isabelle/HOL.
- **Experimental validation** on representative concurrent examples.
- **Formal correctness guarantees** based on semantic encoding.

## Technologies Used

- Isabelle/ML (for implementation within Isabelle)
- HOL-CSP (for CSP algebra modeling in Isabelle/HOL)
- Functional programming & typed lambda calculus
- Formal methods and concurrency theory

## Keywords

`Formal Verification` • `IMP Concur` • `Isabelle/HOL-CSP` • `Concurrency` • `Automatic Translation` • `CSP` • `Process Algebra`
