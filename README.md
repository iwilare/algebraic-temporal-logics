## Algebraic Temporal Logics

This repository contains the Agda presentation of a quantified linear temporal logic QLTL which can reason on the temporal evolution of any multi-sorted algebra (e.g. (directed) graphs, tree-like structures).

An example in the case of the signature of directed graphs can be found at [Example.agda](Example.agda).

The logic is based on the counterpart paradigm (in the sense of Lewis) to capture the evolution of individual elements of the algebraic structure between worlds/instants of time.

## Positive normal forms

Some theorems on the positive normal forms of these counterpart-based temporal logics can be found in [PNF](PNF), considering both the cases in which the counterpart morphisms of the model are either partial functions or (possibly duplicating) relations.

## Requirements

- `agda` 2.6.2.2
- `agda-stdlib` 1.7.1
