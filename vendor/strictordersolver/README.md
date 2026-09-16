# StrictOrderSolver

Complete solver for strict orders (transitive+irreflexive relations) for Rocq.

## Usage

The solver works for any relation that implements the [`Transitive`](https://rocq-prover.org/doc/V9.1.0/corelib/Corelib.Classes.RelationClasses.html#Transitive) and [`Irreflexive`](https://rocq-prover.org/doc/V9.1.0/corelib/Corelib.Classes.RelationClasses.html#Irreflexive) classes. These are implicitly implemented if you instead implement the [`StrictOrder`](https://rocq-prover.org/doc/V9.1.0/corelib/Corelib.Classes.RelationClasses.html#StrictOrder) class.

To invoke the solver, use `strict_order rel`, where `rel` is your strict order relation.

The solver will close the goal in two cases:

1. If your goal is of the form `rel a b` and it is provable from your `rel c d` premises
2. If your `rel c d` premises lead to a contradiction

See [Tests.v](./Tests.v) for example usages and supported use-cases.

```rocq
From Ltac2 Require Import Ltac2.
From StrictOrderSolver Require Import Solver.
From Stdlib Require Import Classes.RelationClasses.

Axiom rel : nat -> nat -> Prop.
Instance SO : StrictOrder rel. Admitted.

Goal forall a b c d e,
   rel a e -> rel a b -> rel c d -> rel b c -> rel a d.
Proof.
   intros.
   strict_order rel.
Qed.
```

## Installation

1. Add the Rocq [opam](https://opam.ocaml.org/) repository

```sh
opam repo add rocq-released https://rocq-prover.org/opam/released
```

2. Install as a dependency (or add `strict-order-solver` to your `dune-project`/`.opam` file)

```sh
opam install strict-order-solver
```

3. Add `StrictOrderSolver` to your Rocq theories (in dune, it is the `rocq.theory (theories)` stanza)
