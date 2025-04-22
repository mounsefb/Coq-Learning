# Induction in Coq

This document summarizes the key concepts of induction as introduced in the `induction.v` file from the Software Foundations (SF) Coq course.

## What is Induction?

Induction is a fundamental proof technique used to reason about recursively defined structures or processes. In Coq, it is commonly applied to natural numbers, lists, and other inductive types.

## Inductive Definitions

### Natural Numbers
The natural numbers (`nat`) are defined inductively in `induction.v`:
```coq
Inductive nat : Type :=
| O : nat
| S : nat -> nat.
```
- `O` represents zero.
- `S` is the successor function, representing the next natural number.

### Lists
Lists are another example of an inductive type:
```coq
Inductive list (X : Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.
```
- `nil` represents an empty list.
- `cons` constructs a list by adding an element to the front.

## Proof by Induction

### Structure of Inductive Proofs
To prove a property `P` for an inductive type:
1. **Base Case**: Prove `P` for the simplest constructor (e.g., `O` for `nat` or `nil` for `list`).
2. **Inductive Step**: Assume `P` holds for a smaller instance and prove it for the next constructor.

### Example: Addition is Associative
The `induction.v` file demonstrates proofs like the associativity of addition:
```coq
Theorem add_assoc : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof.
    intros n m p.
    induction n as [| n' IHn'].
    - (* Base case *) reflexivity.
    - (* Inductive step *) simpl. rewrite IHn'. reflexivity.
Qed.
```

## Tactics for Induction

- `induction`: Automatically generates base and inductive cases.
- `simpl`: Simplifies expressions.
- `rewrite`: Substitutes equal terms.
- `reflexivity`: Proves equality.

## Common Pitfalls

1. **Forgetting Base Cases**: Ensure all constructors are covered.
2. **Incorrect Inductive Hypothesis**: Carefully state the property being proved.
3. **Overlooking Recursive Definitions**: Use `simpl` to handle recursive functions.

## Exercises

The `induction.v` file includes exercises to practice induction:
1. Prove that `n + 0 = n` for all natural numbers `n`.
2. Show that reversing a list twice yields the original list.

## Conclusion

Induction is a powerful tool for reasoning about recursive structures. The `induction.v` file provides a solid foundation for mastering formal proofs in Coq.
