# Basics in Coq

This document summarizes the key concepts from the `Basics.v` file in the *Software Foundations* series, which introduces fundamental Coq programming concepts.

## Introduction to Coq

Coq is a proof assistant based on dependent type theory. It allows us to write functional programs, specify properties, and prove them formally.

---

## Key Concepts

### 1. **Defining Functions and Values**
- Functions are defined using the `Definition` keyword.
- Example:
    ```coq
    Definition plus_two (n : nat) : nat := n + 2.
    ```

### 2. **Booleans**
- Coq provides a `bool` type with two values: `true` and `false`.
- Boolean functions can be defined using pattern matching:
    ```coq
    Definition negb (b : bool) : bool :=
        match b with
        | true => false
        | false => true
        end.
    ```

### 3. **Numbers**
- Coq includes a `nat` type for natural numbers.
- Constructors:
    - `O` for zero.
    - `S` for the successor function (e.g., `S O` is 1, `S (S O)` is 2).
- Example of addition:
    ```coq
    Fixpoint add (n m : nat) : nat :=
        match n with
        | O => m
        | S n' => S (add n' m)
        end.
    ```

### 4. **Proofs by Simplification**
- Proofs can be done interactively using tactics like `simpl` and `reflexivity`.
- Example:
    ```coq
    Theorem plus_O_n : forall n : nat, 0 + n = n.
    Proof.
        simpl. reflexivity.
    Qed.
    ```

### 5. **Inductive Types**
- Custom types can be defined using `Inductive`.
- Example: Defining a `day` type:
    ```coq
    Inductive day : Type :=
        | monday | tuesday | wednesday | thursday | friday | saturday | sunday.
    ```

### 6. **Pattern Matching**
- Used to destructure data types.
- Example:
    ```coq
    Definition is_weekend (d : day) : bool :=
        match d with
        | saturday | sunday => true
        | _ => false
        end.
    ```

### 7. **Proofs by Induction**
- Induction is used for proving properties about recursive structures.
- Example:
    ```coq
    Theorem add_0_r : forall n : nat, n + 0 = n.
    Proof.
        induction n as [| n' IHn'].
        - reflexivity.
        - simpl. rewrite IHn'. reflexivity.
    Qed.
    ```

---

## Summary

The `Basics.v` file introduces:
- Core data types (`bool`, `nat`, custom types).
- Function definitions and pattern matching.
- Proof techniques like simplification and induction.

These concepts form the foundation for programming and proving in Coq.

For more details, refer to the *Software Foundations* series.