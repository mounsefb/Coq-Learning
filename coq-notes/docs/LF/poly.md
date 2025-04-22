# Polymorphism in Coq

This document summarizes key concepts from `poly.v`, part of the Software Foundations Coq course.

## Polymorphic Functions and Types

### Polymorphic Lists
- Coq supports polymorphic data types, such as `list`, which can hold elements of any type.
- Example definition:
    ```coq
    Inductive list (X : Type) : Type :=
    | nil : list X
    | cons : X -> list X -> list X.
    ```
- `X` is a type parameter, making `list` polymorphic.

### Polymorphic Functions
- Functions can also be polymorphic, operating on any type.
- Example: `length` function for lists:
    ```coq
    Fixpoint length {X : Type} (l : list X) : nat :=
        match l with
        | nil => 0
        | cons _ t => 1 + length t
        end.
    ```

## Higher-Order Functions
- Functions that take other functions as arguments or return functions as results.
- Example: `map` function applies a function to each element of a list:
    ```coq
    Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
        match l with
        | nil => nil
        | cons h t => cons (f h) (map f t)
        end.
    ```

## Type Inference and Annotations
- Coq can often infer types, but explicit annotations can improve readability and debugging.
- Example:
    ```coq
    Definition id {X : Type} (x : X) : X := x.
    ```

## Exercises and Proofs
- `poly.v` includes exercises to practice reasoning about polymorphic functions and proving properties about them.
- Example proof: `map` preserves list length:
    ```coq
    Theorem map_length : forall (X Y : Type) (f : X -> Y) (l : list X),
        length (map f l) = length l.
    Proof.
        intros X Y f l. induction l as [| h t IH].
        - reflexivity.
        - simpl. rewrite IH. reflexivity.
    Qed.
    ```

## Key Takeaways
- Polymorphism allows for reusable and generic definitions.
- Higher-order functions enable powerful abstractions.
- Coq's type system ensures correctness through proofs.

For more details, refer to the `poly.v` file in the Software Foundations course.