# Summary of Concepts from `lists.v`

This document summarizes key concepts from the `lists.v` file in the Software Foundations Coq course.

## 1. Introduction to Lists
- **Definition**: A list is a sequence of elements of the same type.
- **Syntax**:
    ```coq
    Inductive list (X : Type) : Type :=
    | nil : list X
    | cons : X -> list X -> list X.
    ```
    - `nil`: Represents an empty list.
    - `cons`: Constructs a list by adding an element to the front.

## 2. Basic List Operations
- **`length`**: Computes the number of elements in a list.
    ```coq
    Fixpoint length {X : Type} (l : list X) : nat :=
        match l with
        | nil => 0
        | cons _ t => 1 + length t
        end.
    ```

- **`app` (append)**: Concatenates two lists.
    ```coq
    Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
        match l1 with
        | nil => l2
        | cons h t => cons h (app t l2)
        end.
    ```

## 3. List Notation
- **Standard Notation**:
    - `[]`: Empty list.
    - `x :: xs`: Cons operator.
    - `[x; y; z]`: Shorthand for `x :: y :: z :: []`.

## 4. Theorems and Proofs
- **Associativity of `app`**:
    ```coq
    Theorem app_assoc : forall X (l1 l2 l3 : list X),
        app l1 (app l2 l3) = app (app l1 l2) l3.
    ```
    - Proof involves induction on `l1`.

- **Length of `app`**:
    ```coq
    Theorem app_length : forall X (l1 l2 : list X),
        length (app l1 l2) = length l1 + length l2.
    ```

## 5. Polymorphism
- Lists in Coq are polymorphic, allowing elements of any type:
    - Example: `list nat`, `list bool`, etc.

## 6. Higher-Order Functions
- **`map`**: Applies a function to each element of a list.
    ```coq
    Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
        match l with
        | nil => nil
        | cons h t => cons (f h) (map f t)
        end.
    ```

- **`filter`**: Filters elements of a list based on a predicate.
    ```coq
    Fixpoint filter {X : Type} (test : X -> bool) (l : list X) : list X :=
        match l with
        | nil => nil
        | cons h t => if test h then cons h (filter test t) else filter test t
        end.
    ```

## 7. List Membership
- **`In`**: Checks if an element exists in a list.
    ```coq
    Fixpoint In {X : Type} (x : X) (l : list X) : Prop :=
        match l with
        | nil => False
        | cons h t => h = x \/ In x t
        end.
    ```

## 8. Exercises
- Practice exercises in `lists.v` include:
    - Proving properties of `length`, `app`, and `map`.
    - Working with `filter` and `In`.

## Conclusion
The `lists.v` file introduces fundamental concepts of lists in Coq, including their definition, operations, and associated theorems. Mastery of these concepts is essential for reasoning about data structures in Coq.
