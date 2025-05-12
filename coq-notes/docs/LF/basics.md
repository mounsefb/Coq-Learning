# Basics in Coq

This document summarizes the key concepts from the `Basics.v` file in the *Software Foundations* series, which introduces fundamental Coq programming concepts.

## Introduction to Coq

Coq is a proof assistant based on dependent type theory. It allows us to write functional programs, specify properties, and prove them formally.

---

## Key Concepts

### 1. **Defining Functions and Values**
- Functions are defined using the `Definition` keyword.
- Example:
```
    Definition plus_two (n : nat) : nat := n + 2.
```

### 2. **Booleans**
- Coq provides a `bool` type with two values: `true` and `false`.
- Boolean functions can be defined using pattern matching:
```
    Definition negb (b : bool) : bool :=
        match b with
        | true => false
        | false => true
        end.
```
Pattern matching can be defined in this case as : b either match true or false.


### 3. **Numbers**
- Coq includes a `nat` type for natural numbers.
- Constructors:
    - `O` for zero.
    - `S` for the successor function (e.g., `S O` is 1, `S (S O)` is 2).
- Example of addition:
```
    Fixpoint add (n m : nat) : nat :=
        match n with
        | O => m
        | S n' => S (add n' m)
        end.
```

### 4. **Proofs by Simplification**
- Proofs can be done interactively using tactics like `simpl` and `reflexivity`.
- Example:
```
    Theorem plus_O_n : forall k : nat, 0 + k = k.
    Proof.
        simpl. reflexivity.
    Qed.
```
In this case, simpl tactic will simplify 0 + k based on the construction of add. i.e add 0 k, n match O so the function returns k. simpl tactic can simplify this operation itself.
Then when two operands are equal, it means we proved the theorem. Reflexivity tactic puts an end to the proof.  


### 5. **Inductive Types**
- Custom types can be defined using `Inductive`.
- Example: Defining a `day` type:
```
    Inductive day : Type :=
        | monday | tuesday | wednesday | thursday | friday | saturday | sunday.
```
day is a new data type, and any variable of type day can have one of the values: monday, tuesday, wednesday, etc.

### 6. **Pattern Matching**
- Used to destructure data types.
- Example:
```
    Definition is_weekend (d : day) : bool :=
        match d with
        | saturday | sunday => true
        | _ => false
        end.
```

### 7. **Fixpoint Functions**
- Recursive functions, needs to explicitly call back the function
- Example :
```
    Fixpoint plus (n : nat) (m : nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.
```

---

## Useful Content List :

### Inductive Types 
```
Inductive bool : Type :=
  | true
  | false.
```
```
Inductive nat : Type :=
  | O
  | S (n : nat).
```
```
Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).
```

### Functions


### Notations
- Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
- Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
- Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.
- Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
- Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
- Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.
- Notation "x !& y" := (nandb x y) (at level 40, left associativity).
- Notation "x && y" := (andb x y).
- Notation "x || y" := (orb x y).


### Proven Theorems
- zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
- andb_commutative :
  forall b c, andb b c = andb c b.
- identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
- negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
- andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
- andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
- plus_O_n : forall n : nat, 0 + n = n.
- plus_1_l : forall n:nat, 1 + n = S n.
- mult_0_l : forall n:nat, 0 * n = 0.
- plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.
- mult_n_0_m_0 : forall p q : nat,
  (p * 0) + (q * 0) = 0.
- mult_n_1 : forall p : nat,
  p * 1 = p.
- plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.

## Summary

The `Basics.v` file introduces:
- Core data types (`bool`, `nat`, custom types).
- Function definitions, recursive functions and pattern matching.
- Proof techniques like simplification and induction.

These concepts form the foundation for programming and proving in Coq.

For more details, refer to the *Software Foundations* series.