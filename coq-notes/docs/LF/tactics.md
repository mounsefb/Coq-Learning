# Tactics in Coq

This document summarizes key concepts and tactics from the Software Foundations (SF) course, focusing on the `tactics.v` file.

## Basic Tactics

### `intros`
- Moves hypotheses or variables from the goal into the context.

### `reflexivity`
- Solves goals where both sides of the equation are identical.

### `apply`
- Uses a hypothesis, lemma, or theorem to prove the goal.

### `exact`
- Provides the exact term that matches the goal.

### `assumption`
- Solves the goal if it matches a hypothesis in the context.

## Structural Tactics

### `split`
- Breaks conjunctions (`A /\ B`) into separate subgoals.

### `left` / `right`
- Chooses a branch in a disjunction (`A \/ B`).

### `destruct`
- Performs case analysis on a term.

### `induction`
- Applies induction on a variable, generating base and inductive cases.

## Simplification Tactics

### `simpl`
- Simplifies computations in the goal.

### `rewrite`
- Replaces terms using equalities from hypotheses or lemmas.

### `unfold`
- Expands a defined term in the goal.

### `fold`
- Collapses a term back into its defined form.

## Logical Tactics

### `assert`
- Introduces an intermediate assertion to simplify proofs.

### `exists`
- Provides a witness to prove existential quantifiers (`exists x, P x`).

### `inversion`
- Analyzes equalities to extract information from constructors.

## Automation

### `auto`
- Attempts to solve goals using simple reasoning and existing hypotheses.

### `eauto`
- Extends `auto` with additional search capabilities.

### `repeat`
- Repeats a tactic until it fails.

### `try`
- Attempts a tactic but does not fail if the tactic does.

## Debugging

### `info_auto`
- Displays the steps taken by `auto`.

### `idtac`
- Prints custom messages for debugging.

---

This summary provides a foundation for understanding Coq tactics. Refer to the `tactics.v` file for detailed examples and exercises.