# Logic in Coq

This document summarizes key concepts from the `logic.v` file in the Software Foundations (SF) Coq course.

## Propositions and Proofs

- **Propositions**: Logical statements that can be true or false.
- **Proofs**: Evidence that a proposition is true, constructed in Coq using tactics.

## Logical Connectives

### Conjunction (`/\`)
- Represents "and".
- Example: `P /\ Q` means both `P` and `Q` are true.
- Proof involves proving both `P` and `Q`.

### Disjunction (`\/`)
- Represents "or".
- Example: `P \/ Q` means either `P` or `Q` (or both) are true.
- Proof involves proving at least one of `P` or `Q`.

### Implication (`->`)
- Represents "if-then".
- Example: `P -> Q` means if `P` is true, then `Q` must also be true.
- Proof involves assuming `P` and deriving `Q`.

### Negation (`~`)
- Represents "not".
- Example: `~P` means `P` is not true.
- Defined as `P -> False`.

### Falsehood (`False`)
- Represents a contradiction.
- Cannot be proven.

### Truth (`True`)
- Always true.
- Requires no proof.

## Quantifiers

### Universal Quantification (`forall`)
- Example: `forall x, P(x)` means `P(x)` is true for all `x`.
- Proof involves showing `P(x)` holds for an arbitrary `x`.

### Existential Quantification (`exists`)
- Example: `exists x, P(x)` means there exists an `x` such that `P(x)` is true.
- Proof involves providing a specific `x` and showing `P(x)` holds.

## Proof Techniques

- **Introduction**: Used to introduce assumptions or break down logical connectives.
- **Elimination**: Used to extract information from assumptions.
- **Case Analysis**: Used for disjunctions or inductive types.
- **Contradiction**: Used to prove `False` and derive negations.

## Classical vs Constructive Logic

- **Constructive Logic**: Proofs must constructively demonstrate truth.
- **Classical Logic**: Allows reasoning with the law of excluded middle (`P \/ ~P`).

## Examples

### Conjunction Example
```coq
Theorem and_example : forall P Q : Prop, P /\ Q -> Q /\ P.
Proof.
    intros P Q [HP HQ].
    split; assumption.
Qed.
```

### Disjunction Example
```coq
Theorem or_example : forall P Q : Prop, P -> P \/ Q.
Proof.
    intros P Q HP.
    left. assumption.
Qed.
```

### Negation Example
```coq
Theorem not_example : forall P : Prop, ~P -> (P -> False).
Proof.
    intros P HNP HP.
    apply HNP. assumption.
Qed.
```

This document provides a concise overview of logical reasoning in Coq. For more details, refer to the `logic.v` file in the Software Foundations course.