# Formalizing the Semantics of a Classical-Quantum Imperative Language in Coq

## Overview


We define the syntax, small-step operational semantics and state-based denotational semantics of a classical-quantum imperative language. In addition, we prove the consistency of these two semantics.  
We lift the denotational semantics from states to distributions and relate the latter to the former. Furthermore, we formalize some practical quantum algorithms and use the distribution-based denotational semantics to prove their correctness.


We describe it in detail in [this draft](https://arxiv.org/pdf/2005.11023).


## Directory Contents

### src


Definitions and related theorems of language semantics


- src/com/QuantumLib/Complex.v : Complex number library, modified from Coquelicot, copid form Qwire(https://github.com/inQWIRE/QuantumLib)

- src/sym/Nat_notWF.v : Matrix library without WF assumptions and redefined matrix equivalence.
- src/sym/Nat_Dirac.v : Symbolic reasoning strategy library with Dirac notation.
- src/sym/Denotations.v : State-based denotational semantics.
- src/sym/Smallstep.v : Operational semantics and semantic equivalence.
- src/sym/Distribution.v : Distribution-based denotational semantics and related theorems.
- src/sym/Preparation.v : Some preparation.


Examples of verifying correctness properties of quantum algorithms.

- src/sym/Tele.v : Quantum teleportation.
- src/sym/Gro.v : Grover’s search algorithms.
- src/sym/Deu.v : Deutsch's algorithm.
- src/sym/Sim.v : Simon's algorithm.


