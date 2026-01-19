# Async Session Subtyping

This repository contains a Coq mechanisation of **subtyping for asynchronous session types**, based on the theory of *asynchronous multiparty session types (MPSTs)*.  

The development formalises session trees, action reordering, refinement, subtyping, and their meta-theoretic properties, and includes mechanised proofs of representative examples from the literature.

---
## Dependencies
The mechanisation is known to compile with the following versions:
- **Rocq** 9.0.0
- **coq-equations** 1.3.1+8.20
- **coq-mathcomp-ssreflect** 2.5.0
- **coq-paco** 4.2.3

All dependencies can be installed via `opam`:
```sh
opam install \
  opam install rocq-prover.9.0.0 \
  coq-equations.1.3.1+8.20 \
  coq-mathcomp-ssreflect.2.5.0 \
  coq-paco.4.2.3
```
## Building the Development

From the root of the repository, run:
-  `rocq makefile -f _CoqProject -o Makefile` to create the Makefile
-  `make` to compile

This generates a Makefile and compiles the entire development.

## Repository Structure
The repository is organised as follows:

| |File |Description |
|---------------- |-------------------------------|-----------------------------|
1 | `src/stream.v` | definitions and a few lemmata on streams (infinite lists)
2 | `src/st.v` | defines payload sorts, subsorts, negation of subsorts and session trees with a few rewrite lemma, and implements the translation from types into trees
3 | `src/so.v` | contains single-output (SO) tree definition based on the greatest fixed point of least fixed point technique employing the `paco` library
4 | `src/si.v` | contains single-input (SI) tree definition
5 | `src/reordering.v` | defines action reorderings for dependently typed prefixes of sorts $A^{(p)}$, $B^{(p)}$ and $C^{(p)}$, and simply typed prefixes of sorts $A$, $B$ and $C$
6 | `src/siso.v` | defines single-output-single-input (SISO) trees and the siso decomposition of an arbitrary session tree
7 | `src/reorderingfacts.v` | contains some facts about the action reorderings for prefixes of sorts $A^{(p)}$, $B^{(p)}$ and $C^{(p)}$
8 | `src/acteqfacts.v` | contains some facts about translating dependently typed prefix types into simply typed ones
9 | `src/nondepro.v` | contains some facts about action reorderings for prefixes of sorts $A$, $B$, and $C$, as well as the transitivity of the refinement relation
10 | `src/inversion.v` | contains some facts about refinement relation inversions
11 | `src/projections.v` | defines SISO projections and proves the correctness of the refinement relation using these projections
12 | `subtyping/refinement.v` | defines the SISO refinement relations
13 | `subtyping/subtyping.v` | defines the subtyping relations
14 | `examples/ring_choice.v` | proves `ring-choice` protocol optimisation
15 | `examples/Example3_17.v` | proves `Example 3-17` in `[1]`
16 | `examples/Example3_18.v` | proves `Example 3-18` in `[1]`
17 | `examples/Example3_19.v` | proves `Example 3-19` in `[1]`
18 | `examples/Example4_14.v` | proves `Example 4-14` in `[1]`
19 | `negations/nrefinement.v` | defines the negation of the SISO refinement relation $\not\lesssim$ inductively proves $\neg (w \lesssim w') \iff w \not\lesssim w'$
20 | `negations/nsubtyping.v` | defines the negation of subtyping relation $\not\leqslant$
21 | `completeness/completeness.v` | proves completeness of subtyping with respect to negations: $\neg (T \leqslant T') \iff T \not\leqslant T'$

## References
[1] Ghilezan et al., Precise Subtyping for Asynchronous Multiparty Sessions [JLAMP 2023]

[2] Ekici B. and Yoshida N., Completeness of Asynchronous Session Tree Subtyping in Coq [ITP 2024]

