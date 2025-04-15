# sessionTreeST

subtyping of asynchronous session types

The library succesfully compiles with the Coq compiler `coqc 8.20.0`.
-  `coq_makefile -f _CoqProject -o Makefile` to create the Makefile
-  `make` to compile
 
| |File |Description |
|---------------- |-------------------------------|-----------------------------|
1 | `src/stream.v` | definitions and a few lemmata on streams (infinite lists)
2 | `src/st.v` | defines payload sorts, subsorts, negation of subsorts and session trees with a few rewrite lemma
3 | `src/so.v` | contains single-output (SO) tree definition based on the greatest fixed point of least fixed point technique employing the `paco` library
4 | `src/si.v` | contains single-input (SI) tree definition
5 | `src/reordering.v` | defines action reorderings for prefixes of sorts $A^{(p)}$, $B^{(p)}$ and $C^{(p)}$
6 | `src/siso.v` | defines single-output-single-input (SISO) trees and the siso decomposition of an arbitrary session tree
7 | `src/reorderingfacts.v` | contains some facts about the action reorderings for prefixes of sorts $A^{(p)}$, $B^{(p)}$ and $C^{(p)}$
8 | `subtyping/refinement.v` | defines the SISO refinement (and refinement2) relation(s)
9 | `subtyping/subtyping.v` | defines the subtyping (and subtyping2) relation(s)
10 | `examples/ring_choice.v` | proves `ring-choice` protocol optimisation
11 | `examples/Example3_17.v` | proves `Example 3-17` in `[1]`
12 | `examples/Example3_18.v` | proves `Example 3-18` in `[1]`
13 | `examples/Example3_19.v` | proves `Example 3-19` in `[1]`
14 | `examples/Example4_14.v` | proves `Example 4-14` in `[1]`
15 | `negations/nrefinement.v` | defines the negation of the SISO refinement relation $\not\lesssim$ inductively proves $\neg (w \lesssim w') \iff w \not\lesssim w'$
16 | `negations/nsubtyping.v` | defines the negation of subtyping relation $\not\leqslant$
17 | `completeness/completeness.v` | proves completeness of subtyping with respect to negations: $\neg (T \leqslant T') \iff T \not\leqslant T'$

`[1] Ghilezan et al., Precise Subtyping for Asynchronous Multiparty Sessions [JLAMP 2023]`
