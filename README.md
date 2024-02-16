# sessionTreeST
subtyping of asynchronous session trees

The library succesfully compiles with the Coq compiler `coqc 8.18.0`.

- `coq_makefile -f _CoqProject -o Makefile` to create the Makefile
- `make` to compile

# file organization
1. `src/stream.v` - definitions and a few lemmata on streams (infinite lists)
2. `src/st.v` - defines payload sorts, subsorts, negation of subsorts and session trees with a few rewrite lemma
3. `src/so.v` - contains single-output tree definition (SO) based on the greatest fixed point of least fixed point technique employing the `paco` library 
4. `src/si.v` - contains single-input tree definition (SI) based on the greatest fixed point of least fixed point technique employing the `paco` library 
5. `src/reordering.v` - defines action reorderings of sort  $A^{(p)}$ and  $B^{(p)}$
6. `src/siso.v` -  defines single-output-single-input trees (SISO) based on the greatest fixed point of least fixed point technique employing the `paco` library 
7. `src/refinement.v` - defines the SISO refinement relation based on the greatest fixed point of least fixed point technique employing the `paco` library 
8. `src/reorderingfacts.v` - contains some facts about the action reorderings $A^{(p)}$ and  $B^{(p)}$
9. `src/subtyping.v` - defines the subtyping relation 
10. `src/nrefinement.v` - defines the negation of the SISO refinement relation inductively proves the absurdity of having both $T \not\lesssim T'$ and $T \not\lesssim T'$ under the same context 
11. `src/nsubtyping.v` -  defines the negation of subtyping $\not\leqslant$ relation and proves the absurdity of having both $T \leqslant T'$ and $T \not\leqslant T'$ under the same context
13. `src/nsubtyping.v` - proves completeness of subtyping with respect to negations

`Ghilezan et al.` $\to$ `Precise Subtyping for Asynchronous Multiparty Sessions [POPL 2021]`
