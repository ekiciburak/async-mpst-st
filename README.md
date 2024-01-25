# sessionTreeST
subtyping of asynchronous session trees

The library succesfully compiles with the Coq compiler `coqc 8.18.0`.

- `coq_makefile -f _CoqProject -o Makefile` to create the Makefile
- `make` to compile

# file organization
1. `stream.v` - definitions and a few lemmata on streams (infinite lists)
2. `st.v` - defines payload sorts, subsorts, negation of subsorts and session trees with a few rewrite lemma
3. `so.v` - contains single-output tree definition (SO) based on the greatest fixed point of least fixed point technique employing the `paco` library 
4. `si.v` - contains single-input tree definition (SI) based on the greatest fixed point of least fixed point technique employing the `paco` library 
5. `reordering.v` - defines action reorderings of sort  $A^{(p)}$ and  $B^{(p)}$
6. `siso.v` -  defines single-output-single-input trees (SISO) based on the greatest fixed point of least fixed point technique employing the `paco` library 
7. `refinement.v` - defines the SISO refinement relation based on the greatest fixed point of least fixed point technique employing the `paco` library 
8. `reorderingfacts.v` - contains some facts about the action reorderings $A^{(p)}$ and  $B^{(p)}$
9. `subtyping.v` - defines the subtyping relation 
10. `example1.v` - contains a proof of Example 3.9 in Ghilezan et al.
11. `example2.v` - contains a proof of Example 3.10 in Ghilezan et al. -- the one presented in this paper
12. `batchproc.v` -  contains a proof of the subtyping that appears in batch processing optimization example in Section 6 in Ghilezan et al.
13. `nrefinement.v` - defines the negation of the SISO refinement relation inductively proves the absurdity of having both $T \not\lesssim T'$ and $T \not\lesssim T'$ under the same context 

`Ghilezan et al.` $\to$ `Precise Subtyping for Asynchronous Multiparty Sessions [POPL 2021]`