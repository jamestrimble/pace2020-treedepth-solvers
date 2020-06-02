# Exact Treedepth Solvers: Bute, Bute-Plus and Bute-Plus-Plus

These directories contain three variants of the Bute solver.  The name
is from the [Isle of Bute](https://en.wikipedia.org/wiki/Isle_of_Bute), and also 
as an almost-acronym for the solvers' bottom-up approach to constructing
an elimination tree.

The optimisation problem is solved as a sequence of decision problems;
`solve()` is called for each of these problems, with `target` being
the sought depth of an elimination tree.

The function `solve()` works upwards from the `target` depth to depth
1 (the root), finding all subtrees that could be rooted at the depth
in an elimination tree of depth `target`.  Each of these subtrees
is stored as a set of vertices (these are called `leafysets` in the
code, but this terminology should probably be improved!).  To find subtrees
rooted at depth `d`, the function `make_leafysets_helper` looks for 
subtrees rooted at depth `d+1` that could have a common parent in an
elimination tree.  A specialised trie data structure, which will be described
in more detail in a soon-to-be-written paper, helps to make this search
fast.

Bute-Plus runs a variant of the Tweed-Plus heuristic (see the
`../heuristic-solvers` directory) for one minute to try to find
an elimination tree of the optimum depth, then runs the Bute algorithm
to prove optimality.  This seems to be quite effective, as Bute seems
to struggle more with finding an elimination tree of depth *treedepth(G)*
than with proving that there is no elimination tree of depth *treedepth(G) - 1*.

Bute-Plus-Plus is a minor variant on Bute-Plus.  It runs the heuristic for
two minutes rather than one, and sometimes avoids an O(n) operation
in a frequently-called function.

## Input and Output Formats

The input and output formats are as described on the
[PACE Challenge site](https://pacechallenge.org/2020/td/#appendix-a-input-format-for-both-tracks).
The programs read only from standard input.

**Please note** that the solvers may give an incorrect answer if the input graph is not connected.

## Dependencies

Bute has no dependencies.

Bute-Plus and Bute-Plus-Plus use code from [Nauty](https://users.cecs.anu.edu.au/~bdm/nauty/)
2.6r12 for the bitset data structure and random number generator (the latter of which
is based in turn on Knuth's code).  The Nauty files are already in this repository and
there is no need to download them.

Bute-Plus and Bute-Plus-Plus use [Metis](http://glaros.dtc.umn.edu/gkhome/metis/metis/download) 5.1.0 
(SHA256: 76faebe03f6c963127dbb73c13eab58c9a3faeae48779f049066a21c087c5db2) to find a nested dissection ordering during
the heuristic presolve.  It is necessary to download and build Metis (hopefully `make config` then `make`
will be sufficient), then copy the file `build/*/libmetis/libmetis.a` from the Metis directory
to the directory of the treedepth solver.  The headers from Metis (`metis.h` and `struct.h`)
are already in this repository.
