# Heuristic Treedepth Solvers: Tweed and Tweed-Plus

The solver Tweed (named after the [cloth](https://en.wikipedia.org/wiki/Tweed)) tries using two
classic heuristics for finding elimination trees: (something very similar to) the minimum degree algorithm
and nested dissection.  For nested dissection, the solver calls the Metis library to find an ordering of vertices.  

The solver tries each of these two approaches multiple times using different seeds for the random
number generators.  In addition, it uses the following approach to try to improve an elimination tree.
First, a subtree containing a vertex of maximum depth is found.  Then, either the minimum degree algorithm
or nested dissection is used to try to find a better elimination tree for the subgraph of the graph induced
by the vertices in that subtree.

Tweed-Plus is, in fact, Tweed *minus* the function `new_improve_solution()`.  I am not convinced that this
function is useful in practice, and it is badly written, so my hope is that Tweed-Plus can become the
default version of this program!

The programs are designed to be run for at least 30 minutes per instance.  After 28 minutes, the programs
attempt to improve upon the best solution found so far.

## Input and Output Formats

The input and output formats are as described on the
[PACE Challenge site](https://pacechallenge.org/2020/td/#appendix-a-input-format-for-both-tracks).
The programs read only from standard input.

**Please note** that the solvers may give an incorrect answer if the input graph is not connected.

The programs will output a solution shortly after receiving a SIGTERM signal.

## Dependencies

Both solvers use code from:

* [Nauty](https://users.cecs.anu.edu.au/~bdm/nauty/)
2.6r12 for the bitset data structure and random number generator (the latter of which
is based in turn on Knuth's code).  The Nauty files are already in this repository and
there is no need to download them.

* [Metis](http://glaros.dtc.umn.edu/gkhome/metis/metis/download) 5.1.0 
(SHA256: 76faebe03f6c963127dbb73c13eab58c9a3faeae48779f049066a21c087c5db2) to find a nested dissection ordering.
There are a few steps to get this working with Tweed and Tweed-Plus:

1. Download and extract Metis 5.1.0.
2. Copy `disable_metis_sigterm_handing.sh` into the root directory of Metis and run the script.  This
ensures that Metis does not catch SIGTERM.
3. Build Metis (hopefully `make config` then `make`
will be sufficient)
4. Copy the file `build/*/libmetis/libmetis.a` from the Metis directory
to the directory of the treedepth solver.

The required headers from Metis (`metis.h` and `struct.h`) are already in this repository, so there is no need to copy them.
