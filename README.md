# Quantum Computing in Lean

This is an implementation of the theory of quantum computing in the Lean programming language (using the Lean theorem prover version 3).

It's built on top of the "mathlib" library written by the Lean Community.


## Organization

### The `src` directory

* `common_lemmas.lean`: Contains lemmas that are not specific to complex matrix or quantum computing.

* `matrix.lean`: Matrix-related definitions, notably `Matrix` and `kron` (the Kronecker product).

  * The `Matrix` type is defined based on the mathlib's `matrix` type, but specialized for complex number and the `fin` range type.

* `matrix_lemmas.lean`: Derived facts from the definitions in the `matrix.lean` file.

* `matrix_inner_product.lean`: The `inner_product_space` instantiation for the `Matrix` type.

* `quantum.lean`: Definitions for quantum computing, such as measurements and basic states and circuits.

* `quantum_lemmas.lean`: Derived facts from the definitions in the `quantum.lean` file.


### The `src/theorems` directory

* `no-clone.lean`: Several different versions of the "No-clone" theorem.


## Reference materials

* Tutorial: Quantum Programming: https://sites.google.com/ncsu.edu/qc-tutorial/home

* An Introduction to Quantum Computing, Without the Physics : https://arxiv.org/abs/1708.03684

* The "Verified Quantum Computing" book: https://www.cs.umd.edu/~rrand/vqc/


## Related project

* Lean: https://leanprover.github.io

* Lean Community: https://leanprover-community.github.io

* QWIRE: https://github.com/inQWIRE/QWIRE
  * "A quantum circuit language and formal verification tool" by Robert Rand et al.
