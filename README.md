# Quantum Computing in Lean

This is an implementation of the theory of quantum computing in the Lean programming language (using the Lean theorem prover version 3).

It's built on top of the "mathlib" library written by the Lean Community.


## Organization

### The [src](src) directory

* [common_lemmas.lean](src/common_lemmas.lean): Contains lemmas that are not specific to complex matrix or quantum computing.

* [matrix_inner_product.lean](src/matrix_inner_product.lean): The `inner_product_space` instantiation for the `matrix` type.

* [matrix.lean](src/matrix.lean): Matrix-related definitions, notably `Matrix` and `kron` (the Kronecker product).

  * The `Matrix` type is defined based on the mathlib's `matrix` type, but specialized for complex number and the `fin` range type.

* [matrix_lemmas.lean](src/matrix_lemmas.lean): Derived facts from the definitions of `Matrix`, `kron` and `adjoint`.

* [quantum.lean](src/quantum.lean): Definitions for quantum computing, such as measurements and basic states and circuits.

* [quantum_lemmas.lean](src/quantum_lemmas.lean): Derived facts from the definitions in the [quantum.lean](src/quantum.lean) file.

* [measurement.lean](src/measurement.lean): More generalized definitions of measurements and theorems about them.


### The [src/theorems](src/theorems) directory

* [no-clone.lean](theorems/no-clone.lean): Several different versions of the "No-clone" theorem.

* [random-number-generator.lean](random-number-generator.lean): A few examples of Hadamard gates.


## Reference materials

* Tutorial: Quantum Programming: https://sites.google.com/ncsu.edu/qc-tutorial/home

* An Introduction to Quantum Computing, Without the Physics : https://arxiv.org/abs/1708.03684

* The "Verified Quantum Computing" book: https://www.cs.umd.edu/~rrand/vqc/


## Related project

* Lean: https://leanprover.github.io

* Lean Community: https://leanprover-community.github.io

* QWIRE: https://github.com/inQWIRE/QWIRE
  * "A quantum circuit language and formal verification tool" by Robert Rand et al.
