We study Wiedijk's toy model of Mizar's soft type system, by formalizing
it in Coq.

The basic components are:
1. The syntactic encoding of soft types, and the inductive definition of
   well-typedness for soft types.
2. An encoding of first-order logic using locally nameless variables.
3. A translation of soft-types into first-order logic.
4. The results concerning correctness.

# License

Everything is under the MIT License.

# References

- F. Wiedijk, "Mizar's Soft Type System."
  In: K. Schneider & J. Brandt (eds.),
  _Theorem Proving in Higher Order Logics 2007_, LNCS 4732, 383-399, 2007.
  [Eprint](http://www.cs.ru.nl/F.Wiedijk/mizar/miztype.pdf).

## First-order logic encodings

- Andreas Halkjær From,
  "Formalized First-Order Logic".
  PhD Thesis, 2007; [Eprint](https://people.compute.dtu.dk/ahfrom/Formalized%20First-Order%20Logic.pdf)
- Olivier Laurent,
  "An Anti-Locally-Nameless Approach to Formalizing Quantifiers".
  [Eprint](https://hal.archives-ouvertes.fr/hal-03096253)
