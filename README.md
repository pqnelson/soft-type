We study Wiedijk's toy model of Mizar's soft type system, by formalizing
it in Coq.

The basic components are:
1. The syntactic encoding of soft types, and the inductive definition of
   well-typedness for soft types.
2. An encoding of first-order logic using locally nameless variables.
3. A translation of soft-types into first-order logic.
4. The results concerning correctness.

I'm basically doing something like test-driven coding in Coq, where the
`Example` environment is used for tests.

## Status

**tl;dr: the results in Wiedijk's paper is correct.** (That was
exciting, wasn't it?)

It turns out that Wiedijk's model is more or less correct. There's some
subtlety in the second typing rule, which is a contraction of a couple
rules in the version presented here (substitution and assumption). We
can derive the contentious rule as a theorem in our model, so it's fine.

There are some tedious theorems left to be proven, which are true but
whose proof is...long and uninteresting. So if you believe them, then
the model is correct.

I may or may not finish them, they won't be terribly insightful.

## Future directions

It may be interesting to add structure types, or prove completeness.

- It is easy to state completeness, but I expect it unpleant to prove:

  ```coq
  Theorem completeness : forall Γ Δ J,
      well_typed (Γ ;; Δ |- CorrectContext) ->
      proves (translate (Γ ;; Δ |- J)) ->
      well_typed (Γ ;; Δ |- J).
  ```

  The trick would be to assemble a library of theorems about well-typed
  judgements, analogous to the library of theorems concerning natural
  deduction in `Logic.v`.
- If you want to actually **use** this library, you would need to
  develop useful results in the `SoftType.v` file concerning
  `well_typed` judgements.
- Structure types in Mizar can be thought of either as a finite set of
  key-value pairs, or as a finite partial map. (From the set theoretic
  perspective, they're equivalent.) You'd need to sketch out some typing
  rule for them.

# License

Everything is under the MIT License.

# References

- F. Wiedijk, "Mizar's Soft Type System."
  In: K. Schneider & J. Brandt (eds.),
  _Theorem Proving in Higher Order Logics 2007_, LNCS 4732, 383-399, 2007.
  [Eprint](http://www.cs.ru.nl/F.Wiedijk/mizar/miztype.pdf).

## First-order logic encodings

A lot of the inspiration for encoding natural deduction comes from
Daniel Schepler's
[coq-sequent-calculus](https://github.com/dschepler/coq-sequent-calculus).
For locally nameless encoding and first-order logic considerations, I
consulted (among the random books in my bookcase):

- Andreas Halkjær From,
  "Formalized First-Order Logic".
  PhD Thesis, 2007; [Eprint](https://people.compute.dtu.dk/ahfrom/Formalized%20First-Order%20Logic.pdf)
- Olivier Laurent,
  "An Anti-Locally-Nameless Approach to Formalizing Quantifiers".
  [Eprint](https://hal.archives-ouvertes.fr/hal-03096253)
