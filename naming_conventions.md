Naming Conventions
==================

TODO: we should also write up proof conventions, coding conventions

General conventions
-------------------

Identifiers are generally lower case with underscores. For the most
part, we rely on descriptive names. Often the name of theorem simply
describes the conclusion:

- `succ_ne_zero`
- `mul_zero`
- `mul_one`
- `sub_add_eq_add_sub`
- `le_iff_lt_or_eq`

If only a prefix of the description is enough to convey the meaning,
the name may be made even shorter:

- `neg_neg`
- `pred_succ`

Sometimes, to disambiguate the name of theorem or better convey the
intended reference, it is necessary to describe some of the
hypotheses. The word "of" is used to separate these hypotheses:

- `lt_of_succ_le`
- `lt_of_not_ge`
- `lt_of_le_of_ne`
- `add_lt_add_of_lt_of_le`

Sometimes abbreviations or alternative descriptions are easier to work
with. For example, we use `pos`, `neg`, `nonpos`, `nonneg` rather than
`zero_lt`, `lt_zero`, `le_zero`, and `zero_le`.

- `mul_pos`
- `mul_nonpos_of_nonneg_of_nonpos`
- `add_lt_of_lt_of_nonpos`
- `add_lt_of_nonpos_of_lt`

Sometimes the word "left" or "right" is helpful to describe variants
of a theorem.

- `add_le_add_left`
- `add_le_add_right`
- `le_of_mul_le_mul_left`
- `le_of_mul_le_mul_right`

We can also use the word "self" to indicate a repeated argument:

- `mul_inv_self`
- `neg_add_self`


Dots
----

Dots are used for namespaces, and also automatically generated names
like recursors, eliminators, strutures projections. They can also be
introduced manually, for example, where projector notation is
useful. Thus they are used in all the following situations.

Intro, elim, and destruct rules for logical connectives, whether they
are automatically generated or not:

- `and.intro`
- `and.elim`
- `and.left`
- `and.right`
- `or.inl`
- `or.inr`
- `or.intro_left`
- `or.intro_right`
- `iff.intro`
- `iff.elim`
- `iff.mp`
- `iff.mpr`
- `not.intro`
- `not.elim`
- `eq.refl`
- `eq.rec`
- `eq.subst`
- `heq.refl`
- `heq.rec`
- `heq.subst`
- `exists.intro`
- `exists.elim`
- `true.intro`
- `false.elim`

General intro, elim, destruct operations, for example:

- `dvd.intro`
- `dvd.dest`
- `dvd.elim`
- `lt.refl`

Places where projection notation is useful, for example:

- `and.symm`
- `or.symm`
- `or.resolve_left`
- `or.resolve_right`
- `eq.symm`
- `eq.trans`
- `heq.symm`
- `heq.trans`


Axiomatic descriptions
----------------------

Some theorems are described using axiomatic names, rather than
describing their conclusions.

- `def`  (for unfolding a definition)
- `refl`
- `irrefl`
- `symm`
- `trans`
- `antisymm`
- `asymm`
- `congr`
- `comm`
- `assoc`
- `left_comm`
- `right_comm`
- `mul_left_cancel`
- `mul_right_cancel`
- `inj`  (injective)


Variable conventions
--------------------

- `u`, `v`, `w`, ... for universes
- `α`, `β`, `γ`, ... for types
- `a`, `b`, `c`, ... for propositions
- `x`, `y`, `z`, ... for elements of a generic type
- `h`, `h₁`, ...     for assumptions
- `p`, `q`, `r`, ... for predicates and relations
- `s`, `t`, ...      for lists
- `s`, `t`, ...      for sets
- `m`, `n`, `k`, ... for natural numbers
- `i`, `j`, `k`, ... for integers


Names for symbols
-----------------

- `implies` : implication
- `forall`
- `exists`
- `bforall` : bounded forall
- `bexists` : bounded exists




Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
