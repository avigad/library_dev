Naming Conventions
==================

NOTE: These are all open to negotiation!

TODO: we should also write up proof conventions, coding conventions

We have not yet settled on conventions for capitalization, snake_case, etc.

In the meanwhile, I am favoring lower case for elements of `Prop` and functions
that return elements of `Prop`, even variables.

Use periods *only* for namespaces and system-defined identifiers
(like `.rec` and `.mk`). So we would have

- `not_intro`
- `not_elim`
- `iff_intro`
- `ne_elim`

and so on. I would suggest also defining `and_intro` as an alias for
`and.intro`, etc.


Axiomatic descriptions
----------------------

- `refl`
- `irrefl`
- `symm`
- `trans`
- `antisymm`
- `asymm`

- `congr`: for congruences

- `comm`
- `assoc`
- `left_comm`
- `distrib`  (specify ops only as needed: and_distrib, mul_sub_distrib)
- `distrib_right`
- `inj` : injective



Variable conventions
--------------------

- `A`, `B`, `C`, ... for types
- `a`, `b`, `c`, ... for propositions
- `x`, `y`, `z`, ... for elements of a generic type
- `h`, `h₁`, ...     for assumptions
- `p`, `q`, `r`, ... for predicates and relations
- `s`, `t`, `u`, ... for lists
- `s`, `t`, `u`, ... for sets
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