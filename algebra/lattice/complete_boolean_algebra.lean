/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Theory of complete Boolean algebras.
-/
import .complete_lattice .boolean_algebra

universes u v w
variables {α : Type u} {β : Type v} {ι : Sort w}

namespace lattice
open lattice

class complete_distrib_lattice α extends complete_lattice α :=
  (sup_Inf : ∀a s, a ⊔ Inf s = (⨅ b ∈ s, a ⊔ b))
  (inf_Sup : ∀a s, a ⊓ Sup s = (⨆ b ∈ s, a ⊓ b))



class complete_boolean_algebra α extends boolean_algebra α, complete_distrib_lattice α


end lattice
