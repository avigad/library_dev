/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Theory of complete lattices.
-/
import .basic .bounded_lattice

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w} {ι : Sort v}

namespace set

theorem subset_union_left (s t : set α) : s ⊆ s ∪ t := λ x H, or.inl H

theorem subset_union_right (s t : set α) : t ⊆ s ∪ t := λ x H, or.inr H

definition univ : set α := λx, true

end set

class has_Sup (α : Type u) := (Sup : set α → α)
class has_Inf (α : Type u) := (Inf : set α → α)
def Sup [has_Sup α] : set α → α := has_Sup.Sup
def Inf [has_Inf α] : set α → α := has_Inf.Inf

class complete_lattice (α : Type u) extends bounded_lattice α, has_Sup α, has_Inf α :=
(le_Sup : ∀s, ∀a∈s, a ≤ Sup s)
(Sup_le : ∀s a, (∀b∈s, b ≤ a) → Sup s ≤ a)
(Inf_le : ∀s, ∀a∈s, Inf s ≤ a)
(le_Inf : ∀s a, (∀b∈s, a ≤ b) → a ≤ Inf s)

def supr [complete_lattice α] (s : ι → α) : α := Sup {a : α | ∃i : ι, a = s i}
def infi [complete_lattice α] (s : ι → α) : α := Inf {a : α | ∃i : ι, a = s i}

notation `⨆` binders `, ` r:(scoped f, supr f) := r
notation `⨅` binders `, ` r:(scoped f, infi f) := r

section
open set
variables [complete_lattice α] {s t : set α} {a b : α}

lemma le_Sup : a ∈ s → a ≤ Sup s         := complete_lattice.le_Sup s a
lemma Sup_le : (∀b∈s, b ≤ a) → Sup s ≤ a := complete_lattice.Sup_le s a
lemma Inf_le : a ∈ s → Inf s ≤ a         := complete_lattice.Inf_le s a
lemma le_Inf : (∀b∈s, a ≤ b) → a ≤ Inf s := complete_lattice.le_Inf s a

lemma le_Sup_of_le (hb : b ∈ s) (h : a ≤ b) : a ≤ Sup s :=
le_trans h (le_Sup hb)

lemma Inf_le_of_le (hb : b ∈ s) (h : b ≤ a) : Inf s ≤ a :=
le_trans (Inf_le hb) h

lemma Sup_le_Sup (h : s ⊆ t) : Sup s ≤ Sup t :=
Sup_le (take a, assume ha : a ∈ s, le_Sup $ h ha)

lemma Inf_le_Inf (h : s ⊆ t) : Inf t ≤ Inf s :=
le_Inf (take a, assume ha : a ∈ s, Inf_le $ h ha)

lemma le_Sup_iff : Sup s ≤ a ↔ (∀b ∈ s, b ≤ a) :=
⟨suppose Sup s ≤ a, take b, suppose b ∈ s,
  le_trans (le_Sup ‹b ∈ s›) ‹Sup s ≤ a›,
  Sup_le⟩

lemma Inf_le_iff : a ≤ Inf s ↔ (∀b ∈ s, a ≤ b) :=
⟨suppose a ≤ Inf s, take b, suppose b ∈ s,
  le_trans ‹a ≤ Inf s› (Inf_le ‹b ∈ s›),
  le_Inf⟩

-- how to state this? instead a parameter `a`, use `∃a, a ∈ s` or `s ≠ ∅`?
lemma Inf_le_Sup (h : a ∈ s) : Inf s ≤ Sup s :=
Inf_le_of_le h (le_Sup h)

lemma Sup_union {s t : set α} : Sup (s ∪ t) = Sup s ⊔ Sup t :=
le_antisymm
  (Sup_le $ take a h, or.rec_on h (le_sup_left_of_le ∘ le_Sup) (le_sup_right_of_le ∘ le_Sup))
  (sup_le (Sup_le_Sup $ subset_union_left _ _) (Sup_le_Sup $ subset_union_right _ _))

lemma Sup_inter_le {s t : set α} : Sup (s ∩ t) ≤ Sup s ⊓ Sup t :=
Sup_le (take a ⟨a_s, a_t⟩, le_inf (le_Sup a_s) (le_Sup a_t))

lemma Inf_union {s t : set α} : Inf (s ∪ t) = Inf s ⊓ Inf t :=
le_antisymm
  (le_inf (Inf_le_Inf $ subset_union_left _ _) (Inf_le_Inf $ subset_union_right _ _))
  (le_Inf $ take a h, or.rec_on h (inf_le_left_of_le ∘ Inf_le) (inf_le_right_of_le ∘ Inf_le))

lemma le_Inf_inter {s t : set α} : Inf s ⊔ Inf t ≤ Inf (s ∩ t) :=
le_Inf (take a ⟨a_s, a_t⟩, sup_le (Inf_le a_s) (Inf_le a_t))

@[simp]
lemma Sup_empty : Sup ∅ = (bot : α) :=
le_antisymm (Sup_le (take _, false.elim)) bot_le

@[simp]
lemma Inf_empty : Inf ∅ = (top : α) :=
le_antisymm le_top (le_Inf (take _, false.elim))

@[simp]
lemma Sup_univ : Sup univ = (top : α) :=
le_antisymm le_top (le_Sup ⟨⟩)

@[simp]
lemma Inf_univ : Inf univ = (bot : α) :=
le_antisymm (Inf_le ⟨⟩) bot_le

@[simp]
lemma Sup_insert {a : α} {s : set α} : Sup (insert a s) = a ⊔ Sup s :=
have Sup {b | b = a} = a,
  from le_antisymm (Sup_le $ take b b_eq, b_eq ▸ le_refl _) (le_Sup rfl),
calc Sup (insert a s) = Sup {b | b = a} ⊔ Sup s : Sup_union
                  ... = a ⊔ Sup s : by rw [this]

@[simp]
lemma Inf_insert {a : α} {s : set α} : Inf (insert a s) = a ⊓ Inf s :=
have Inf {b | b = a} = a,
  from le_antisymm (Inf_le rfl) (le_Inf $ take b b_eq, b_eq ▸ le_refl _),
calc Inf (insert a s) = Inf {b | b = a} ⊓ Inf s : Inf_union
                  ... = a ⊓ Inf s : by rw [this]

@[simp]
lemma Sup_singleton {a : α} : Sup {a} = a :=
eq.trans Sup_insert $ by simp

@[simp]
lemma Inf_singleton {a : α} : Inf {a} = a :=
eq.trans Inf_insert $ by simp

lemma infi_const {β : Sort v} {a : α} (b : β) : (⨅ b:β, a) = a := 
le_antisymm (Inf_le ⟨b, rfl⟩) (le_Inf $ take a' ⟨b', h⟩, h^.symm ▸ le_refl _)

lemma supr_const {β : Sort v} {a : α} (b : β) : (⨆ b:β, a) = a := 
le_antisymm (Sup_le $ take a' ⟨b', h⟩, h^.symm ▸ le_refl _) (le_Sup ⟨b, rfl⟩)

end


/- supr & infi -/
section
open set
variables [complete_lattice α] {s t : ι → α} {a b : α}

lemma le_supr (s : ι → α) (i : ι) : s i ≤ supr s :=
le_Sup ⟨i, rfl⟩

lemma le_supr_of_le (i : ι) (h : a ≤ s i) : a ≤ supr s :=
le_trans h (le_supr _ i)

lemma supr_le (h : ∀i, s i ≤ a) : supr s ≤ a :=
Sup_le $ take b ⟨i, eq⟩, eq^.symm ▸ h i

lemma supr_le_supr (h : ∀i, s i ≤ t i) : supr s ≤ supr t :=
supr_le $ take i, le_supr_of_le i (h i)

lemma infi_le (s : ι → α) (i : ι) : infi s ≤ s i :=
Inf_le ⟨i, rfl⟩

lemma infi_le_of_le (i : ι) (h : s i ≤ a) : infi s ≤ a :=
le_trans (infi_le _ i) h

lemma le_infi (h : ∀i, a ≤ s i) : a ≤ infi s :=
le_Inf $ take b ⟨i, eq⟩, eq^.symm ▸ h i

lemma infi_le_infi (h : ∀i, s i ≤ t i) : infi s ≤ infi t :=
le_infi $ take i, infi_le_of_le i (h i)

lemma Inf_image {s : set β} {f : β → α} : Inf (set.image f s) = (⨅ a ∈ s, f a) := 
le_antisymm
  (le_infi $ take b, le_infi $ suppose b ∈ s, Inf_le ⟨b, ⟨this, rfl⟩⟩)
  (le_Inf $ take a ⟨b', ⟨in_s, eq_a⟩⟩, infi_le_of_le b' $ infi_le_of_le in_s $ le_of_eq eq_a)

lemma Sup_image {s : set β} {f : β → α} : Sup (set.image f s) = (⨆ a ∈ s, f a) := 
le_antisymm
  (Sup_le $ take a ⟨b', ⟨in_s, eq_a⟩⟩, le_supr_of_le b' $ le_supr_of_le in_s $ le_of_eq eq_a^.symm)
  (supr_le $ take b, supr_le $ suppose b ∈ s, le_Sup ⟨b, ⟨this, rfl⟩⟩)

@[simp]
lemma infi_false {x : α} : (⨅ h : false, x) = top :=
le_antisymm le_top (le_infi false.elim)

@[simp]
lemma supr_false {x : α} : (⨆ h : false, x) = bot :=
le_antisymm (supr_le false.elim) bot_le

@[simp]
lemma infi_empty {f : β → α} : (⨅ x ∈ (∅ : set β), f x) = top :=
le_antisymm le_top (le_infi $ take x, le_infi false.elim)

@[simp]
lemma supr_empty {f : β → α} : (⨆ x ∈ (∅ : set β), f x) = bot :=
le_antisymm (supr_le $ take x, supr_le false.elim) bot_le

@[simp]
lemma infi_univ {f : β → α} : (⨅ x ∈ (univ : set β), f x) = (⨅ x, f x) :=
show (⨅ (x : β) (H : true), f x) = ⨅ (x : β), f x,
  from congr_arg infi $ funext $ take x, infi_const ⟨⟩

@[simp]
lemma supr_univ {f : β → α} : (⨆ x ∈ (univ : set β), f x) = (⨆ x, f x) :=
show (⨆ (x : β) (H : true), f x) = ⨆ (x : β), f x,
  from congr_arg supr $ funext $ take x, supr_const ⟨⟩

@[simp]
lemma infi_union {f : β → α} {s t : set β} : (⨅ x ∈ s ∪ t, f x) = (⨅x∈s, f x) ⊓ (⨅x∈t, f x) :=
le_antisymm
  (le_inf
    (infi_le_infi $ take i, le_infi $ suppose i ∈ s, infi_le (λh, f i) (or.inl this))
    (infi_le_infi $ take i, le_infi $ suppose i ∈ t, infi_le (λh, f i) (or.inr this)))
  (le_infi $ take i, le_infi $ suppose i ∈ s ∪ t, match this with
   | or.inl _ := inf_le_left_of_le  $ infi_le_of_le i $ infi_le (λh, f i) ‹i∈s›
   | or.inr _ := inf_le_right_of_le $ infi_le_of_le i $ infi_le (λh, f i) ‹i∈t›
   end)

@[simp]
lemma supr_union {f : β → α} {s t : set β} : (⨆ x ∈ s ∪ t, f x) = (⨆x∈s, f x) ⊔ (⨆x∈t, f x) :=
le_antisymm
  (supr_le $ take i, supr_le $ suppose i ∈ s ∪ t, match this with
   | or.inl _ := le_sup_left_of_le  $ le_supr_of_le i $ le_supr (λh, f i) ‹i∈s›
   | or.inr _ := le_sup_right_of_le $ le_supr_of_le i $ le_supr (λh, f i) ‹i∈t›
   end)
  (sup_le
    (supr_le_supr $ take i, supr_le $ suppose i ∈ s, le_supr (λh, f i) (or.inl this))
    (supr_le_supr $ take i, supr_le $ suppose i ∈ t, le_supr (λh, f i) (or.inr this)))

@[simp]
lemma infi_insert {f : β → α} {s : set β} {b : β} : (⨅ x ∈ insert b s, f x) = f b ⊓ (⨅x∈s, f x) :=
have (⨅x ∈ {b_1 : β | b_1 = b}, f x) = f b,
  from le_antisymm
    (infi_le_of_le b $ infi_le _ rfl)
    (le_infi $ take b', le_infi $ take eq, eq ▸ le_refl (f b')),
eq.trans infi_union $ congr_arg (λx:α, x ⊓ (⨅x∈s, f x)) this

@[simp]
lemma supr_insert {f : β → α} {s : set β} {b : β} : (⨆ x ∈ insert b s, f x) = f b ⊔ (⨆x∈s, f x) :=
have (⨆x ∈ {b_1 : β | b_1 = b}, f x) = f b,
  from le_antisymm
    (supr_le $ take b', supr_le $ take eq, eq ▸ le_refl (f b'))
    (le_supr_of_le b $ le_supr (λh, f b) rfl),
eq.trans supr_union $ congr_arg (λx:α, x ⊔ (⨆x∈s, f x)) this

@[simp]
lemma infi_singleton {f : β → α} {b : β} : (⨅ x ∈ (singleton b : set β), f x) = f b :=
show (⨅ x ∈ insert b (∅ : set β), f x) = f b,
  by simp

@[simp]
lemma supr_singleton {f : β → α} {b : β} : (⨆ x ∈ (singleton b : set β), f x) = f b :=
show (⨆ x ∈ insert b (∅ : set β), f x) = f b,
  by simp

end

/- Instances -/

instance complete_lattice_Prop : complete_lattice Prop :=
{ bounded_lattice_Prop with 
  Sup    := λs, ∃a∈s, a,
  le_Sup := take s a h p, ⟨a, h, p⟩,
  Sup_le := take s a h ⟨b, h', p⟩, h b h' p,
  Inf    := λs, ∀a∈s, a,
  Inf_le := take s a h p, p a h,
  le_Inf := take s a h p b hb, h b hb p }

instance complete_lattice_fun {α : Type u} {β : Type v} [complete_lattice β] :
  complete_lattice (α → β) :=
{ bounded_lattice_fun with 
  Sup    := λs a, Sup (set.image (λf : α → β, f a) s),
  le_Sup := take s f h a, le_Sup ⟨f, h, rfl⟩,
  Sup_le := take s f h a, Sup_le $ take b ⟨f', h', b_eq⟩, b_eq ▸ h _ h' a,
  Inf    := λs a, Inf (set.image (λf : α → β, f a) s),
  Inf_le := take s f h a, Inf_le ⟨f, h, rfl⟩,
  le_Inf := take s f h a, le_Inf $ take b ⟨f', h', b_eq⟩, b_eq ▸ h _ h' a }

section complete_lattice
variables [weak_order α] [complete_lattice β]

lemma monotone_Sup_of_monotone {s : set (α → β)} (m_s : ∀f∈s, monotone f) : monotone (Sup s) :=
take x y h, Sup_le $ take x' ⟨f, f_in, fx_eq⟩, le_Sup_of_le ⟨f, f_in, rfl⟩ $ fx_eq ▸ m_s _ f_in h

lemma monotone_Inf_of_monotone {s : set (α → β)} (m_s : ∀f∈s, monotone f) : monotone (Inf s) :=
take x y h, le_Inf $ take x' ⟨f, f_in, fx_eq⟩, Inf_le_of_le ⟨f, f_in, rfl⟩ $ fx_eq ▸ m_s _ f_in h

end complete_lattice
