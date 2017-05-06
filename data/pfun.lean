import data.set ..data.set.basic

universes u v w

structure pfun (α : Type u) (β : Type v) : Type (max u v) :=
(dom : set α)
(fn : Π x, dom x → β)

infixr ` →. `:25 := pfun

namespace pfun
variables {α : Type u} {β : Type v} {γ : Type w}

def eval_opt {β : Type v} (f : α →. β) [decidable_pred (dom f)] (x : α) : option β :=
if h : dom f x then some (f.fn x h) else none

protected def ext : Π {f g : α →. β}
  (H1 : ∀x, x ∈ dom f ↔ x ∈ dom g)
  (H2 : ∀x p q, f.fn x p = g.fn x q), f = g
| ⟨df, f⟩ ⟨dg, g⟩ H1 H2 := have t : df = dg, from set.ext H1,
  by cases t; rw [show f = g, from funext $ λx, funext $ λp, H2 x p p]

def as_subtype (f : α →. β) (s : {x // f.dom x}) : β := f.fn s.1 s.2

protected def lift (f : α → β) : α →. β := ⟨set.univ, λx _, f x⟩ 

instance : has_coe (α → β) (α →. β) := ⟨pfun.lift⟩

def graph (f : α →. β) : set (α × β) := λ ⟨a, b⟩, ∃ ha, f.fn a ha = b

def ran (f : α →. β) : set β := {b | ∃a, (a, b) ∈ f.graph}

def restrict (f : α →. β) {p : set α} (H : p ⊆ f.dom) : α →. β :=
⟨p, λx h, f.fn x (H h)⟩

theorem dom_iff_graph (f : α →. β) (x : α) : x ∈ f.dom ↔ ∃y, (x, y) ∈ f.graph :=
⟨λh, ⟨f.fn x h, h, rfl⟩, λ⟨y, h, _⟩, h⟩

protected def pure (x : β) : α →. β := pfun.lift (λy, x)

protected def bind (f : α →. β) (g : β → α →. γ) : α →. γ :=
⟨λa, ∃b: dom f a, (g (f.fn a b)).dom a, λa ha,
(g (f.fn a (exists.elim ha $ λh _, h))).fn a (exists.elim ha $ λ_ h, h)⟩ 

instance : monad (pfun α) :=
{ pure := @pfun.pure _,
  bind := @pfun.bind _,
  id_map := λβ f, pfun.ext (λa, ⟨λ⟨h, _⟩, h, λh, ⟨h, trivial⟩⟩) (λ_ _ _, rfl),
  pure_bind := λβ γ x f, pfun.ext (λa, ⟨λ⟨_, h⟩, h, λh, ⟨trivial, h⟩⟩) (λ_ _ _, rfl),
  bind_assoc := λβ γ δ f g k, pfun.ext (λa, ⟨λ⟨⟨h1, h2⟩, h3⟩, ⟨h1, h2, h3⟩, λ⟨h1, h2, h3⟩, ⟨⟨h1, h2⟩, h3⟩⟩) (λ_ _ _, rfl) }

theorem pure_defined (p : set α) (x : β) : p ⊆ (@pfun.pure α _ x).dom := set.subset_univ p

theorem bind_defined {α : Type u} {β γ : Type v} (p : set α) {f : α →. β} {g : β → α →. γ}
  (H1 : p ⊆ f.dom) (H2 : ∀x, p ⊆ (g x).dom) : p ⊆ (f >>= g).dom :=
λa ha, (⟨H1 ha, H2 _ ha⟩ : (f >>= g).dom a)

end pfun