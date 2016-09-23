open tactic expr list

attribute [instance]
meta_definition expr_has_ordering : has_ordering expr :=
has_ordering.mk expr.cmp

meta_definition imp (a b : expr) : expr :=
pi (default name) binder_info.default a b

meta_definition get_metas : expr → list expr
| (var _) := []
| (sort _) := []
| (const _ _) := []
| (meta n t) := expr.meta n t :: get_metas t
| (local_const _ _ _ t) := get_metas t
| (app a b) := get_metas a ++ get_metas b
| (lam _ _ d b) := get_metas d ++ get_metas b
| (pi _ _ d b) := get_metas d ++ get_metas b
| (elet _ t v b) := get_metas t ++ get_metas v ++ get_metas b
| (macro _ _ _) := []

meta_definition get_meta_type : expr → expr
| (meta _ t) := t
| _ := mk_var 0

meta_definition expr_size : expr → nat
| (var _) := 1
| (sort _) := 1
| (const _ _) := 1
| (meta n t) := 1
| (local_const _ _ _ _) := 1
| (app a b) := expr_size a + expr_size b
| (lam _ _ d b) := expr_size b
| (pi _ _ d b) := expr_size b
| (elet _ t v b) := expr_size v + expr_size b
| (macro _ _ _) := 1

namespace option

definition to_monad {m : Type → Type} [monad m] [alternative m] {A} : option A → m A
| none := failure
| (some a) := return a

definition get_or_else {B} : option B → B → B
| (some x) _   := x
| none default := default

end option

namespace ordering

definition is_lt {A} [has_ordering A] (x y : A) : bool :=
match has_ordering.cmp x y with ordering.lt := tt | _ := ff end

end ordering

namespace rb_map

meta_definition keys {K V} (m : rb_map K V) : list K :=
@fold K _ (list K) m [] (λk v ks, k::ks)

meta_definition values {K V} (m : rb_map K V) : list V :=
@fold _ V (list V) m [] (λk v vs, v::vs)

meta_definition set_of_list {A} [has_ordering A] : list A → rb_map A unit
| []      := mk _ _
| (x::xs) := insert (set_of_list xs) x ()

end rb_map

namespace list

meta_definition nub {A} [has_ordering A] (l : list A) : list A :=
rb_map.keys (rb_map.set_of_list l)

meta_definition nub_on {A B} [has_ordering B] (f : A → B) (l : list A) : list A :=
rb_map.values (rb_map.of_list (map (λx, (f x, x)) l))

definition nub_on' {A B} [decidable_eq B] (f : A → B) : list A → list A
| [] := []
| (x::xs) := x :: filter (λy, f x ≠ f y) (nub_on' xs)

definition foldr {A B} (f : A → B → B) (b : B) : list A → B
| [] := b
| (a::ass) := f a (foldr ass)

definition foldl {A B} (f : B → A → B) : B → list A → B
| b [] := b
| b (a::ass) := foldl (f b a) ass

definition for_all {A} (p : A → Prop) [decidable_pred p] : list A → bool
| (x::xs) := if ¬p x then ff else for_all xs
| [] := tt

definition filter_maximal {A} (gt : A → A → bool) (l : list A) : list A :=
filter (λx, for_all (λy, ¬gt y x) l) l

definition taken {A} : ℕ → list A → list A
| (n+1) (x::xs) := x :: taken n xs
| _ _ := []

definition empty {A} (l : list A) : bool :=
match l with
| [] := tt
| _::_ := ff
end

private definition zip_with_index' {A} : ℕ → list A → list (A × ℕ)
| _ nil := nil
| i (x::xs) := (x,i) :: zip_with_index' (i+1) xs

definition zip_with_index {A} : list A → list (A × ℕ) :=
zip_with_index' 0

definition remove {A} : list A → ℕ → list A
| []      _     := []
| (x::xs) 0     := xs
| (x::xs) (i+1) := x :: remove xs i

definition bor : list bool → bool
| (tt::xs) := tt
| (ff::xs) := bor xs
| [] := ff

definition contains {a} [decidable_eq a] (elem : a) : list a → bool
| (x::xs) := if x = elem then tt else contains xs
| [] := ff

definition range : ℕ → list ℕ
| (n+1) := n :: range n
| 0 := []

definition update {A} (new_elem : A) : ℕ → list A → list A
| 0     (x::xs) := new_elem :: xs
| (i+1) (x::xs) := x :: update i xs
| _     []      := []

definition partition {A} (pred : A → Prop) [decidable_pred pred] : list A → list A × list A
| (x::xs) := match partition xs with (ts,fs) := if pred x then (x::ts, fs) else (ts, x::fs) end
| [] := ([],[])

meta_definition merge_sorted {A} [has_ordering A] : list A → list A → list A
| [] ys := ys
| xs [] := xs
| (x::xs) (y::ys) :=
  if ordering.is_lt x y = tt then
    x :: merge_sorted xs (y::ys)
  else
    y :: merge_sorted (x::xs) ys

meta_definition sort {A} [has_ordering A] : list A → list A
| (x::xs) :=
  match partition (λy, ordering.is_lt y x) xs with
  | (smaller, greater_eq) := merge_sorted (sort smaller) (x :: sort greater_eq)
  end
| [] := []

meta_definition sort_on {A B} (f : A → B) [has_ordering B] : list A → list A :=
@sort _ ⟨λx y, has_ordering.cmp (f x) (f y)⟩

end list

meta_definition name_of_funsym : expr → name
| (local_const uniq _ _ _) := uniq
| (const n _) := n
| _ := name.anonymous

private meta_definition contained_funsyms' : expr → rb_map name expr → rb_map name expr
| (var _) m := m
| (sort _) m := m
| (const n ls) m := rb_map.insert m n (const n ls)
| (meta _ t) m := contained_funsyms' t m
| (local_const uniq pp bi t) m := rb_map.insert m uniq (local_const uniq pp bi t)
| (app a b) m := contained_funsyms' a (contained_funsyms' b m)
| (lam _ _ d b) m := contained_funsyms' d (contained_funsyms' b m)
| (pi _ _ d b) m := contained_funsyms' d (contained_funsyms' b m)
| (elet _ t v b) m := contained_funsyms' t (contained_funsyms' v (contained_funsyms' b m))
| (macro _ _ _) m := m

meta_definition contained_funsyms (e : expr) : rb_map name expr :=
contained_funsyms' e (rb_map.mk name expr)

private meta_definition contained_lconsts' : expr → rb_map name expr → rb_map name expr
| (var _) m := m
| (sort _) m := m
| (const _ _) m := m
| (meta _ t) m := contained_lconsts' t m
| (local_const uniq pp bi t) m := contained_lconsts' t (rb_map.insert m uniq (local_const uniq pp bi t))
| (app a b) m := contained_lconsts' a (contained_lconsts' b m)
| (lam _ _ d b) m := contained_lconsts' d (contained_lconsts' b m)
| (pi _ _ d b) m := contained_lconsts' d (contained_lconsts' b m)
| (elet _ t v b) m := contained_lconsts' t (contained_lconsts' v (contained_lconsts' b m))
| (macro _ _ _) m := m

meta_definition contained_lconsts (e : expr) : rb_map name expr :=
contained_lconsts' e (rb_map.mk name expr)

meta_definition contained_lconsts_list (es : list expr) : rb_map name expr :=
list.foldl (λlcs e, contained_lconsts' e lcs) (rb_map.mk name expr) es

meta_definition local_type : expr → expr
| (local_const _ _ _ t) := t
| e := e

meta_definition lambdas : list expr → expr → expr
| (local_const uniq pp info t :: es) f :=
               lam pp info t (abstract_local (lambdas es f) uniq)
| _ f := f

meta_definition pis : list expr → expr → expr
| (local_const uniq pp info t :: es) f :=
               pi pp info t (abstract_local (pis es f) uniq)
| _ f := f
