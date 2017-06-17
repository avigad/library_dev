/- Temporary space for definitions pending merges to the lean repository -/

import data.stream data.lazy_list

-- To be merged into data.stream
namespace stream
def corec' {α β} (f : α → β × α) (a : α) : stream β :=
corec (prod.fst ∘ f) (prod.snd ∘ f) a

def corec'_eq {α β} (f : α → β × α) (a : α) :
  corec' f a = (f a).1 :: corec' f (f a).2 :=
corec_eq _ _ _

lemma map_tail {α β} (f : α → β) (s : stream α) : map f (tail s) = tail (map f s) :=
rfl
end stream

-- To be merged into data.lazy_list
def lazy_list.to_list {α} : lazy_list α → list α
| lazy_list.nil        := []
| (lazy_list.cons h t) := h :: lazy_list.to_list (t ())

-- To be merged into init.data.list.basic
def list.filter_map {α β} (f : α → option β) : list α → list β 
| []     := [] 
| (list.cons a l) := 
  match f a with 
  | none   := list.filter_map l 
  | some b := b :: list.filter_map l 
  end

-- To be merged into init.data.option.instances
def option_map {α β} (f : α → β) (o : option α) : option β :=
option_bind o (some ∘ f)

@[simp] theorem option.map_id {α} : (option_map id : option α → option α) = id :=
funext (λo, by cases o; refl)
