/- Temporary space for definitions pending merges to the lean repository -/

import data.stream data.lazy_list

-- To be merged into data.stream
def stream.corec' {α β} (f : α → β × α) (a : α) : stream β :=
stream.corec (prod.fst ∘ f) (prod.snd ∘ f) a

def stream.corec'_eq {α β} (f : α → β × α) (a : α) :
  stream.corec' f a = (f a).1 :: stream.corec' f (f a).2 :=
stream.corec_eq _ _ _

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
