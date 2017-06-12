/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import data.seq.seq data.seq.computation
universes u v w

-- While the `seq` structure allows for lists which may not be finite,
-- a weak sequence also allows the computation of each element to
-- involve an indeterminate amount of computation, including possibly
-- an infinite loop. This is represented as a regular `seq` interspersed
-- with `none` elements to indicate that computation is ongoing.
--
-- This model is appropriate for Haskell style lazy lists, and is closed
-- under most interesting computation patterns on infinite lists,
-- but conversely it is difficult to extract elements from it.

/-
coinductive wseq (α : Type u) : Type u
| nil : wseq α
| cons : α → wseq α → wseq α 
| think : wseq α → wseq α 
-/
def wseq (α) := seq (option α)

namespace wseq
variables {α : Type u} {β : Type v} {γ : Type w}

def of_seq : seq α → wseq α := (<$>) some

def of_list (l : list α) : wseq α := of_seq l

def of_stream (l : stream α) : wseq α := of_seq l

instance coe_seq : has_coe (seq α) (wseq α) := ⟨of_seq⟩
instance coe_list : has_coe (list α) (wseq α) := ⟨of_list⟩
instance coe_stream : has_coe (stream α) (wseq α) := ⟨of_stream⟩

def nil : wseq α := seq.nil

def cons (a : α) : wseq α → wseq α := seq.cons (some a)

def think : wseq α → wseq α := seq.cons none

def destruct : wseq α → computation (option (α × wseq α)) :=
computation.corec (λs, match seq.destruct s with
  | none              := sum.inl none
  | some (none, s')   := sum.inr s'
  | some (some a, s') := sum.inl (some (a, s'))
  end)

def cases_on {C : wseq α → Sort v} (s : wseq α) (h1 : C nil)
  (h2 : ∀ x s, C (cons x s)) (h3 : ∀ s, C (think s)) : C s :=
seq.cases_on s h1 (λ o, option.cases_on o h3 h2)

protected def mem (a : α) (s : wseq α) := seq.mem (some a) s

instance : has_mem α (wseq α) :=
⟨wseq.mem⟩

theorem not_mem_nil (a : α) : a ∉ @nil α := seq.not_mem_nil a

def head (s : wseq α) : computation (option α) :=
((<$>) prod.fst) <$> destruct s

def flatten : computation (wseq α) → wseq α :=
seq.corec (λc, match computation.destruct c with
  | sum.inl s := seq.omap return (seq.destruct s)
  | sum.inr c' := some (none, c')
  end)

def tail (s : wseq α) : wseq α :=
flatten $ (λo, option.rec_on o nil prod.snd) <$> destruct s

def dropn (s : wseq α) : ℕ → wseq α
| 0     := s
| (n+1) := tail (dropn n)
attribute [simp] dropn

def nth (s : wseq α) (n : ℕ) : computation (option α) := head (dropn s n)

def to_list (s : wseq α) : computation (list α) :=
@computation.corec (list α) (list α × wseq α) (λ⟨l, s⟩,
  match seq.destruct s with
  | none              := sum.inl l.reverse
  | some (none, s')   := sum.inr (l, s')
  | some (some a, s') := sum.inr (a::l, s')
  end) ([], s)

def length (s : wseq α) : computation ℕ :=
@computation.corec ℕ (ℕ × wseq α) (λ⟨n, s⟩,
  match seq.destruct s with
  | none              := sum.inl n
  | some (none, s')   := sum.inr (n, s')
  | some (some a, s') := sum.inr (n+1, s')
  end) (0, s)

def update_nth (s : wseq α) (n : ℕ) (a : α) : wseq α :=
@seq.corec (option α) (ℕ × wseq α) (λ⟨n, s⟩,
  match seq.destruct s, n with
  | none,               n     := none
  | some (none, s'),    n     := some (none, n, s')
  | some (some a', s'), 0     := some (some a', 0, s')
  | some (some a', s'), 1     := some (some a, 0, s')
  | some (some a', s'), (n+2) := some (some a', n+1, s')
  end) (n+1, s)

def remove_nth (s : wseq α) (n : ℕ) : wseq α :=
@seq.corec (option α) (ℕ × wseq α) (λ⟨n, s⟩,
  match seq.destruct s, n with
  | none,               n     := none
  | some (none, s'),    n     := some (none, n, s')
  | some (some a', s'), 0     := some (some a', 0, s')
  | some (some a', s'), 1     := some (none, 0, s')
  | some (some a', s'), (n+2) := some (some a', n+1, s')
  end) (n+1, s)

def filter_map (f : α → option β) : wseq α → wseq β :=
seq.corec (λs, match seq.destruct s with
  | none              := none
  | some (none, s')   := some (none, s')
  | some (some a, s') := some (f a, s')
  end)

def filter (p : α → Prop) [decidable_pred p] : wseq α → wseq α :=
filter_map (λa, if p a then some a else none)

-- example of infinite list manipulations
def find (p : α → Prop) [decidable_pred p] (s : wseq α) : computation (option α) :=
head $ filter p s

def zip_with (f : α → β → γ) (s1 : wseq α) (s2 : wseq β) : wseq γ :=
@seq.corec (option γ) (wseq α × wseq β) (λ⟨s1, s2⟩,
  match seq.destruct s1, seq.destruct s2 with
  | some (none, s1'),    some (none, s2')    := some (none, s1', s2')
  | some (some a1, s1'), some (none, s2')    := some (none, s1, s2')
  | some (none, s1'),    some (some a2, s2') := some (none, s1', s2)
  | some (some a1, s1'), some (some a2, s2') := some (some (f a1 a2), s1', s2')
  | _,                   _                   := none
  end) (s1, s2)

def zip : wseq α → wseq β → wseq (α × β) := zip_with prod.mk

def find_indexes (p : α → Prop) [decidable_pred p] (s : wseq α) : wseq ℕ :=
(zip s (stream.nats : wseq ℕ)).filter_map
  (λ ⟨a, n⟩, if p a then some n else none)

def find_index (p : α → Prop) [decidable_pred p] (s : wseq α) : computation ℕ :=
(λ o, option.get_or_else o 0) <$> head (find_indexes p s)

def index_of [decidable_eq α] (a : α) : wseq α → computation ℕ := find_index (eq a)

def indexes_of [decidable_eq α] (a : α) : wseq α → wseq ℕ := find_indexes (eq a)

-- Calculate one step of computation
def compute (s : wseq α) : wseq α :=
match seq.destruct s with
| some (none, s') := s'
| _               := s
end

-- Like taken, but does not wait for a result
def collect (s : wseq α) (n : ℕ) : list α :=
(seq.taken n s).filter_map id

def append : wseq α → wseq α → wseq α := seq.append

def join (S : wseq (wseq α)) : wseq α :=
seq.join ((λo : option (wseq α), match o with
  | none := seq1.ret none
  | some s := (none, s)
  end) <$> S)

@[simp] def join_nil : join nil = (nil : wseq α) := seq.join_nil

@[simp] def join_think (S : wseq (wseq α)) :
  join (think S) = think (join S) :=
by { simp [think, join], unfold has_map.map, simp [join, seq1.ret] }

@[simp] def join_cons (s : wseq α) (S) :
  join (cons s S) = think (append s (join S)) :=
by { simp [think, join], unfold has_map.map, simp [join, cons, append] }

def bisim_o (R : wseq α → wseq α → Prop) :
  option (α × wseq α) → option (α × wseq α) → Prop
| none          none          := true
| (some (a, s)) (some (b, t)) := a = b ∧ R s t
| _             _             := false
attribute [simp] bisim_o

theorem bisim_o.imp {R S : wseq α → wseq α → Prop} (H : ∀ s t, R s t → S s t) :
  ∀ o p, bisim_o R o p → bisim_o S o p
| none          none          h := trivial
| (some (a, s)) (some (b, t)) h := and.imp id (H _ _) h
| none          (some _)      h := false.elim h
| (some (_, _)) none          h := false.elim h

def equiv (s t : wseq α) : Prop :=
∃ R : wseq α → wseq α → Prop, R s t ∧
∀ {s t}, R s t → computation.lift_rel (bisim_o R) (destruct s) (destruct t)

infix ~ := equiv

def equiv_destruct {s t : wseq α} :
  s ~ t → computation.lift_rel (bisim_o (~)) (destruct s) (destruct t)
| ⟨R, h1, h2⟩ :=
  by refine computation.lift_rel.imp _ _ _ (h2 h1);
     apply bisim_o.imp; exact λ s' t' h', ⟨R, h', @h2⟩

open computation
local notation `return` := computation.return

@[simp] theorem destruct_nil : destruct (nil : wseq α) = return none :=
computation.destruct_eq_ret rfl

@[simp] theorem destruct_cons (a : α) (s) : destruct (cons a s) = return (some (a, s)) :=
computation.destruct_eq_ret $ by simp [destruct, cons, computation.rmap]

@[simp] theorem destruct_think (s : wseq α) : destruct (think s) = (destruct s).think :=
computation.destruct_eq_think $ by simp [destruct, think, computation.rmap]

@[simp] theorem head_nil : head (nil : wseq α) = return none := by simp [head]; refl
@[simp] theorem head_cons (a : α) (s) : head (cons a s) = return (some a) := by simp [head]; refl
@[simp] theorem head_think (s : wseq α) : head (think s) = (head s).think := by simp [head]; refl

@[simp] theorem flatten_ret (s : wseq α) : flatten (return s) = s :=
begin
  refine seq.eq_of_bisim (λs1 s2, flatten (return s2) = s1) _ rfl,
  intros s' s h, rw -h, simp [flatten],
  cases seq.destruct s, { simp },
  { cases a with o s', simp }
end

@[simp] theorem flatten_think (c : computation (wseq α)) : flatten c.think = think (flatten c) :=
seq.destruct_eq_cons $ by simp [flatten, think]

@[simp] theorem destruct_flatten (c : computation (wseq α)) : destruct (flatten c) = c >>= destruct :=
begin
  refine computation.eq_of_bisim (λc1 c2, c1 = c2 ∨
    ∃ c, c1 = destruct (flatten c) ∧ c2 = computation.bind c destruct) _ (or.inr ⟨c, rfl, rfl⟩),
  intros c1 c2 h, exact match c1, c2, h with
  | c, ._, (or.inl rfl) := by cases c.destruct; simp
  | ._, ._, (or.inr ⟨c, rfl, rfl⟩) := begin
    apply c.cases_on (λa, _) (λc', _); repeat {simp},
    { cases (destruct a).destruct; simp },
    { exact or.inr ⟨c', rfl, rfl⟩ }
  end end
end

theorem head_terminates_iff (s : wseq α) : terminates (head s) ↔ terminates (destruct s) :=
terminates_map_iff _ (destruct s)

@[simp] theorem tail_nil : tail (nil : wseq α) = nil := by simp [tail]
@[simp] theorem tail_cons (a : α) (s) : tail (cons a s) = s := by simp [tail]
@[simp] theorem tail_think (s : wseq α) : tail (think s) = (tail s).think := by simp [tail]

theorem head_terminates_of_head_tail_terminates (s : wseq α) [T : terminates (head (tail s))] :
  terminates (head s) :=
(head_terminates_iff _).2 $ begin
  cases (head_terminates_iff _).1 T with a h,
  simp [tail] at h,
  cases exists_of_mem_bind h with s' h1, cases h1 with h1 h2,
  unfold has_map.map at h1,
  exact let ⟨t, h3, h4⟩ := exists_of_mem_map h1 in terminates_of_mem h3
end

theorem nth_terminates_le (s : wseq α) {m n} (h : m ≤ n) : terminates (nth s n) → terminates (nth s m) :=
by induction h with m' h IH; [exact id,
  exact λ T, IH (@head_terminates_of_head_tail_terminates _ _ T)]

theorem head_terminates_of_nth_terminates (s : wseq α) n [T : terminates (nth s n)] : terminates (head s) :=
nth_terminates_le s (nat.zero_le n) T

theorem destruct_terminates_of_nth_terminates (s : wseq α) n [T : terminates (nth s n)] : terminates (destruct s) :=
(head_terminates_iff _).1 $ head_terminates_of_nth_terminates s n

/-
theorem exists_nth_of_mem {s : wseq α} {a} (h : a ∈ s) : ∃ n, some a ∈ nth s n :=
_
-/

end wseq