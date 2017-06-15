/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Coinductive formalization of unbounded computations.
-/
import data.stream data.nat.find pending
universes u v w

/-
coinductive computation (α : Type u) : Type u
| return : α → computation α
| think : computation α → computation α
-/

def computation (α : Type u) : Type u :=
{ f : stream (option α) // ∀ {n a}, f n = some a → f (n+1) = some a }

namespace computation
variables {α : Type u} {β : Type v} {γ : Type w}

-- constructors
def return (a : α) : computation α := ⟨stream.const (some a), λn a', id⟩

instance : has_coe α (computation α) := ⟨return⟩

def think (c : computation α) : computation α :=
⟨none :: c.1, λn a h, by {cases n with n, contradiction, exact c.2 h}⟩

def thinkN (c : computation α) : ℕ → computation α
| 0 := c
| (n+1) := think (thinkN n)

-- check for immediate result
def head (c : computation α) : option α := c.1.head

-- one step of computation
def tail (c : computation α) : computation α :=
⟨c.1.tail, λ n a, let t := c.2 in t⟩

def empty (α) : computation α := ⟨stream.const none, λn a', id⟩

def compute : computation α → ℕ → option α := subtype.val

def destruct (s : computation α) : α ⊕ computation α :=
match s.1 0 with
| none := sum.inr (tail s)
| some a := sum.inl a
end

meta def finish : computation α → α | c :=
match destruct c with
| sum.inl a := a
| sum.inr ca := finish ca
end

theorem destruct_eq_ret {s : computation α} {a : α} :
  destruct s = sum.inl a → s = return a :=
begin
  dsimp [destruct],
  ginduction s.1 0 with f0; intro h,
  { contradiction },
  { apply subtype.eq, apply funext,
    dsimp [return], intro n,
    induction n with n IH,
    { injection h, rwa h at f0 },
    { exact s.2 IH } }
end

theorem destruct_eq_think {s : computation α} {s'} :
  destruct s = sum.inr s' → s = think s' :=
begin
  dsimp [destruct],
  ginduction s.1 0 with f0 a'; intro h,
  { injection h, rw -h,
    cases s with f al,
    apply subtype.eq, dsimp [think, tail],
    rw -f0, exact (stream.eta f).symm },
  { contradiction }
end

@[simp] theorem destruct_ret (a : α) : destruct (return a) = sum.inl a := rfl

@[simp] theorem destruct_think : ∀ s : computation α, destruct (think s) = sum.inr s
| ⟨f, al⟩ := rfl

@[simp] theorem destruct_empty : destruct (empty α) = sum.inr (empty α) := rfl

@[simp] theorem head_ret (a : α) : head (return a) = some a := rfl

@[simp] theorem head_think (s : computation α) : head (think s) = none := rfl

@[simp] theorem head_empty : head (empty α) = none := rfl

@[simp] theorem tail_ret (a : α) : tail (return a) = return a := rfl

@[simp] theorem tail_think (s : computation α) : tail (think s) = s :=
by cases s with f al; apply subtype.eq; dsimp [tail, think]; rw [stream.tail_cons]

@[simp] theorem tail_empty : tail (empty α) = empty α := rfl

theorem think_empty : empty α = think (empty α) :=
destruct_eq_think destruct_empty

def cases_on {C : computation α → Sort v} (s : computation α)
  (h1 : ∀ a, C (return a)) (h2 : ∀ s, C (think s)) : C s := begin
  ginduction destruct s with H,
  { rw destruct_eq_ret H, apply h1 },
  { cases a with a s', rw destruct_eq_think H, apply h2 }
end

def corec.F (f : β → α ⊕ β) : α ⊕ β → option α × (α ⊕ β)
| (sum.inl a) := (some a, sum.inl a)
| (sum.inr b) := (match f b with
  | sum.inl a := some a
  | sum.inr b' := none
  end, f b)

def corec (f : β → α ⊕ β) (b : β) : computation α :=
begin
  refine ⟨stream.corec' (corec.F f) (sum.inr b), λn a' h, _⟩,
  rw stream.corec'_eq,
  change stream.corec' (corec.F f) (corec.F f (sum.inr b)).2 n = some a',
  revert h, generalize (sum.inr b) o,
  induction n with n IH; intro o,
  { change (corec.F f o).1 = some a' → (corec.F f (corec.F f o).2).1 = some a',
    cases o with a b; intro h, { exact h },
    dsimp [corec.F] at h, dsimp [corec.F],
    cases f b with a b', { exact h },
    { contradiction } },
  { rw [stream.corec'_eq (corec.F f) (corec.F f o).2,
        stream.corec'_eq (corec.F f) o],
    exact IH (corec.F f o).2 }
end

def rmap (f : β → γ) : α ⊕ β → α ⊕ γ
| (sum.inl a) := sum.inl a
| (sum.inr b) := sum.inr (f b)
attribute [simp] rmap

@[simp] def corec_eq (f : β → α ⊕ β) (b : β) :
  destruct (corec f b) = rmap (corec f) (f b) :=
begin
  dsimp [corec, destruct],
  change stream.corec' (corec.F f) (sum.inr b) 0 with corec.F._match_1 (f b),
  ginduction f b with h a b', { refl },
  dsimp [corec.F, destruct],
  apply congr_arg, apply subtype.eq,
  dsimp [corec, tail],
  rw [stream.corec'_eq, stream.tail_cons],
  dsimp [corec.F], rw h
end

section bisim
  variable (R : computation α → computation α → Prop)

  local infix ~ := R

  def bisim_o : α ⊕ computation α → α ⊕ computation α → Prop
  | (sum.inl a) (sum.inl a') := a = a'
  | (sum.inr s) (sum.inr s') := R s s'
  | _           _            := false
  attribute [simp] bisim_o

  def is_bisimulation := ∀ ⦃s₁ s₂⦄, s₁ ~ s₂ → bisim_o R (destruct s₁) (destruct s₂)

  -- If two computations are bisimilar, then they are equal
  lemma eq_of_bisim (bisim : is_bisimulation R) {s₁ s₂} (r : s₁ ~ s₂) : s₁ = s₂ :=
  begin
    apply subtype.eq,
    apply stream.eq_of_bisim (λx y, ∃ s s' : computation α, s.1 = x ∧ s'.1 = y ∧ R s s'),
    dsimp [stream.is_bisimulation],
    intros t₁ t₂ e,
    exact match t₁, t₂, e with ._, ._, ⟨s, s', rfl, rfl, r⟩ :=
      suffices head s = head s' ∧ R (tail s) (tail s'), from
      and.imp id (λr, ⟨tail s, tail s',
        by cases s; refl, by cases s'; refl, r⟩) this,
      begin
        note := bisim r, revert r this,
        apply cases_on s _ _; intros; apply cases_on s' _ _; intros; intros r this,
        { constructor, dsimp at this, rw this, assumption },
        { rw [destruct_ret, destruct_think] at this,
          exact false.elim this },
        { rw [destruct_ret, destruct_think] at this,
          exact false.elim this },
        { simp at this, simph }          
      end
    end,
    exact ⟨s₁, s₂, rfl, rfl, r⟩
  end
end bisim

-- It's more of a stretch to use ∈ for this relation, but it
-- asserts that the computation limits to the given value.
protected def mem (a : α) (s : computation α) := some a ∈ s.1

instance : has_mem α (computation α) :=
⟨computation.mem⟩

theorem le_stable (s : computation α) {a m n} (h : m ≤ n) :
  s.1 m = some a → s.1 n = some a :=
by {cases s with f al, induction h with n h IH, exacts [id, λ h2, al (IH h2)]}

theorem mem_unique :
   relator.left_unique ((∈) : α → computation α → Prop) :=
λa s b ⟨m, ha⟩ ⟨n, hb⟩, by injection
  (le_stable s (le_max_left m n) ha.symm).symm.trans
  (le_stable s (le_max_right m n) hb.symm)

@[class] def terminates (s : computation α) : Prop := ∃ a, a ∈ s

theorem terminates_of_mem {s : computation α} {a : α} : a ∈ s → terminates s :=
exists.intro a

theorem terminates_def (s : computation α) : terminates s ↔ ∃ n, (s.1 n).is_some :=
⟨λ⟨a, n, h⟩, ⟨n, by {dsimp [stream.nth] at h, rw -h, exact rfl}⟩,
λ⟨n, h⟩, ⟨option.get h, n, (option.eq_some_of_is_some h).symm⟩⟩

theorem ret_mem (a : α) : a ∈ return a :=
exists.intro 0 rfl

instance ret_terminates (a : α) : terminates (return a) :=
terminates_of_mem (ret_mem _)

theorem think_mem {s : computation α} {a} : a ∈ s → a ∈ think s
| ⟨n, h⟩ := ⟨n+1, h⟩

instance think_terminates (s : computation α) :
  ∀ [terminates s], terminates (think s)
| ⟨a, n, h⟩ := ⟨a, n+1, h⟩

theorem of_think_mem {s : computation α} {a} : a ∈ think s → a ∈ s
| ⟨n, h⟩ := by {cases n with n', contradiction, exact ⟨n', h⟩}

theorem of_think_terminates {s : computation α} :
  terminates (think s) → terminates s
| ⟨a, h⟩ := ⟨a, of_think_mem h⟩

theorem not_mem_empty (a : α) : a ∉ empty α :=
λ ⟨n, h⟩, by clear _fun_match; contradiction

theorem not_terminates_empty : ¬ terminates (empty α) :=
λ ⟨a, h⟩, not_mem_empty a h

theorem eq_empty_of_not_terminates {s} (H : ¬ terminates s) : s = empty α :=
begin
  apply subtype.eq, apply funext, intro n,
  ginduction s.val n with h,
  { exact h }, { refine absurd _ H, exact ⟨_, _, h.symm⟩ }
end

theorem thinkN_mem {s : computation α} {a} : ∀ n, a ∈ thinkN s n ↔ a ∈ s
| 0 := iff.rfl
| (n+1) := iff.trans ⟨of_think_mem, think_mem⟩ (thinkN_mem n)

instance thinkN_terminates (s : computation α) :
  ∀ [terminates s] n, terminates (thinkN s n)
| ⟨a, h⟩ n := ⟨a, (thinkN_mem n).2 h⟩

theorem of_thinkN_terminates (s : computation α) (n) :
  terminates (thinkN s n) → terminates s
| ⟨a, h⟩ := ⟨a, (thinkN_mem _).1 h⟩

def promises (s : computation α) (a : α) : Prop := ∀ ⦃a'⦄, a' ∈ s → a = a'

infix ` ~> `:50 := promises

theorem mem_promises {s : computation α} {a : α} : a ∈ s → s ~> a :=
λ h a', mem_unique h

theorem empty_promises (a : α) : empty α ~> a :=
λ a' h, absurd h (not_mem_empty _)

section get
variables (s : computation α) [h : terminates s]
include s h

def length : ℕ := nat.find ((terminates_def _).1 h)

-- If a computation has a result, we can retrieve it
def get : α := option.get (nat.find_spec $ (terminates_def _).1 h)

def get_mem : get s ∈ s :=
exists.intro (length s) (option.eq_some_of_is_some _).symm

def get_eq_of_mem {a} : a ∈ s → get s = a :=
mem_unique (get_mem _)

@[simp] theorem get_think : get (think s) = get s :=
get_eq_of_mem _ $ let ⟨n, h⟩ := get_mem s in ⟨n+1, h⟩

@[simp] theorem get_thinkN (n) : get (thinkN s n) = get s :=
get_eq_of_mem _ $ (thinkN_mem _).2 (get_mem _)

def get_promises : s ~> get s := λ a, get_eq_of_mem _

def mem_of_promises {a} (p : s ~> a) : a ∈ s :=
by cases h with a' h; rw p h; exact h

def get_eq_of_promises {a} : s ~> a → get s = a :=
get_eq_of_mem _ ∘ mem_of_promises _

end get

@[simp] theorem get_ret (a : α) : get (return a) = a :=
get_eq_of_mem _ ⟨0, rfl⟩

@[simp] theorem length_ret (a : α) : length (return a) = 0 :=
let h := computation.ret_terminates a in
nat.eq_zero_of_le_zero $ nat.find_min' ((terminates_def (return a)).1 h) rfl

@[simp] theorem length_think (s : computation α) [h : terminates s] :
  length (think s) = length s + 1 :=
begin
  apply le_antisymm,
  { exact nat.find_min' _ (nat.find_spec ((terminates_def _).1 h)) },
  { note : (option.is_some ((think s).val (length (think s))) : Prop) :=
      nat.find_spec ((terminates_def _).1 s.think_terminates),
    cases length (think s) with n,
    { contradiction },
    { apply nat.succ_le_succ, apply nat.find_min', apply this } }
end
--set_option pp.implicit true
@[simp] theorem length_thinkN (s : computation α) [h : terminates s] : ∀ n,
  length (thinkN s n) = length s + n
| 0 := rfl
| (n+1) := (length_think _).trans $ congr_arg nat.succ (length_thinkN n)

def eq_thinkN (s : computation α) [h : terminates s] :
  s = thinkN (return (get s)) (length s) :=
begin
  generalize2 (length s) n e, revert s,
  induction n with n IH; intro s; apply cases_on s _ _,
  { intros a h e, apply congr_arg, exact (get_ret _).symm },
  { intros s h e, note h' := of_think_terminates h,
    change h with @computation.think_terminates α s h' at e,
    rw [length_think] at e, injection e },
  { intros a h e, rw [length_ret] at e, injection e },
  { intros s h e, note h' := of_think_terminates h,
    change h with @computation.think_terminates α s h' at e,
    rw [length_think] at e, injection e with e,
    simp [thinkN], apply congr_arg,
    apply IH _ e }
end

def mem_rec_on {C : computation α → Sort v} {a s} (M : a ∈ s)
  (h1 : C (return a)) (h2 : ∀ s, C s → C (think s)) : C s :=
begin
  note T := terminates_of_mem M,
  rw [eq_thinkN s, get_eq_of_mem s M],
  generalize (length s) n, intro n,
  induction n with n IH, exacts [h1, h2 _ IH]
end

def terminates_rec_on {C : computation α → Sort v} (s) [terminates s]
  (h1 : ∀ a, C (return a)) (h2 : ∀ s, C s → C (think s)) : C s :=
mem_rec_on (get_mem s) (h1 _) h2

def map (f : α → β) : computation α → computation β
| ⟨s, al⟩ := ⟨s.map (λo, option.cases_on o none (some ∘ f)),
λn b, begin
  dsimp [stream.map],
  ginduction s n with e a; dsimp; intro h,
  { contradiction }, { rw [al e, -h] }
end⟩

def bind.G : β ⊕ computation β → β ⊕ computation α ⊕ computation β
| (sum.inl b)   := sum.inl b
| (sum.inr cb') := sum.inr $ sum.inr cb'

def bind.F (f : α → computation β) :
  computation α ⊕ computation β → β ⊕ computation α ⊕ computation β
| (sum.inl ca) :=
  match destruct ca with
  | sum.inl a := bind.G $ destruct (f a)
  | sum.inr ca' := sum.inr $ sum.inl ca'
  end
| (sum.inr cb) := bind.G $ destruct cb

def bind (c : computation α) (f : α → computation β) : computation β :=
corec (bind.F f) (sum.inl c)

instance : has_bind computation := ⟨@bind⟩

def join (c : computation (computation α)) : computation α := c >>= id

@[simp] lemma map_ret (f : α → β) (a) : map f (return a) = return (f a) := rfl

@[simp] lemma map_think (f : α → β) : ∀ s, map f (think s) = think (map f s)
| ⟨s, al⟩ := by apply subtype.eq; dsimp [think, map]; rw stream.map_cons

@[simp] theorem map_id : ∀ (s : computation α), map id s = s
| ⟨f, al⟩ := begin
  apply subtype.eq; dsimp [think, map],
  assert e : (@option.rec α (λ_, option α) none some) = id,
  { apply funext, intro, cases x; refl },
  rw [e, stream.map_id]
end

@[simp] lemma ret_bind (a) (f : α → computation β) :
  bind (return a) f = f a :=
begin
  apply eq_of_bisim (λc1 c2,
         c1 = bind (return a) f ∧ c2 = f a ∨
         c1 = corec (bind.F f) (sum.inr c2)),
  { intros c1 c2 h,
    exact match c1, c2, h with
    | ._, ._, or.inl ⟨rfl, rfl⟩ := begin
      simp [bind, bind.F],
      cases destruct (f a) with b cb; simp [bind.G]
    end
    | ._, c, or.inr rfl := begin
      simp [bind.F],
      cases destruct c with b cb; simp [bind.G]
    end end },
  { simp }
end

@[simp] lemma think_bind (c) (f : α → computation β) :
  bind (think c) f = think (bind c f) :=
destruct_eq_think $ by simp [bind, bind.F]

@[simp] theorem bind_ret (f : α → β) (s) : bind s (return ∘ f) = map f s :=
begin
  apply eq_of_bisim (λc1 c2, c1 = c2 ∨
         ∃ s, c1 = bind s (return ∘ f) ∧ c2 = map f s),
  { intros c1 c2 h,
    exact match c1, c2, h with
    | c, ._, or.inl rfl := by cases destruct c with b cb; simp
    | ._, ._, or.inr ⟨s, rfl, rfl⟩ := begin
      apply cases_on s; intros s; simp,
      exact or.inr ⟨s, rfl, rfl⟩
    end end },
  { exact or.inr ⟨s, rfl, rfl⟩ }
end

@[simp] theorem bind_assoc (s : computation α) (f : α → computation β) (g : β → computation γ) :
  bind (bind s f) g = bind s (λ (x : α), bind (f x) g) :=
begin
  apply eq_of_bisim (λc1 c2, c1 = c2 ∨
         ∃ s, c1 = bind (bind s f) g ∧ c2 = bind s (λ (x : α), bind (f x) g)),
  { intros c1 c2 h,
    exact match c1, c2, h with
    | c, ._, or.inl rfl := by cases destruct c with b cb; simp
    | ._, ._, or.inr ⟨s, rfl, rfl⟩ := begin
      apply cases_on s; intros s; simp,
      { generalize (f s) fs, intro fs,
        apply cases_on fs; intros t; simp,
        { cases destruct (g t) with b cb; simp } },
      { exact or.inr ⟨s, rfl, rfl⟩ }
    end end },
  { exact or.inr ⟨s, rfl, rfl⟩ }
end

theorem mem_bind {s : computation α} {f : α → computation β} {a b}
  (h1 : a ∈ s) (h2 : b ∈ f a) : b ∈ bind s f :=
begin
  apply mem_rec_on h1,
  { rw [ret_bind], exact h2 },
  { intros s, rw [think_bind], exact think_mem }
end

instance terminates_bind (s : computation α) (f : α → computation β)
  [terminates s] [terminates (f (get s))] :
  terminates (bind s f) :=
terminates_of_mem (mem_bind (get_mem s) (get_mem (f (get s))))

@[simp] theorem get_bind (s : computation α) (f : α → computation β)
  [terminates s] [terminates (f (get s))] :
  get (bind s f) = get (f (get s)) :=
get_eq_of_mem _ (mem_bind (get_mem s) (get_mem (f (get s))))

@[simp] theorem length_bind (s : computation α) (f : α → computation β)
  [T1 : terminates s] [T2 : terminates (f (get s))] :
  length (bind s f) = length (f (get s)) + length s :=
begin
  note T1' := T1, revert T1 T2, apply terminates_rec_on s _ _,
  { intros a T1 T2, change T1 with @computation.ret_terminates _ a, simp },
  { intros s IH T1, note T3 := of_think_terminates T1,
    change T1 with @computation.think_terminates α s T3, intro,
    simp at T2,
    simp only [length_think, think_bind, get_think],
    exact congr_arg (λn,n+1) IH }
end

theorem exists_of_mem_bind {s : computation α} {f : α → computation β} {b}
  (h : b ∈ bind s f) : ∃ a ∈ s, b ∈ f a :=
begin
  note T := terminates_of_mem h,
  note e := eq_thinkN (bind s f),
  rw get_eq_of_mem _ h at e, revert e,
  generalize (length (bind s f)) n, intro n,
  clear T h, revert s, induction n with n IH; intros;
  simp [thinkN] at e; revert e; apply cases_on s _ _,
  { intros a e, refine ⟨a, ret_mem _, _⟩,
    simp at e, rw e, apply ret_mem },
  { intros s e, note := congr_arg head e, contradiction },
  { intros a e, refine ⟨a, ret_mem _, _⟩,
    simp at e, rw e, apply (thinkN_mem (n+1)).2, apply ret_mem },
  { intros s e, note e := congr_arg tail e, simp at e,
    cases IH e with a h, cases h with h1 h2,
    exact ⟨a, think_mem h1, h2⟩ }
end

theorem bind_promises {s : computation α} {f : α → computation β} {a b}
  (h1 : s ~> a) (h2 : f a ~> b) : bind s f ~> b :=
λ b' bB, begin
  cases exists_of_mem_bind bB with a' a's, cases a's with a's ba',
  rw -h1 a's at ba', exact h2 ba'
end

instance : monad computation :=
{ map  := @map,
  pure := @return,
  bind := @bind,
  id_map := @map_id,
  bind_pure_comp_eq_map := @bind_ret,
  pure_bind := @ret_bind,
  bind_assoc := @bind_assoc }

@[simp] lemma return_def (a) : (_root_.return a : computation α) = return a := rfl

@[simp] lemma map_ret' {α β} : ∀ (f : α → β) (a), f <$> return a = return (f a) := map_ret
@[simp] lemma map_think' {α β} : ∀ (f : α → β) s, f <$> think s = think (f <$> s) := map_think

theorem mem_map (f : α → β) {a} {s : computation α} (m : a ∈ s) : f a ∈ map f s :=
by rw -bind_ret; apply mem_bind m; apply ret_mem

theorem exists_of_mem_map {f : α → β} {b : β} {s : computation α} (h : b ∈ map f s) :
   ∃ a, a ∈ s ∧ f a = b :=
by rw -bind_ret at h; exact
let ⟨a, as, fb⟩ := exists_of_mem_bind h in ⟨a, as, mem_unique (ret_mem _) fb⟩

instance terminates_map (f : α → β) (s : computation α) [terminates s] : terminates (map f s) :=
by rw -bind_ret; apply_instance

theorem terminates_map_iff (f : α → β) (s : computation α) :
  terminates (map f s) ↔ terminates s :=
⟨λ⟨a, h⟩, let ⟨b, h1, _⟩ := exists_of_mem_map h in ⟨_, h1⟩, @computation.terminates_map _ _ _ _⟩

-- Parallel computation
def orelse (c1 c2 : computation α) : computation α :=
@computation.corec α (computation α × computation α)
  (λ⟨c1, c2⟩, match destruct c1 with
  | sum.inl a := sum.inl a
  | sum.inr c1' := match destruct c2 with
    | sum.inl a := sum.inl a
    | sum.inr c2' := sum.inr (c1', c2')
    end
  end) (c1, c2)

instance : alternative computation :=
{ computation.monad with
  orelse := @orelse,
  failure := @empty }

@[simp] theorem ret_orelse (a : α) (c2 : computation α) :
  (return a <|> c2) = return a :=
destruct_eq_ret $ by unfold has_orelse.orelse; simp [orelse]

@[simp] theorem orelse_ret (c1 : computation α) (a : α) :
  (think c1 <|> return a) = return a :=
destruct_eq_ret $ by unfold has_orelse.orelse; simp [orelse]

@[simp] theorem orelse_think (c1 c2 : computation α) :
  (think c1 <|> think c2) = think (c1 <|> c2) :=
destruct_eq_think $ by unfold has_orelse.orelse; simp [orelse]

@[simp] theorem empty_orelse (c) : (empty α <|> c) = c :=
begin
  apply eq_of_bisim (λc1 c2, (empty α <|> c2) = c1) _ rfl,
  intros s' s h, rw -h,
  apply cases_on s; intros s; rw think_empty; simp,
  rw -think_empty,
end

@[simp] theorem orelse_empty (c : computation α) : (c <|> empty α) = c :=
begin
  apply eq_of_bisim (λc1 c2, (c2 <|> empty α) = c1) _ rfl,
  intros s' s h, rw -h,
  apply cases_on s; intros s; rw think_empty; simp,
  rw -think_empty,
end

def equiv (c1 c2 : computation α) : Prop := ∀ a, a ∈ c1 ↔ a ∈ c2

infix ~ := equiv

theorem equiv.refl (s : computation α) : s ~ s := λ_, iff.rfl

theorem equiv.symm {s t : computation α} : s ~ t → t ~ s :=
λh a, (h a).symm

theorem equiv.trans {s t u : computation α} : s ~ t → t ~ u → s ~ u :=
λh1 h2 a, (h1 a).trans (h2 a)

theorem equiv.equivalence : equivalence (@equiv α) :=
⟨@equiv.refl _, @equiv.symm _, @equiv.trans _⟩

theorem terminates_congr {c1 c2 : computation α}
  (h : c1 ~ c2) : terminates c1 ↔ terminates c2 :=
exists_congr h

theorem promises_congr {c1 c2 : computation α}
  (h : c1 ~ c2) (a) : c1 ~> a ↔ c2 ~> a :=
forall_congr (λa', imp_congr (h a') iff.rfl)

theorem get_equiv {c1 c2 : computation α} (h : c1 ~ c2)
  [terminates c1] [terminates c2] : get c1 = get c2 :=
get_eq_of_mem _ $ (h _).2 $ get_mem _

theorem think_equiv (s : computation α) : think s ~ s :=
λ a, ⟨of_think_mem, think_mem⟩

theorem thinkN_equiv (s : computation α) (n) : thinkN s n ~ s :=
λ a, thinkN_mem n

theorem bind_congr {s1 s2 : computation α} {f1 f2 : α → computation β}
  (h1 : s1 ~ s2) (h2 : ∀ a, f1 a ~ f2 a) : bind s1 f1 ~ bind s2 f2 :=
λ b, ⟨λh, let ⟨a, ha, hb⟩ := exists_of_mem_bind h in
        mem_bind ((h1 a).1 ha) ((h2 a b).1 hb),
      λh, let ⟨a, ha, hb⟩ := exists_of_mem_bind h in
        mem_bind ((h1 a).2 ha) ((h2 a b).2 hb)⟩

def lift_rel (R : α → β → Prop) (ca : computation α) (cb : computation β) : Prop :=
(terminates ca ↔ terminates cb) ∧ ∀ {a b}, a ∈ ca → b ∈ cb → R a b

theorem lift_eq_iff_equiv (c1 c2 : computation α) : lift_rel (=) c1 c2 ↔ c1 ~ c2 :=
⟨λ⟨h1, h2⟩ a,
  ⟨λ a1, by {cases h1.1 ⟨_, a1⟩ with b b2, rw h2 a1 b2, exact b2},
   λ a2, by {cases h1.2 ⟨_, a2⟩ with b b1, rw -h2 b1 a2, exact b1},⟩,
λe, ⟨terminates_congr e, λ a b a1, mem_unique ((e _).1 a1)⟩⟩

def lift_rel.refl (R : α → α → Prop) (H : reflexive R) : reflexive (lift_rel R) :=
λ s, ⟨iff.rfl, λ a b as bs, by {rw mem_unique as bs, apply H}⟩

def lift_rel.symm (R : α → α → Prop) (H : symmetric R) : symmetric (lift_rel R) :=
λ s1 s2 ⟨l, r⟩, ⟨l.symm, λ a b a2 b1, H (r b1 a2)⟩

def lift_rel.trans (R : α → α → Prop) (H : transitive R) : transitive (lift_rel R) :=
λ s1 s2 s3 ⟨l1, r1⟩ ⟨l2, r2⟩, ⟨l1.trans l2, λ a c a1 c3,
  let ⟨b, b2⟩ := l1.1 ⟨_, a1⟩ in H (r1 a1 b2) (r2 b2 c3)⟩

def lift_rel.equiv (R : α → α → Prop) : equivalence R → equivalence (lift_rel R)
| ⟨refl, symm, trans⟩ :=
  ⟨lift_rel.refl R refl, lift_rel.symm R symm, lift_rel.trans R trans⟩ 

def lift_rel.imp {R S : α → β → Prop} (H : ∀ {a b}, R a b → S a b) (s t) :
 lift_rel R s t → lift_rel S s t :=
and.imp id (λ h a b as bt, H (h as bt))

theorem bind_lift_rel {δ} (R : α → β → Prop) (S : γ → δ → Prop)
  {s1 : computation α} {s2 : computation β}
  {f1 : α → computation γ} {f2 : β → computation δ}
  (h1 : lift_rel R s1 s2) (h2 : ∀ {a b}, R a b → lift_rel S (f1 a) (f2 b))
  : lift_rel S (bind s1 f1) (bind s2 f2) :=
begin
  cases h1 with l1 r1,
  refine ⟨⟨λh, _, λh, _⟩, λb b' b1 b'2, _⟩,
  { cases h with b h,
    cases exists_of_mem_bind h with a a1, cases a1 with a1 b1,
    cases l1.1 ⟨a, a1⟩ with a' a'2,
    cases h2 (r1 a1 a'2) with l2 r2,
    cases l2.1 ⟨_, b1⟩ with b' b'2,
    exact ⟨_, mem_bind a'2 b'2⟩ },
  { cases h with b h,
    cases exists_of_mem_bind h with a a2, cases a2 with a2 b2,
    cases l1.2 ⟨a, a2⟩ with a' a'1,
    cases h2 (r1 a'1 a2) with l2 r2,
    cases l2.2 ⟨_, b2⟩ with b' b'1,
    exact ⟨_, mem_bind a'1 b'1⟩ },
  { cases exists_of_mem_bind b1 with a a1, cases a1 with a1 b1,
    cases exists_of_mem_bind b'2 with a' a'2, cases a'2 with a'2 b'2,
    cases h2 (r1 a1 a'2) with l2 r2,
    exact r2 b1 b'2 }
end

end computation
