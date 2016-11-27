/-
   alternative names for theorems in init.logic.
-/

-- parallels not_false_iff
def not_true_iff := not_true

def not_not_em := non_contradictory_em

def not_not_not_iff := not_non_contradictory_iff_absurd

def and_implies := @and.imp

def and.symm := @and.swap

def or.symm := @or.swap

-- we should have these for uniformity with mul_assoc, mul_comm

def and_assoc := @and.assoc

def and_comm := @and.comm

def or_assoc := @or.assoc

def or_comm := @or.comm

-- also, arguments to all of these should be explicit


/- alternative names for calculational theorems-/

-- in group

def inv_mul_self := @mul_left_inv

def mul_inv_self := @mul_right_inv

def neg_add_self := @add_left_neg

def add_neg_self := @add_right_neg

def eq_of_add_eq_add_left := @add_left_cancel

def eq_of_add_eq_add_right := @add_right_cancel


-- in ring

def mul_add := @left_distrib

def add_mul := @right_distrib

def mul_sub := @mul_sub_left_distrib

def sub_mul := @mul_sub_right_distrib


/- others -/


-- in init.set

-- implicit argument in subset should be ⦃ ⦄

-- in nat_lemmas.lean

-- le.elim should be le.dest
