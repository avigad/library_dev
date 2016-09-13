open tactic expr list

meta_definition tactic_of_option {A} : option A → tactic A
| none := failed
| (some a) := return a

meta_definition imp (a b : expr) : expr :=
pi (default name) binder_info.default a b

definition range : ℕ → list ℕ
| (n+1) := n :: range n
| 0 := []

definition option_getorelse {B} (opt : option B) (val : B) : B :=
match opt with
| some x := x
| none := val
end

definition list_empty {A} (l : list A) : bool :=
match l with
| [] := tt
| _::_ := ff
end

private definition list_zipwithindex' {A} : nat → list A → list (A × nat)
| _ nil := nil
| i (x::xs) := (x,i) :: list_zipwithindex' (i+1) xs

definition list_zipwithindex {A} : list A → list (A × nat) :=
list_zipwithindex' 0

definition list_remove {A} : list A → nat → list A
| []      _     := []
| (x::xs) 0     := xs
| (x::xs) (i+1) := x :: list_remove xs i

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
