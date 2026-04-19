theory Start
  imports Main
begin

fun conj :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
"conj True True = True" |
"conj _ _ = False"

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc (add m n)"

lemma add_02 : "add m 0 = m"
  apply (induction m)
  apply auto
done

thm add_02

value "1 + (2 :: nat)"
value "1 + (2 :: int)"
value "1 - (2 :: nat)"
value "1 - (2 :: int)"

(* exercise 2.2 *)
theorem add_assoc [simp]: "add (add x y) z = add x (add y z)"
  apply (induction x)
  apply auto
done

declare add_02 [simp]

lemma add_Suc_right [simp]: "add x (Suc y) = Suc (add x y)"
  apply (induction x)
  apply auto
done

theorem add_comm : "add x y = add y x"
  apply (induction x)
  apply auto
done

fun double :: "nat \<Rightarrow> nat" where
"double 0 = 0" |
"double (Suc n) = Suc (Suc (double n))"

value "double 2"
value "double 3"

theorem double_add [simp]: "double m = add m m"
  apply (induction m)
  apply auto
done

(* exercise 2.3 *)
fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count el [] = 0" |
"count el (x # xs) = (if el = x then Suc (count el xs) else count el xs)"

value "count True []"
value "count True [True]"
value "count True [True, False, True]"

theorem count_le_length : "count x xs \<le> length xs"
  apply (induction xs)
  apply auto
done

(* exercise 2.4 *)
fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] y = y # []" |
"snoc (x # xs) y = x # snoc xs y"

value "snoc [] x"
value "snoc [x] y"
value "snoc [x, y] z"

fun reverse :: "'a list \<Rightarrow> 'a list" where
"reverse [] = []" |
"reverse (x # xs) = snoc (reverse xs) x"

value "reverse [x, y, z]"

(* rev (app (rev xs) (Cons x1 Nil)) = Cons x1 xs *)
(* rev (app xs ys) = app (rev ys) (rev xs) *)

(* reverse (snoc (reverse xs) a) = a # xs *)
value "reverse (snoc (reverse [1, 2]) a) = a # [1, 2]"
value "reverse (snoc [2, 1] a) = a # reverse [1, 2]"
(* reverse (snoc xs a) = a # reverse xs *)
lemma reverse_snoc [simp]: "reverse (snoc xs x) = x # reverse xs"
  apply (induction xs)
  apply auto
done

theorem reverse_reverse [simp]: "reverse (reverse xs) = xs"
  apply (induction xs)
  apply auto
done

(* exercise 2.5 *)
fun sum_upto :: "nat \<Rightarrow> nat" where
"sum_upto 0 = 0" |
"sum_upto (Suc n) = Suc n + sum_upto n"

value "sum_upto 0"
value "sum_upto 1"
value "sum_upto 2"
value "sum_upto 100"

theorem gauss_sum : "sum_upto n = n * (n + 1) div 2"
  apply (induction n)
  apply auto
done

type_synonym string = "char list"

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror Tip = Tip" |
"mirror (Node l a r) = Node (mirror r) a (mirror l)"

lemma "mirror (mirror t) = t"
  apply (induction t)
  apply auto
done

fun lookup :: "('a * 'b) list \<Rightarrow> 'a \<Rightarrow> 'b option" where
"lookup [] x = None" |
"lookup ((a, b) # ps) x = (if a = x then Some b else lookup ps x)"

end
