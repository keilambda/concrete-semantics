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

definition sq :: "nat \<Rightarrow> nat" where
"sq n = n * n"

abbreviation sq' :: "nat \<Rightarrow> nat" where
"sq' n \<equiv> n * n"

fun div2 :: "nat \<Rightarrow> nat" where
"div2 0 = 0" |
"div2 (Suc 0) = 0" |
"div2 (Suc (Suc n)) = Suc (div2 n)"

lemma "div2 n = n div 2"
  apply (induction n rule: div2.induct)
  apply auto
done

(* exercise 2.6 *)
fun contents :: "'a tree \<Rightarrow> 'a list" where
"contents Tip = []" |
"contents (Node l a r) = a # contents l @ contents r"

fun sum_tree :: "nat tree \<Rightarrow> nat" where
"sum_tree Tip = 0" |
"sum_tree (Node l a r) = a + sum_tree l + sum_tree r"

theorem sum_tree_contents : "sum_tree t = sum_list (contents t)"
  apply (induction t)
  apply auto
done

(* exercise 2.7 *)
fun pre_order :: "'a tree \<Rightarrow> 'a list" where
"pre_order Tip = []" |
"pre_order (Node l a r) = a # pre_order l @ pre_order r"

fun post_order :: "'a tree \<Rightarrow> 'a list" where
"post_order Tip = []" |
"post_order (Node l a r) = post_order l @ post_order r @ [a]"

value "pre_order (Node (Node Tip a Tip) b (Node Tip c Tip))"
value "post_order (Node (Node Tip a Tip) b (Node Tip c Tip))"

theorem pre_order_mirror : "pre_order (mirror t) = rev (post_order t)"
  apply (induction t)
  apply auto
done

(* exercise 2.8 *)
fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse a [] = []" |
"intersperse a (x # []) = [x]" |
"intersperse a (x # xs) = x # a # intersperse a xs"

value "intersperse a [x1, x2]"

theorem map_intersperse : "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply (induction xs rule: intersperse.induct)
  apply auto
done

fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"itrev [] ys = ys" |
"itrev (x # xs) ys = itrev xs (x # ys)"

(*
lemma "itrev xs [] = rev xs"
  apply (induction xs)
  apply auto
*)

lemma "itrev xs ys = rev xs @ ys"
  apply (induction xs arbitrary: ys)
  apply auto
done

(* exercise 2.9 *)
fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 n = n" |
"itadd (Suc m) n = itadd m (Suc n)"

theorem itadd_eq_add : "itadd m n = add m n"
  apply (induction m arbitrary: n)
  apply auto
done

(* exercise 2.10 *)
datatype tree0 = Tip0 | Node0 tree0 tree0

fun nodes :: "tree0 \<Rightarrow> nat" where
"nodes Tip0 = 1" |
"nodes (Node0 l r) = 1 + nodes l + nodes r"

value "nodes (Node0 Tip0 Tip0)"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node0 t t)"

(* nodes = 1 *)
value "nodes (explode 0 Tip0)" (* 1 *)
value "nodes (explode 1 Tip0)" (* 3 *)
value "nodes (explode 2 Tip0)" (* 7 *)
value "nodes (explode 3 Tip0)" (* 15 *)
value "nodes (explode 4 Tip0)" (* 31 *)

(* nodes = 3 *)
value "nodes (explode 0 (Node0 Tip0 Tip0))" (* 3 *)
value "nodes (explode 1 (Node0 Tip0 Tip0))" (* 7 *)
value "nodes (explode 2 (Node0 Tip0 Tip0))" (* 15 *)
value "nodes (explode 3 (Node0 Tip0 Tip0))" (* 31 *)

(* nodes = 5 *)
value "nodes (explode 0 (Node0 (Node0 Tip0 Tip0) Tip0))"

value "nodes (Node0 (Node0 (Node0 Tip0 Tip0) Tip0) (Node0 Tip0 Tip0))"

lemma nodes_explode_0 [simp]: "nodes (explode 0 t) = nodes t"
  apply (induction t)
  apply auto
done

lemma nodes_explode_Suc [simp]: "nodes (explode (Suc n) t) = 2 * nodes (explode n t) + 1"
  apply (induction n arbitrary: t)
  apply auto
done

theorem "nodes (explode n t) = 2^n * nodes t + 2^n - 1"
  apply (induction n arbitrary: t)
  apply (auto simp: algebra_simps)
done

lemma "2^n * nodes t + 2^n - 1 = 2^n * (nodes t + 1) - 1"
  apply (induction n arbitrary: t)
  apply (auto simp: algebra_simps)
done

fun explode2 :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode2 0 t = t" |
"explode2 (Suc n) t = Node0 (explode2 n t) (explode2 n t)"

value "nodes (explode2 3 Tip0)" (* 15 *)
value "nodes (explode2 3 (Node0 Tip0 Tip0))" (* 31 *)

lemma [simp]: "explode2 n (Node0 t t) = Node0 (explode2 n t) (explode2 n t)"
  apply (induction n)
  apply auto
done

lemma explode_eq_explode2 : "explode n t = explode2 n t"
  apply (induction n arbitrary: t)
  apply auto
done

end
