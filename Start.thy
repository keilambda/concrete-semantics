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

declare [[names_short]]

datatype 'a list = Nil | Cons 'a "'a list"

fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"app Nil ys = ys" |
"app (Cons x xs) ys = Cons x (app xs ys)"

fun rev :: "'a list \<Rightarrow> 'a list" where
"rev Nil = Nil" |
"rev (Cons x xs) = app (rev xs) (Cons x Nil)"

value "rev (Cons True (Cons False Nil))"
value "rev (Cons a (Cons b Nil))"

lemma app_Nil2 [simp]: "app xs Nil = xs"
  apply (induction xs)
  apply auto
done

lemma app_assoc [simp]: "app (app xs ys) zs = app xs (app ys zs)"
  apply (induction xs)
  apply auto
done

lemma rev_app [simp]: "rev (app xs ys) = app (rev ys) (rev xs)"
  apply (induction xs)
  apply auto
done

theorem rev_rev [simp]: "rev (rev xs) = xs"
  apply (induction xs)
  apply auto
done

end