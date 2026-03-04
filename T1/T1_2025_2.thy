theory T1_2025_2
  imports Main
begin

(* Integrantes: Carolina Ferreira, Felipe Freitas, Luiza Heller, Mateus Caçabuena *)

primrec cat :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
cateq1: "cat [] ys = ys" |
cateq2: "cat (x#xs) ys = x#cat xs ys"

primrec reverso :: "'a list \<Rightarrow> 'a list" where
reveq1: "reverso [] = []" |
reveq2: "reverso (x#xs) = cat (reverso xs) [x]"

lemma l1: "\<forall>ys zs :: 'a list . cat xs (cat ys zs) = cat (cat xs ys) zs"
proof (induction xs)
  show "\<forall>ys zs :: 'a list . cat [] (cat ys zs) = cat (cat [] ys) zs"
  proof (rule allI, rule allI)
    fix l2::"'a list" and l3::"'a list"
    have "cat [] (cat l2 l3) = cat l2 l3" by (simp only:cateq1)
    also have "... = cat (cat [] l2) l3" by (simp only:cateq1)
    finally show "cat [] (cat l2 l3) = cat (cat [] l2) l3" .
  qed
next
  fix h::'a and l1::"'a list"
  assume HI: "\<forall>ys zs :: 'a list . cat l1 (cat ys zs) = cat (cat l1 ys) zs"
  show "\<forall>ys zs :: 'a list . cat (h#l1) (cat ys zs) = cat (cat (h#l1) ys) zs"
  proof (rule allI, rule allI)
    fix l2::"'a list" and l3::"'a list"
    have "cat (h#l1) (cat l2 l3) = h#(cat l1 (cat l2 l3))" by (simp only:cateq2)
    also have "... = h#(cat (cat l1 l2) l3)" by (simp only:HI)
    also have "... = cat (h#(cat l1 l2)) l3" by (simp only:cateq2)
    also have "... = cat (cat (h#l1) l2) l3" by (simp only:cateq2)
    finally show "cat (h#l1) (cat l2 l3) = cat (cat (h#l1) l2) l3" .
  qed
qed

lemma l2: "cat xs [] = xs"
proof (induction xs)
  case Nil
  then show ?case by (simp only: cateq1)
next
  case (Cons h t)
  then show ?case by (simp only: cateq2)
qed

lemma l3: "\<forall>ys :: 'a list . reverso (cat xs ys) = cat (reverso ys) (reverso xs)"
proof (induction xs)
  case Nil
  then show ?case
  proof (intro allI)
    fix ys :: "'a list"
    have "reverso (cat [] ys) = reverso ys" by (simp only: cateq1)
    also have "... = cat (reverso ys) []" by (simp only: l2 reveq1)
    also have "... = cat (reverso ys) (reverso [])" by (simp only: reveq1)
    finally show "reverso (cat [] ys) = cat (reverso ys) (reverso [])" .
  qed
next
  case (Cons h t)
  then show ?case
  proof (intro allI)
    fix ys :: "'a list"
    have "reverso (cat (h#t) ys) = reverso (h # cat t ys)" by (simp only: cateq2)
    also have "... = cat (reverso (cat t ys)) [h]" by (simp only: reveq2)
    also have "... = cat (cat (reverso ys) (reverso t)) [h]" using Cons.IH by simp
    also have "... = cat (reverso ys) (cat (reverso t) [h])"
      by (simp only: l1)
    also have "... = cat (reverso ys) (reverso (h#t))" by (simp only: reveq2)
    finally show "reverso (cat (h#t) ys) = cat (reverso ys) (reverso (h#t))" .
  qed
qed


theorem t1: "reverso (reverso xs) = xs"
proof (induction xs)
  case Nil
  then show ?case by (simp only: reveq1)
next
  case (Cons h t)
  then show ?case
  proof -
    have "reverso (reverso (h#t)) = reverso (cat (reverso t) [h])" by (simp only: reveq2)
    also have "... = cat (reverso [h]) (reverso (reverso t))"
      using l3[of "reverso t"] by simp
    also have "... = cat [h] (reverso (reverso t))" by (simp only: reveq2 reveq1 cateq1)
    also have "... = cat [h] t" using Cons.IH by simp
    also have "... = h#t" by (simp only: cateq2 cateq1)
    finally show ?case .
  qed
qed

end