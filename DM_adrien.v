Require Import List.
Require Import Compare_dec.
Require Import Arith.

(** Exercice 1 **)

(**
Rappel :
<<
Inductive list (A : Type) : Type :=
 | nil : list A
 | cons : A -> list A -> list A.
>>
**)

(** Variable A : Type.**)
Definition A := nat.

(** Hypothesis dec_A : forall (x y : A), ({x=y}+{~x=y}). **)
Definition dec_A := Nat.eq_dec.

(** Question 1 **)

Fixpoint occ (x : A) (l : list A) :=
  match l with
   | nil => O
   | x' :: l' =>(
   match dec_A x' x with
   | left _ => S (occ x l')
   | right _ => occ x l'
   end)
  end.

(** Eval compute in (occ 0 (cons 4 (cons 4 (cons 3 (cons 1 (cons 2 (cons 4 nil))))))). **)

(** Question 2 **)

Theorem occ_app : forall (x : A) l1 l2,
occ x (app l1 l2) = (occ x l1) + (occ x l2).
Proof.
 intros x l1 l2.
 induction l1.
 simpl. reflexivity.
 simpl.
 destruct (dec_A a x).
 simpl.
 rewrite IHl1.
 reflexivity.
 rewrite IHl1.
 reflexivity.
Qed.

(** Question 3 **)

Theorem occ_filter : forall (P : A -> bool) (a : A) l,
occ a (filter P l) = if (P a) then occ a l else 0.
Proof.
 intros P a l. 
 case_eq (P a).
 intros H.
 induction l.
 simpl.
 reflexivity.
 simpl.
 case_eq (P a0).
 intros H2.
 case_eq (dec_A a0 a).
 intros H3.
 intros H4.
 simpl.
 case_eq (dec_A a0 a).
 intros H7.
 intros H8.
 rewrite IHl.
 reflexivity.
 intros H9.
 contradiction.
 intros H10.
 intros H11.
 simpl.
 case_eq (dec_A a0 a).
 intros H13.
 contradiction.
 intros H14 H15.
 rewrite IHl.
 reflexivity.
 intros H16.
 case_eq (dec_A a0 a).
 intros H17.
 intros H18.
 rewrite <- H17 in H.
 rewrite H in H16.
 discriminate H16.
 intros H17.
 intros H18.
 rewrite IHl.
 reflexivity.
 intros H.
 induction l.
 simpl.
 reflexivity.
 simpl.
 case_eq (P a0).
 intros H18.
 simpl.
 case_eq (dec_A a0 a).
 intros H19 H20.
 rewrite <- H19 in H.
 rewrite H in H18.
 discriminate H18.
 intros H20.
 intros H21.
 rewrite IHl.
 reflexivity.
 intros H21.
 rewrite IHl.
 reflexivity.
Qed.

(** Question 4 **)

Fixpoint map (f : A -> A) (l : list A) :=
  match l with
   | nil => nil
   | x' :: l' => cons (f x') (map f l')
  end.

(** Eval compute in (map (fun x => x+1) (cons 4 (cons 4 (cons 3 (cons 1 (cons 2 (cons 4 nil))))))). **)

Theorem occ_map : exists (f : A -> A) (x : A) (l : list A),
occ (f x) (map f l) <> occ x l.
Proof.
 exists (fun x => 0).
 exists (2).
 exists (cons 2 (cons 3 nil)).
 simpl.
 unfold not.
 intros H.
 discriminate H.
Qed.

(** Question 5 **)

Inductive mem : A -> list A -> Prop :=
| mem_cons : forall x l, mem x (cons x l)
| mem_tail : forall x y l, mem x l -> mem x (cons y l).

Theorem mem_diff : forall (l : list A) (x : A) (y : A), mem x (cons y l) -> x <> y -> mem x l.
Proof.
 intros l x y H1.
 induction l.
 Focus 2.
Admitted.

Theorem mem_null_1 : forall (l : list A) (x : A), occ x l = 0 -> ~(mem x l).
Proof.
 induction l.
 simpl.
 intros x H.
 unfold not.
 intros H1.
 inversion H1.
 simpl.
 intros x.
 case_eq (dec_A a x).
 intros e H1 H2.
 inversion H2.
 intros n H1 H2.
 unfold not.
 intros H3.
 pose (IHl2 := IHl x).
 unfold not in IHl2.
 apply IHl2.
 rewrite H2.
 reflexivity.
 apply mem_diff with (y:=a).
 apply H3.
 unfold not.
 intros H4.
 symmetry in H4.
 contradiction.
Qed.

Theorem mem_null_2 : forall (l : list A) (x : A), ~(mem x l) -> occ x l = 0.
Proof.
 intros l x H.
 unfold not in H.
 induction l.
 simpl.
 reflexivity.
 simpl.
 case_eq (dec_A a x).
 intros e H2.
 rewrite e in H.
 simpl in H.
 unfold not in H.
 unfold not in IHl.
 destruct H.
 destruct IHl.
Admitted.

(** Question 6 **)

Inductive nodup : list A -> Prop :=
| nodup_nil : nodup nil
| nodup_tail : forall x l, ~mem x l -> nodup l -> nodup (cons x l).

Theorem doublon_1 : forall (l : list A) (x : A), nodup l -> occ x l <= 1.
Proof.
 intros l x.
 induction l.
 simpl.
 intros H.
 apply (lt_n_Sm_le 0 1).
 auto.
 simpl.
 intros H5.
 case_eq (dec_A a x).
 intros e H6.
Admitted.


(** Exercice 2  (Implantation des multi-ensembles) **)


(** Variable T : Type.**)
Definition T := nat.

(** Hypothesis T_eq_dec : forall (x y : T), {x=y} + {~x=y}.**)
Definition T_eq_dec := Nat.eq_dec.

(** Rappel :

Inductive list (A:Type) : Type :=
| nil : list A
| cons : A -> list A -> list A .

**)

Definition multiset := list (T*nat).

(** empty est le multiset vide. **)
Definition empty : multiset := nil.
Print empty.

(** TEST
  Eval compute in empty.
**)


(** singleton x crée le multi-ensemble qui ne contient que x en un seul exemplaire **)
Definition singleton (x:T) : multiset := cons (x,1) empty.
Print singleton.

(** TEST
  Eval compute in (singleton 2). 
**)


(** add x n s ajoute, au multi-ensemble s, n occurrences de l’élément x dans s **)
Fixpoint add (x:T) (n:nat) (s:multiset) : multiset := 
  match s with
  | nil => (x,n) :: empty
  | (x',occ) :: l' => (
    match (T_eq_dec x x') with
    | left _ => (x',occ+n) :: l'
    | right _ => (x',occ) :: (add x n l')
   end)
  end.
Print add.

(** TESTS
  Eval compute in (add 2 3 empty).
  Eval compute in (add 2 4 (add 2 5 empty)).
  Eval compute in (add 3 3 (singleton 2)). 
**)


(** member x s retourne la valeur true si x a au moins une occurrence dans s, false sinon. **)
Fixpoint member (x:T) (s:multiset) : bool := 
  match s with
  | nil => false
  | (x',occ) :: l' => (
    match (T_eq_dec x x') with
    | left _ => true
    | right _ => member x l'
   end)
  end.
Print member.

(** TESTS
  Eval compute in (member 2 (add 2 3 empty)).
  Eval compute in (member 3 (add 2 5 empty)).
  Eval compute in (member 1 (singleton 2)). 
  Eval compute in (member 1 empty).
**)


(** union fait l’union de deux multi-ensembles. **)
Fixpoint union (s1:multiset) (s2:multiset) : multiset :=
  match s1 with
  | nil => s2
  | (x',occ) :: l' => union l' (add x' occ s2)
  end.
Print union.

(** TESTS
  Eval compute in (union (add 2 3 empty) (add 2 4 empty)).
  Eval compute in (union (add 2 3 (add 4 5 empty)) (add 2 3 empty)).
  Eval compute in (union (add 2 3 empty) empty).
  Eval compute in (union empty empty).
**)


(** muliplicity x s retourne le nombre d’occurrences de x dans s **)
Fixpoint multiplicity (x:T) (s:multiset) : nat := 
  match s with
  | nil => 0
  | (x',occ) :: l' => (
    match (T_eq_dec x x') with
    | left _ => occ
    | right _ => multiplicity x l'
   end)
  end.
Print multiplicity.

(** TESTS
  Eval compute in (multiplicity 2 (add 2 7 empty)).
  Eval compute in (multiplicity 3 (add 2 7 empty)).
  Eval compute in (multiplicity 3 empty).
**)


(** removeOne x s retourne le multi-ensemble s avec une occurrence de moins pour x. Si s ne contient pas x, le multi-ensemble résultat est s. **)

Fixpoint removeOne (x:T) (s:multiset) : multiset :=
  match s with
  | nil => nil
  | (x', occ) :: l' => (
    match (T_eq_dec x x') with
    | left _ => (
      match (le_lt_dec occ 1) with
      | left _ => l'
      | right _ => (x', occ-1) :: l'
      end)
    | right _ => (x', occ) :: (removeOne x l')
   end)
  end.
Print removeOne.
  
(** TESTS
  Eval compute in (removeOne 2 (add 2 7 empty)).
  Eval compute in (removeOne 2 (add 2 2 (add 3 5 empty))).
  Eval compute in (removeOne 2 (add 6 5 (add 2 2 (add 3 5 empty)))).
  Eval compute in (removeOne 2 (add 2 1 (add 3 5 empty))).
  Eval compute in (removeOne 2 (add 6 5 (add 2 1 (add 3 5 empty)))).
  Eval compute in (removeOne 3 (add 2 7 empty)).
  Eval compute in (removeOne 3 empty).
**)


(** removeAll x s retourne le mult-ensemble s o`u x n’apparait plus. Si s ne contient pas x, le multiensemble r´esultat est s. **)

Fixpoint removeAll (x:T) (s:multiset) : multiset :=
  match s with
  | nil => nil
  | (x', occ) :: l' => (
    match (T_eq_dec x x') with
    | left _ => l'
    | right _ => (x', occ) :: removeAll x l'
   end)
  end.
Print removeAll.

(** TESTS
  Eval compute in (removeAll 2 (add 2 7 empty)).
  Eval compute in (removeAll 2 (add 2 2 (add 3 5 empty))).
  Eval compute in (removeAll 2 (add 6 5 (add 2 2 (add 3 5 empty)))).
  Eval compute in (removeAll 2 (add 2 1 (add 3 5 empty))).
  Eval compute in (removeAll 2 (add 6 5 (add 2 1 (add 3 5 empty)))).
  Eval compute in (removeAll 3 (add 2 7 empty)).
  Eval compute in (removeAll 3 empty).
**)

(** Ce prédicat spécifie qu’un élément appartient à un multi-ensemble dès lors 
qu’il en existe une occurrence **)
Inductive InMultiset : T -> multiset -> Prop :=
  | inMultiset_cons : forall x v l, InMultiset x (cons (x,v) l)
  | inMultiset_tail : forall x y l, InMultiset x l -> InMultiset x (cons y l).

(** Ce prédicat spécifie qu’une liste qui représente un multi-ensemble est bien formée, c'est-à-dire que tout élément de T apparaît dans au plus un seul couple et que tous les nombres d’occurrences sont des entiers naturels non nuls. **)
Inductive wf (l: multiset) : Prop :=
  | wf_intro : (forall x, member x (removeAll x l) = false /\ (member x l = true -> (multiplicity x l) > 0)) -> wf l.

Theorem empty_wf : wf empty.
Proof.
  apply wf_intro.
  intro x.
  split.
  simpl.
  reflexivity.
  simpl.
  intros H.
  discriminate H.
Qed. 

   
Theorem singleton_wf : forall (x:T), wf (singleton x).
Proof.
  intro x.
  apply wf_intro.
  intros x0.
  simpl.
  split.
  destruct (T_eq_dec x0 x).
  simpl.
  reflexivity.
  simpl.
  destruct (T_eq_dec x0 x).
  contradiction.
  reflexivity.
  destruct (T_eq_dec x0 x).
  intros H.
  apply (le_lt_n_Sm 0 0).
  reflexivity.
  intros H.
  discriminate H.
Qed. 


Lemma union_add : forall (x:T) (n:nat) (l: multiset), union l ((x,n)::empty) = add x n l.
Proof.
Admitted.

Lemma union_assoc : forall (l1: multiset) (l2: multiset) (l3: multiset), union (union l1 l2) l3 = union l1 (union l2 l3).
Proof.
Admitted.

Theorem add_wf : forall (x:T) (n:nat) (l: multiset), wf l -> wf (add x n l).
Proof.
  intros x n l well_formed_proof.
  apply wf_intro.
  intros x0.
  split.
  inversion well_formed_proof.
  pose (H0 := H x0).
  destruct H0.
  
  apply wf_intro.
  simpl.
(**   intros x0.
  split.
  destruct (T_eq_dec x0 x).
  simpl.
  reflexivity.
  simpl.
  destruct (T_eq_dec x0 x).
  contradiction.
  reflexivity.
  destruct (T_eq_dec x0 x).
  intros H.
 split.
  destruct (T_eq_dec x0 x).
  simpl.
  reflexivity.
  contradiction.
  destruct (T_eq_dec x0 x).
  simpl.
  destruct (T_eq_dec x0 x).
  contradiction.
  reflexivity.
  simpl.
  destruct (T_eq_dec x0 x).
  intros H.
  
  apply wf_intro.
  intros x0.
  split.
  simpl.
  destruct (T_eq_dec x0 x).
  simpl.
  reflexivity.
  simpl.
  destruct (T_eq_dec x0 x).
  contradiction.
  reflexivity.
  simpl.
  destruct (T_eq_dec x0 x).
  intros H.
  discriminate well_formed_proof.**)
Admitted.

Theorem x_not_in_empty_Multiset : forall (x : T), ~InMultiset x empty.
Proof.
 intros x.
 unfold not.
 intros H.
 inversion H.
Qed.

Theorem x_equal_y : forall x y , InMultiset y (singleton x) <-> x = y.
Proof.
 intros x y.
 unfold iff.
 split.
 intros H.
 inversion H.
 reflexivity.
 inversion H2.
 intros H.
 rewrite H.
 apply inMultiset_cons.
Qed.


Theorem x_multiplicity_1 :forall x, multiplicity x (singleton x) = 1.
Proof.
 intros x.
 unfold singleton.
 simpl.
 destruct (T_eq_dec x x).
 reflexivity.
 contradiction.
Qed.

Theorem wf_and_member : forall x s, wf s -> (member x s = true <-> InMultiset x s).
Proof.
 intros x s.
 induction s.
 intros H.
 unfold iff.
 split.
 simpl.
 intros H2.
 discriminate H2.
 simpl.
 intros H2.
 inversion H2.
 intros H1.
 unfold iff.
 split.
 inversion H1.
Admitted.

Theorem add_x_in_s : forall x n s, n > 0 -> InMultiset x (add x n s).
Proof.
 intros x n s.
 intros H.
 induction s.
 simpl.
 apply inMultiset_cons.
 unfold add in IHs.
 unfold add.
Admitted.

Theorem x_diff_y_multiset : forall x n y s, x <> y -> (InMultiset y (add x n s) <-> InMultiset y s).
Proof.
 intros x n y s.
 intros H.
 unfold iff.
 split.
Admitted.























