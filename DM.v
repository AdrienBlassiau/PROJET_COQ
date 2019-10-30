Require Import List.
Require Import Omega.

(******************************************************************************)
(**************************** DM COQ 2019-2020 ********************************)
(******************************************************************************)
(******************************************************************************)
(***************************# Adrien BLASSIAU #********************************)
(***************************# Corentin JUVIGNY #*******************************)
(******************************************************************************)
(******************************************************************************)
(******* PREUVES RÉUSSIES : 41 ************************************************)
(******* PREUVES ADMISES :   7 ************************************************)
(******************************************************************************)


(******************************************************************************)
(******************************************************************************)
(********************** Exercice 1 (Listes et comptage) ***********************)
(******************************************************************************)
(******************************************************************************)
(****** PREUVES RÉUSSIES : 7 **************************************************)
(****** PREUVES ADMISE :   1 **************************************************)
(******************************************************************************)


(** Dans la suite on travaille avec un type A quelconque muni d’une égalité 
    décidable. Pour les tests, on utilise nat. **)

Variable A : Type.
(**Definition A := nat.**)

Hypothesis dec_A : forall (x y : A), ({x=y}+{~x=y}).
(**Definition dec_A := Nat.eq_dec.**)

(****************)
(** Question 1 **)
(****************)

(** occ prend en argument un élément x de type A et une liste l de type (list A) 
    et retourne le nombre d’occurrences de x dans l. **)
Fixpoint occ (x : A) (l : list A) :=
  match l with
   | nil => O
   | x' :: l' =>(
   match dec_A x' x with
   | left _ => S (occ x l')
   | right _ => occ x l'
   end)
  end.
Check occ.
(** TESTS
  Eval compute in (occ 0 (cons 4 (cons 4 (cons 3 (cons 1 (cons 2 (cons 4 nil))))))).
  Eval compute in (occ 4 (cons 4 (cons 4 (cons 3 (cons 1 (cons 2 (cons 4 nil))))))).
  Eval compute in (occ 4 nil).
**)

(****************)
(** Question 2 **)
(****************)

Theorem occ_app : forall (x : A) l1 l2,
occ x (app l1 l2) = (occ x l1) + (occ x l2).
Proof.
 intros x l1 l2.
 induction l1.
 + simpl. reflexivity.
 + simpl. destruct (dec_A a x).
   - simpl. rewrite IHl1. reflexivity.
   - rewrite IHl1. reflexivity.
Qed.

(****************)
(** Question 3 **)
(****************)

Theorem occ_filter : forall (P : A -> bool) (a : A) l,
occ a (filter P l) = if (P a) then occ a l else 0.
Proof.
 intros P a l.
 induction l.
 + case_eq (P a).
   - intros H. simpl. reflexivity.
   - simpl. reflexivity.
 + case_eq (P a) ;intros H2 ; rewrite H2 in IHl.
   - case_eq (dec_A a0 a).
     * intros H3 H4. simpl. rewrite H3. rewrite H2. rewrite H3 in H4. 
       simpl. rewrite H4. rewrite IHl. reflexivity.
     * intros n H3. simpl. rewrite H3.
       case_eq(P a0) ; intros H4.
       ** simpl. rewrite H3. assumption.
       ** assumption.
   - simpl. case_eq (dec_A a0 a).
     * intros H7. intros H8. rewrite H7. rewrite H2. assumption.
     * intros H1 H3.
       case_eq(P a0) ; intros H4.
       ** simpl. rewrite H3. assumption.
       ** assumption.
Qed.

(****************)
(** Question 4 **)
(****************)

(** map applique une fonction f de type A -> A sur tous les éléments d’une liste. **)
Fixpoint map (f : A -> A) (l : list A) :=
  match l with
   | nil => nil
   | x' :: l' => cons (f x') (map f l')
  end.
Check map.
(** TESTS
  Eval compute in (map (fun x => x+1) (cons 4 (cons 4 (cons 3 (cons 1 (cons 2 (cons 4 nil))))))).
**)


(** L'énoncé semble éronné. Si on prend deux éléments y et z distinct dans 
    l'ensemble A, on peut construire une fonction f qui rend l'énoncé faux ! **)
Theorem occ_map : forall (y:A) (z:A), y<>z -> exists (f : A -> A) (x : A) (l : list A),
occ (f x) (map f l) <> occ x l.
Proof.
 intros y z H.
 exists (fun x => y). exists (y). exists (cons y (cons z nil)). simpl.
 unfold not. intros H1.
 case_eq (dec_A y y).
 + intros e H2. rewrite H2 in H1.
   case_eq(dec_A z y).
   - intros e0 H3. pose(e':=e0). symmetry in e'. contradiction.
   - intros n H3. rewrite H3 in H1. omega.
 + contradiction.
Qed.

(****************)
(** Question 5 **)
(****************)

Inductive mem : A -> list A -> Prop :=
| mem_cons : forall x l, mem x (cons x l)
| mem_tail : forall x y l, mem x l -> mem x (cons y l).

(** Un preuve intermédiaire ... **)
Lemma mem_diff : forall (l : list A) (x : A) (y : A), mem x (cons y l) -> x <> y -> mem x l.
Proof.
 intros l x y H1. induction l ; 
 intros H.
 + inversion H1.
   - contradiction.
   - assumption.
 + inversion H1.
   - apply mem_tail. rewrite <- H3. apply IHl.
     * rewrite H3. apply mem_cons.
     * assumption.
   - assumption.
Qed.

Theorem mem_null_1 : forall (l : list A) (x : A), occ x l = 0 -> ~(mem x l).
Proof.
 induction l ; simpl.
 + intros x H. unfold not. intros H1. inversion H1.
 + intros x.
   case_eq (dec_A a x).
   - intros e H1 H2. inversion H2.
   - intros n H1 H2. unfold not. intros H3. pose (IHl2 := IHl x). unfold not in IHl2.
     apply IHl2.
     * rewrite H2. reflexivity.
     * apply mem_diff with (y:=a).
       apply H3. unfold not. intros H4. symmetry in H4. contradiction.
Qed.

Theorem mem_null_2 : forall (l : list A) (x : A), ~(mem x l) -> occ x l = 0.
Proof.
 intros l x H. unfold not in H. 
 induction l ; simpl.
 + reflexivity.
 + case_eq (dec_A a x).
   - intros e H2. rewrite e in H. pose(H3:= mem_cons x l). pose(H':=H H3).
     destruct H'.
   - intros n H1. apply IHl. intros H2. apply mem_tail with (y:=a) in H2. apply H.
     assumption.
Qed.

(****************)
(** Question 6 **)
(****************)

Inductive nodup : list A -> Prop :=
| nodup_nil : nodup nil
| nodup_tail : forall x l, ~mem x l -> nodup l -> nodup (cons x l).

Theorem doublon_1 : forall (l : list A) (x : A), nodup l -> occ x l <= 1.
Proof.
 intros l x H.
 induction l.
 + simpl. omega.
 + inversion H. unfold not in H2. simpl.
   case_eq (dec_A a x).
   * intros e H4. pose (H':=IHl H3). rewrite e in H2. apply mem_null_2 in H2.
     rewrite H2. omega.
   * intros n H4. apply IHl.
     assumption.
Qed.

(** Nous n'avons pas réussi à démontrer la preuve dans ce sens ... **)
Theorem doublon_2 : forall (l : list A) (x : A), occ x l <= 1 -> nodup l.
Proof.
 intros l.
 induction l ; intros x H.
 + apply nodup_nil.
 + simpl in H.
   case_eq (dec_A a x).
   - intros e H1. rewrite H1 in H. 
     apply (nodup_tail).
     * unfold not. intros H2.
       case_eq(Nat.eq_dec (occ x l) 0).
       ** intros e0 H3. pose(H4:=mem_null_1 l x). pose(H5:=H4 e0). 
          rewrite <- e in H5. contradiction.
       ** intros n H3. omega.
     * apply (IHl x). omega.
   - intros n H1.
     apply nodup_tail.
     * unfold not. intros H2. rewrite H1 in H. pose(H':=IHl x). pose(H'':=H' H). 
       inversion H2.
Admitted.

(******************************************************************************)
(******************************************************************************)
(*************** Exercice 2  (Implantation des multi-ensembles) ***************)
(******************************************************************************)
(******************************************************************************)
(****** PREUVES RÉUSSIES : 34 *************************************************)
(****** PREUVES ADMISES :   6 *************************************************)
(******************************************************************************)


(** Dans la suite on travaille avec un type T quelconque muni d’une égalité 
    décidable. Pour les tests, on utilise nat. **)

Variable T : Type.
(**Definition T := nat.**)

Hypothesis T_eq_dec : forall (x y : T), {x=y} + {~x=y}.
(**Definition T_eq_dec := Nat.eq_dec.**)


(******************************************************************************)
(****2.1 Implantation des multi-ensembles à l’aide de listes d’association*****)
(******************************************************************************)
(****** PREUVES RÉUSSIES : 18 *************************************************)
(****** PREUVES ADMISES :   6 *************************************************)
(******************************************************************************)

(****************)
(** Question 1 **)
(****************)

Definition multiset := list (T*nat).

(** empty est le multiset vide. **)
Definition empty : multiset := nil.
Check empty.
(** TEST
  Eval compute in empty.
**)


(** singleton x crée le multi-ensemble qui ne contient que x en un seul exemplaire **)
Definition singleton (x:T) : multiset := cons (x,1) empty.
Check singleton.
(** TEST
  Eval compute in (singleton 2). 
**)


(** add x n s ajoute, au multi-ensemble s, n occurrences de l’élément x dans s **)
Fixpoint add (x:T) (n:nat) (s:multiset) : multiset := if (le_lt_dec n 0) then s else
  match s with
  | nil => (x,n) :: empty
  | (x',occ) :: l' => (
    match (T_eq_dec x x') with
    | left _ => (x',occ+n) :: l'
    | right _ => (x',occ) :: (add x n l')
   end)
  end.
Check add.
(** TESTS
  Eval compute in (add 2 3 empty).
  Eval compute in (add 2 4 (add 2 5 empty)).
  Eval compute in (add 3 3 (singleton 2)). 
**)


(** member x s retourne la valeur true si x a au moins une occurrence dans s, 
    false sinon. **)
Fixpoint member (x:T) (s:multiset) : bool := 
  match s with
  | nil => false
  | (x',occ) :: l' => (
    match (T_eq_dec x x') with
    | left _ => true
    | right _ => member x l'
   end)
  end.
Check member.
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
Check union.
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
Check multiplicity.
(** TESTS
  Eval compute in (multiplicity 2 (add 2 7 empty)).
  Eval compute in (multiplicity 3 (add 2 7 empty)).
  Eval compute in (multiplicity 3 empty).
**)


(** removeOne x s retourne le multi-ensemble s avec une occurrence de moins 
    pour x. Si s ne contient pas x, le multi-ensemble résultat est s. **)
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
Check removeOne.
(** TESTS
  Eval compute in (removeOne 2 (add 2 7 empty)).
  Eval compute in (removeOne 2 (add 2 2 (add 3 5 empty))).
  Eval compute in (removeOne 2 (add 6 5 (add 2 2 (add 3 5 empty)))).
  Eval compute in (removeOne 2 (add 2 1 (add 3 5 empty))).
  Eval compute in (removeOne 2 (add 6 5 (add 2 1 (add 3 5 empty)))).
  Eval compute in (removeOne 3 (add 2 7 empty)).
  Eval compute in (removeOne 3 empty).
**)


(** removeAll x s retourne le mult-ensemble s o`u x n’apparait plus. 
    Si s ne contient pas x, le multiensemble r´esultat est s. **)
Fixpoint removeAll (x:T) (s:multiset) : multiset :=
  match s with
  | nil => nil
  | (x', occ) :: l' => (
    match (T_eq_dec x x') with
    | left _ => l'
    | right _ => (x', occ) :: removeAll x l'
   end)
  end.
Check removeAll.
(** TESTS
  Eval compute in (removeAll 2 (add 2 7 empty)).
  Eval compute in (removeAll 2 (add 2 2 (add 3 5 empty))).
  Eval compute in (removeAll 2 (add 6 5 (add 2 2 (add 3 5 empty)))).
  Eval compute in (removeAll 2 (add 2 1 (add 3 5 empty))).
  Eval compute in (removeAll 2 (add 6 5 (add 2 1 (add 3 5 empty)))).
  Eval compute in (removeAll 3 (add 2 7 empty)).
  Eval compute in (removeAll 3 empty).
**)

(****************)
(** Question 2 **)
(****************)

(********************)
(** Question 2. a) **)
(********************)

(** Ce prédicat spécifie qu’un élément appartient à un multi-ensemble dès lors 
    qu’il en existe une occurrence **)
Inductive InMultiset (x:T) (l:multiset) : Prop := 
  | inMultiset_intro : member x l = true -> InMultiset x l.
 
 
(********************)
(** Question 2. b) **)
(********************)

(** Ce prédicat spécifie qu’une liste qui représente un multi-ensemble est bien 
    formée, c'est-à-dire que tout élément de T apparaît dans au plus un seul couple 
    et que tous les nombres d’occurrences sont des entiers naturels non nuls. **)
Inductive wf (l: multiset) : Prop :=
  | wf_intro : (forall x, (InMultiset x (removeAll x l) -> False) /\ (member x l = true -> (multiplicity x l) > 0)) -> wf l.


(********************)
(** Question 2. c) **)
(********************)

(** empty possède-t-elle un résultat bien formé ? **)
Theorem empty_wf : wf empty.
Proof.
  apply wf_intro. intro x. split; simpl ; intros H.
  + inversion H. discriminate H0.
  + discriminate H.
Qed. 

(** singleton possède-t-elle un résultat bien formé ? **)
Theorem singleton_wf : forall (x:T), wf (singleton x).
Proof.
  intro x. apply wf_intro. intros x0. simpl.
  split.
  + case_eq (T_eq_dec x0 x).
    - intros e H H1. inversion H1. discriminate H0.
    - intros n H1 H2. inversion H2. simpl in H.
      case_eq (T_eq_dec x0 x).
      * intros e. contradiction.
      * intros H3 H4. rewrite H1 in H. discriminate H.
  + case_eq (T_eq_dec x0 x).
    - intros e H1 H2. omega.
    - intros n H1 H2. discriminate H2.
Qed.

(** Un preuve intermédiaire ... **)
Lemma plus_n_0 : forall n, n + O = n.
Proof.
induction n.
+ simpl. reflexivity.
+ simpl. rewrite IHn. reflexivity.
Qed.

(** Un preuve intermédiaire ... **)
Lemma wf_plus_n : forall t n0 n l, wf ((t, n0) :: l) -> wf ((t, n0+n) :: l).
Proof.
intros t n0 n l H.
induction n.
+ rewrite plus_n_0. assumption.
+ apply wf_intro. intros x. split.
  - simpl.
    case_eq(T_eq_dec x t).
    * intros e H1 H2. inversion H2. rewrite e in H0. inversion IHn. pose(H4:=H3 x).
      destruct H4. simpl in H4. rewrite H1 in H4. pose(H6:=H4 H2). destruct H6.
    * intros n1 H1 H2. inversion H2. simpl in H0. rewrite H1 in H0. inversion H.
      pose(H4:=H3 x). destruct H4. simpl in H4. rewrite H1 in H4.
      apply H4. apply inMultiset_intro. simpl. rewrite H1. exact H0.
  - intros H1. simpl in H1.
    case_eq(T_eq_dec x t).
    * intros e H2. simpl. rewrite H2. omega.
    * intros n1 H2. rewrite H2 in H1. simpl. rewrite H2. inversion H. pose(H3:=H0 x).
      destruct H3. simpl in H4. rewrite H2 in H4. rewrite H1 in H4. apply H4. reflexivity.
Qed.


(** Nous n'avons pas réussi à démontrer que add preserve les propriétés de 
    bonne formation ... **)
Theorem add_wf : forall (x:T) (n:nat) (l: multiset), wf l -> wf (add x n l).
Proof.
intros x n l H. inversion H. pose(H1:=H0 x). destruct H1.
induction l ; simpl.
+ case_eq(le_lt_dec n 0).
  - intros l H3. assumption.
  - intros l H3. apply wf_intro. intros x0. split.
    * simpl.
      case_eq(T_eq_dec x0 x) ; intros e H4 H5 ; inversion H5 ; simpl in H6.
      ** discriminate H6.
      ** rewrite H4 in H6. discriminate H6.
    * simpl.
      case_eq(T_eq_dec x0 x).
      ** intros e H4. omega.
      ** intros n0 H4 H5. discriminate H5.
+ case_eq(le_lt_dec n 0) ;intros l0 H3.
  - assumption.
  - destruct a.
    case_eq(T_eq_dec x t).
    * intros e H4. apply wf_plus_n. assumption.
    * intros n1 H4. apply wf_intro. intros x0. 
      split.
      ** intros H5. inversion H5. simpl in H6. 
         case_eq(T_eq_dec x0 t).
         *** intros e H7.
             rewrite H7 in H6. rewrite e in H6. simpl in H2. rewrite H4 in H2. inversion H5.
Admitted.

(** Nous n'avons pas réussi à démontrer que union preserve les propriétés de 
    bonne formation ... **)
Theorem union_wf : forall (l: multiset) (l': multiset), wf l -> wf l' -> wf (union l l').
Proof.
intros l l' well_formed_proof_of_l well_formed_proof_of_l'.
apply wf_intro.
intros x.
destruct well_formed_proof_of_l.
pose (H1 := H x).
destruct H1.
destruct well_formed_proof_of_l'.
pose (H3 := H2 x).
destruct H3.
split.
Admitted.

(** Nous n'avons pas réussi à démontrer que removeOne preserve les propriétés de 
    bonne formation ... **)
Theorem removeOne_wf: forall (x: T) (l: multiset), wf l -> wf (removeOne x l).
Proof.
intros x l H.
induction l.
+ simpl. assumption.
+ destruct a. simpl.
  case_eq(T_eq_dec x t).
  - intros e H1.
    case_eq(le_lt_dec n 1).
    * intros l0 H2. apply wf_intro. intros x0.
      split.
      ** intros H3. inversion H.
Admitted.

(** Nous n'avons pas réussi à démontrer que removeAll preserve les propriétés de 
    bonne formation ... **)
Theorem removeAll_wf: forall (x: T) (l: multiset), wf l -> wf (removeAll x l).
Proof.
intros x l H.
induction l.
+ simpl. assumption.
+ destruct a. simpl.
  case_eq(T_eq_dec x t).
  - intros e H1. inversion H.
    pose(H':=H0 x). destruct H'. apply wf_intro. intros x0. split.
Admitted.


(*****************)
(** Question 3. **)
(*****************)

Theorem proof_1_1 : forall (x : T), ~InMultiset x empty.
Proof.
 intros x. unfold not. intros H. inversion H. discriminate H0.
Qed.

Theorem proof_2_1 : forall x y , InMultiset y (singleton x) <-> x = y.
Proof.
 intros x y. unfold iff.
 split ; intros H.
 + inversion H. simpl in H0.
   case_eq (T_eq_dec y x).
   - intros e H2. rewrite e. reflexivity.
   - intros n H2. rewrite H2 in H0. discriminate H0.
 + apply inMultiset_intro. simpl.
   case_eq (T_eq_dec y x).
   - intros e H2. reflexivity.
   - intros n. symmetry in H. contradiction.
Qed.

Theorem proof_3_1 :forall x, multiplicity x (singleton x) = 1.
Proof.
 intros x. unfold singleton. simpl.
 destruct (T_eq_dec x x).
 + reflexivity.
 + contradiction.
Qed.

Theorem proof_4_1 : forall x s, wf s -> (member x s = true <-> InMultiset x s).
Proof.
intros x s well_formed_proof_of_l. unfold iff.
split ; intros H.
+ destruct well_formed_proof_of_l. pose (H1:=H0 x). destruct H1. apply inMultiset_intro. exact H.
+ inversion H. exact H0.
Qed.

Theorem proof_5_1 : forall x n s, n > 0 -> InMultiset x (add x n s).
Proof.
 intros x n s H. apply inMultiset_intro.
 induction s.
 + simpl.
   case_eq (le_lt_dec n 0) ; intros l H2.
   - apply (gt_not_le n 0) in H. contradiction.
   - simpl.
     destruct (T_eq_dec x x).
     * reflexivity.
     * unfold not in n0. destruct n0. reflexivity.
 + destruct a.
   case_eq (T_eq_dec t x).
   - intros e H1. rewrite e. simpl.
     case_eq (le_lt_dec n 0).
     * intros l. apply (gt_not_le n 0) in H. contradiction.
     * intros l H2. destruct (T_eq_dec x x) ; simpl.
       ** destruct (T_eq_dec x x).
          *** reflexivity.
          *** contradiction.
       ** destruct (T_eq_dec x x).
          *** reflexivity.
          *** exact IHs.
   - intros n1 H1. simpl.
     case_eq (le_lt_dec n 0).
     * intros l. apply (gt_not_le n 0) in H. contradiction.
     * intros l H2.
       case_eq (T_eq_dec x t).
       ** intros e. pose (f:=e). symmetry in f. contradiction.
       ** intros n2 H3. simpl.
          destruct (T_eq_dec x t).
          *** reflexivity.
          *** exact IHs.
Qed.

Theorem proof_6_1 : forall x n y s, x <> y -> (InMultiset y (add x n s) <-> InMultiset y s).
Proof.
 intros x n y s H. unfold iff.
 split.
 + intros H2. inversion H2. apply inMultiset_intro.
   induction s.
   - simpl. simpl in H0. case_eq (le_lt_dec n 0) ; intros l H1 ; rewrite H1 in H0 ; simpl in H0.
     * discriminate H0.
     * case_eq (T_eq_dec y x).
       ** intros e H3. pose(e':=e). symmetry in e'. contradiction.
       ** intros n0 H4. rewrite H4 in H0. discriminate H0.
   - destruct a.
     case_eq (T_eq_dec t y).
     * intros e H3. rewrite e. simpl.
       case_eq (T_eq_dec y y).
       ** reflexivity.
       ** contradiction.
     * intros n1 H3. simpl.
       case_eq (T_eq_dec y t).
       ** intros e. pose(e':=e). symmetry in e'. contradiction.
       ** intros n2 H4. simpl in H2.
          case_eq (le_lt_dec n 0); intros l H5 ; rewrite H5 in H2.
          *** inversion H2. simpl in H1. rewrite H4 in H1. assumption.
          *** case_eq (T_eq_dec x t).
              **** intros e H6. rewrite H6 in H2. rewrite e in H0. simpl in H0. 
                   rewrite H5 in H0. 
                   case_eq (T_eq_dec t t);intros e0 H7 ;rewrite H7 in H0; simpl in H0 ;rewrite H4 in H0.
                   ***** assumption.
                   ***** apply IHs.
                         ****** apply inMultiset_intro. rewrite e. exact H0.
                         ****** rewrite e. exact H0.
              **** intros n3 H6. rewrite H6 in H2. simpl in H0. rewrite H5 in H0.
                   rewrite H6 in H0. simpl in H0. rewrite H4 in H0. apply IHs.
                   ***** apply inMultiset_intro.
                         exact H0.
                   ***** exact H0.
 + intros H1. inversion H1. apply inMultiset_intro.
   induction s.
   - simpl.
     case_eq (le_lt_dec n 0) ; intros l H2.
     * exact H0.
     * simpl.
       case_eq (T_eq_dec y x).
       ** intros e H3. reflexivity.
       ** simpl in H0. discriminate H0.
   - destruct a.
     case_eq (T_eq_dec t x).
     * intros e H2. rewrite e. simpl.
       case_eq(le_lt_dec n 0).
       ** intros l H3. simpl.
          case_eq (T_eq_dec y x).
          *** intros e0. pose(e':=e0). symmetry in e'. contradiction.
          *** intros n1 H4. simpl in H0. case_eq (T_eq_dec y t).
              **** intros e0 H5. rewrite e0 in H. pose(e':=e). symmetry in e'. contradiction.
              **** intros n2 H5. rewrite H5 in H0. assumption.
       ** intros l H3. 
          case_eq (T_eq_dec x x).
          *** intros e0 H4. simpl.
              case_eq(T_eq_dec y x).
              **** intros e1 H5. reflexivity.
              **** intros n1 H5. simpl in H0.
                   case_eq (T_eq_dec y t) ;  intros e1 H6.
                   ***** rewrite e1 in H. pose(e':=e). symmetry in e'. contradiction.
                   ***** rewrite H6 in H0. assumption.
          *** contradiction.
     * intros n1 H2. simpl.
       case_eq(le_lt_dec n 0) ; intros l H3.
       ** simpl.
          case_eq(T_eq_dec y t) ; intros e H4.
          *** reflexivity.
          *** simpl in H0. rewrite H4 in H0. assumption.
       ** case_eq(T_eq_dec x t) ; intros n2 H4 ; simpl.
          *** case_eq(T_eq_dec y t) ; intros e0 H5.
              **** reflexivity.
              **** simpl in H0. rewrite H5 in H0. assumption.
          *** case_eq(T_eq_dec y t).
              **** intros e H5. reflexivity.
              **** intros n3 H5. apply IHs.
                   apply inMultiset_intro.
                   ***** simpl in H0. rewrite H5 in H0. assumption.
                   ***** simpl in H0. rewrite H5 in H0. assumption.
Qed.

(** Un preuve intermédiaire ... **)
Lemma proof_7_1_1: forall x s, multiplicity x s <> 0 -> InMultiset x s.
Proof.
intros x s. intros H. apply inMultiset_intro.
induction s.
+ simpl in H. omega.
+ destruct a.
  case_eq (T_eq_dec x t) ; intros e H1.
  - rewrite e in H. simpl in H.
    case_eq (T_eq_dec t t).
    * intros e0 H2. rewrite e. simpl. rewrite H2. reflexivity.
    * intros n0. unfold not in n0. intros H2. rewrite e in H1. contradiction.
  - simpl. rewrite H1. simpl in H. rewrite H1 in H. apply IHs. assumption.
Qed.

Theorem proof_7_1_2 : forall x s, wf s -> (multiplicity x s = 0 <-> ~InMultiset x s).
Proof.
intros x s well_formed_proof_of_l. unfold iff. 
split.
+ unfold not. intros H1 H2. destruct H2. destruct well_formed_proof_of_l. 
  pose (H2:= H0 x). destruct H2. apply H3 in H. rewrite H1 in H. omega.
+ intros H2. unfold not in H2. destruct well_formed_proof_of_l. pose (H3:= H x). destruct H3.
  case_eq (Nat.eq_dec (multiplicity x s) 0) ; intros e H3.
  - exact e.
  - pose (n':=e). apply proof_7_1_1 in n'. pose (H4:=H2 n'). destruct H2.
Qed.


Theorem proof_8_1 : forall x n s, multiplicity x (add x n s) = n + (multiplicity x s).
Proof.
intros x n s.
induction s.
+ simpl.
  case_eq(le_lt_dec n 0) ; intros l H1 ; simpl.
  - omega.
  - case_eq(T_eq_dec x x).
    * intros e H2. omega.
    * contradiction.
+ destruct a.
  case_eq (T_eq_dec x t) ; intros e H1.
  - rewrite e. simpl.
    case_eq (le_lt_dec n 0) ;intros l H2.
    * simpl. omega.
    * case_eq (T_eq_dec t t).
      ** intros e0 H3. simpl. rewrite H3. omega.
      ** contradiction.
  - simpl.
    case_eq (le_lt_dec n 0) ; intros l H2.
    * simpl. omega.
    * rewrite H1. simpl. rewrite H1. assumption.
Qed.

(** Nous n'avons pas réussi à démontrer cette preuve ... **)
Theorem proof_9_1 : forall x n y s, x <> y -> wf s ->multiplicity y (add x n s) = multiplicity y s.
Proof.
intros x n y s H H2. inversion H2. pose(H':=H0 x). destruct H'.
induction s.
+ simpl.
  case_eq (le_lt_dec n 0) ; intros l H4 ; simpl.
  - reflexivity.
  - case_eq(T_eq_dec y x).
    * intros e. pose(e':=e). symmetry in e'. contradiction.
    * intros n0 H5. reflexivity.
+ destruct a. simpl.
  case_eq(le_lt_dec n 0).
  - intros l H4. simpl. omega.
  - intros l H4.
    case_eq(T_eq_dec x t) ; intros e H5 ; simpl.
    * case_eq(T_eq_dec y t).
      ** intros e0. rewrite e0 in H. contradiction.
      ** intros n1 H6. reflexivity.
    * case_eq(T_eq_dec y t).
      ** reflexivity.
      ** intros n2 H6. apply IHs. apply wf_intro. intros x0.
         split. simpl in H1. rewrite H5 in H1. intros H7. inversion H7.
Admitted.

(** Nous n'avons pas réussi à démontrer cette preuve ... **)
Theorem proof_10_1 : forall s t x, wf s -> wf t ->(InMultiset x (union s t) <-> InMultiset x s \/ InMultiset x t).
Proof.
intros s t x H1 H2. pose(H':=union_wf s t H1 H2). unfold iff.
split.
+ intros H3. inversion H3. inversion H1. pose (H4:=H0 x). destruct H4.
Admitted.


(*****************)
(** Question 4. **)
(*****************)

Theorem proof_11_1 : forall x, multiplicity x (removeOne x (singleton x)) = 0.
Proof.
intros x. simpl.
case_eq(T_eq_dec x x ).
+ intros e H. simpl. reflexivity.
+ contradiction.
Qed.

Theorem proof_12_1 : forall x, multiplicity x (removeAll x (singleton x)) = 0.
Proof.
intros x. simpl.
case_eq(T_eq_dec x x ).
+ intros e H. simpl. reflexivity.
+ contradiction.
Qed.

Theorem proof_13_1 : forall x l n, multiplicity x l = n -> n > 1 -> multiplicity x (removeOne x l) = n-1.
Proof.
intros x l n H1 H2.
induction l.
+ simpl. simpl in H1. omega.
+ destruct a. simpl.
  case_eq(T_eq_dec x t) ;intros e H3.
  - case_eq(le_lt_dec n0 1) ; intros l0 H4.
    * rewrite e in H1. simpl in H1.
      case_eq (T_eq_dec t t).
      ** intros e0 H5. rewrite H5 in H1. omega.
      ** contradiction.
    *  simpl. rewrite H3. rewrite e in H1. simpl in H1.
      case_eq(T_eq_dec t t).
      ** intros e0 H5. rewrite H5 in H1. rewrite H1. reflexivity.
      ** contradiction.
  - simpl. rewrite H3. apply IHl. simpl in H1. rewrite H3 in H1. assumption.
Qed.

Theorem proof_14_1 : forall x l, wf l -> ~(InMultiset x (removeAll x l)).
Proof.
intros x l H1. unfold not. intros H2. inversion H2. inversion H1.
pose(H':=H0 x). destruct H'. pose(H5:=H3 H2). destruct H5.
Qed.

Theorem proof_15_1 : forall x l, multiplicity x l > 1 -> InMultiset x (removeOne x l).
Proof.
intros x l H1. apply inMultiset_intro.
induction l.
+ simpl in H1. omega.
+ destruct a. simpl.
  case_eq(T_eq_dec x t) ;intros e H3.
  - case_eq(le_lt_dec n 1) ; intros l0 H4.
    * rewrite e in H1. simpl in H1.
      case_eq (T_eq_dec t t).
      ** intros e0 H5. rewrite H5 in H1. omega.
      ** contradiction.
    * simpl. rewrite H3. reflexivity.
  - simpl. rewrite H3. apply IHl. simpl in H1. rewrite H3 in H1. assumption.
Qed.


(******************************************************************************)
(**************2.2 Implantation Fonctionnelle des multi-ensembles**************)
(******************************************************************************)
(****** PREUVES RÉUSSIES : 16 *************************************************)
(****** PREUVES ADMISES :   0 *************************************************)
(******************************************************************************)

(****************)
(** Question 1 **)
(****************)

Definition multiset_2 := T -> nat.
Print multiset_2.

(** empty_2 est le multiset vide. **)
Definition empty_2 : multiset_2 := (fun a:T => 0).
Check empty_2.
(** TEST
  Eval compute in empty_2.
**)


(** singleton_2 x crée le multi-ensemble qui ne contient que x en un seul exemplaire **)
Definition singleton_2 (x:T) : multiset_2 := fun a:T => 
  match T_eq_dec a x with
  | left _ => 1
  | right _ => 0
  end.
Check singleton_2.
(** TEST
  Eval compute in ((singleton_2 2) 3).
  Eval compute in ((singleton_2 2) 2).
**)


(** add_2 x n s ajoute, au multi-ensemble s, n occurrences de l’élément x dans s **)
Definition add_2 (x:T) (n:nat) (s:multiset_2) : multiset_2 := fun a:T => 
  match T_eq_dec a x with
  | left _ => s x + n
  | right _ => s a
  end.
Check add_2.
(** TEST
  Eval compute in ((add_2 3 4 (add_2 2 3 (singleton_2 1))) 3).
  Eval compute in ((add_2 3 4 (add_2 2 3 (singleton_2 1))) 3).
  Eval compute in ((add_2 3 4 (add_2 2 3 (singleton_2 1))) 5).
  Eval compute in ((add_2 3 4 (add_2 2 3 (empty_2))) 1).
**)


(** member_2 x s retourne la valeur true si x a au moins une occurrence dans s, 
    false sinon. **)
Definition member_2 (x:T) (s:multiset_2) : bool := 
  match Nat.eq_dec (s x) 0 with
  | left _ => false
  | right _ => true
  end.
Check member_2.
(** TESTS
  Eval compute in (member_2 2 (empty_2)).
  Eval compute in (member_2 2 (singleton_2 2)).
  Eval compute in (member_2 3 (singleton_2 2)).
  Eval compute in (member_2 3 (add_2 3 0 empty_2)).
  Eval compute in (member_2 3 (add_2 3 1 empty_2)).
**)


(** union_2 fait l’union de deux multi-ensembles. **)
Definition union_2 (s1:multiset_2) (s2:multiset_2) : multiset_2 := (fun a:T => s1 a + s2 a).
Check union_2.
(** TESTS
  Eval compute in ((union_2 (add_2 2 3 empty_2) (add_2 2 4 empty_2)) 2).
  Eval compute in ((union_2 (add_2 2 3 (add_2 4 5 empty_2)) (add_2 2 3 empty_2)) 4).
  Eval compute in ((union_2 (add_2 2 3 empty_2) empty_2) 2).
  Eval compute in ((union_2 empty_2 empty_2) 1).
**)


(** multiplicity_2 x s retourne le nombre d’occurrences de x dans s **)
Definition multiplicity_2 (x:T) (s:multiset_2) : nat := s x.
Check multiplicity_2.
(** TESTS
  Eval compute in (multiplicity_2 2 (add_2 2 7 empty_2)).
  Eval compute in (multiplicity_2 3 (add_2 2 7 empty_2)).
  Eval compute in (multiplicity_2 3 empty_2).
**)


(** removeOne_2 x s retourne le multi-ensemble s avec une occurrence de moins pour x.
    Si s ne contient pas  x, le multi-ensemble résultat est s. **)
Definition removeOne_2 (x:T) (s:multiset_2) : multiset_2 := fun a:T => 
  match T_eq_dec a x with
  | left _ => if member_2 x s then s x - 1 else 0
  | right _ => s a
  end.
Check removeOne_2.
(** TESTS
  Eval compute in ((removeOne_2 2 (add_2 2 7 empty_2)) 2).
  Eval compute in ((removeOne_2 2 (add_2 2 2 (add_2 3 5 empty_2))) 2).
  Eval compute in ((removeOne_2 2 (add_2 6 5 (add_2 2 2 (add_2 3 5 empty_2)))) 2).
  Eval compute in ((removeOne_2 2 (add_2 2 1 (add_2 3 5 empty_2))) 2).
  Eval compute in ((removeOne_2 2 (add_2 6 5 (add_2 2 1 (add_2 3 5 empty_2)))) 2).
  Eval compute in ((removeOne_2 3 (add_2 2 7 empty_2)) 3).
  Eval compute in ((removeOne_2 3 empty_2) 3).
**)


(** removeAll_2 x s retourne le mult-ensemble s o`u x n’apparait plus. 
    Si s ne contient pas x, le multiensemble r´esultat est s. **)
Definition removeAll_2 (x:T) (s:multiset_2) : multiset_2 := fun a:T => 
  match T_eq_dec a x with
  | left _ => 0
  | right _ => s a
  end.
Check removeAll_2.
(** TESTS
  Eval compute in ((removeAll_2 2 (add_2 2 7 empty_2)) 2).
  Eval compute in ((removeAll_2 2 (add_2 2 2 (add_2 3 5 empty_2))) 2).
  Eval compute in ((removeAll_2 2 (add_2 6 5 (add_2 2 2 (add_2 3 5 empty_2)))) 2).
  Eval compute in ((removeAll_2 2 (add_2 2 1 (add_2 3 5 empty_2))) 2).
  Eval compute in ((removeAll_2 2 (add_2 6 5 (add_2 2 1 (add_2 3 5 empty_2)))) 2).
  Eval compute in ((removeAll_2 3 (add_2 2 7 empty_2)) 2).
  Eval compute in ((removeAll_2 3 empty_2) 3).
**)

(****************)
(** Question 2 **)
(****************)

(** Ce prédicat spécifie qu’un élément appartient à un multi-ensemble dès lors 
    qu’il en existe une occurrence **)
Inductive InMultiset_2 (x:T) (l:multiset_2) : Prop := 
  | inMultiset_2_intro : member_2 x l = true -> InMultiset_2 x l.


(****************)
(** Question 3 **)
(****************)

Theorem proof_1_2 : forall (x : T), ~InMultiset_2 x empty_2.
Proof.
 intros x. unfold not. intros H. inversion H. discriminate H0.
Qed.

Theorem proof_2_2 : forall x y , InMultiset_2 y (singleton_2 x) <-> x = y.
Proof.
 intros x y. unfold iff.
 split.
 + intros H. inversion H. unfold member_2 in H0. unfold singleton_2 in H0.
   case_eq (T_eq_dec y x) ; intros H1 H2.
   - rewrite H1 in H0. destruct H0. symmetry. assumption.
   - rewrite H2 in H0. simpl in H0. discriminate H0.
 + intros H0. apply inMultiset_2_intro. unfold member_2. unfold singleton_2. rewrite H0.
   destruct (T_eq_dec y y).
   - destruct (Nat.eq_dec 1 0). discriminate e0. reflexivity.
   - destruct (Nat.eq_dec 0 0). contradiction. reflexivity.
Qed.

Theorem proof_3_2 :forall x, multiplicity_2 x (singleton_2 x) = 1.
Proof.
 intros x. unfold multiplicity_2. unfold singleton_2.
 case_eq (T_eq_dec x x).
 + reflexivity.
 + intros n H. contradiction.
Qed.

Theorem proof_4_2 : forall x s, member_2 x s = true <-> InMultiset_2 x s.
Proof.
intros x s. unfold iff.
split ; intros H.
+ apply inMultiset_2_intro. exact H.
+ inversion H. exact H0.
Qed.

Theorem proof_5_2 : forall x n s, n > 0 -> InMultiset_2 x (add_2 x n s).
Proof.
intros x n s H. apply inMultiset_2_intro. unfold member_2. unfold add_2.
case_eq (T_eq_dec x x) ; intros e H1.
+ case_eq (Nat.eq_dec (s x + n) 0). 
  - intros e0 H2. omega.
  - reflexivity.
+ contradiction e. reflexivity.
Qed.

Theorem proof_6_2 : forall x n y s, x <> y -> (InMultiset_2 y (add_2 x n s) <-> InMultiset_2 y s).
Proof.
 intros x n y s H. unfold iff.
 split ; intros H1 ; inversion H1.
 + apply inMultiset_2_intro.  unfold member_2. unfold member_2 in H0.
   case_eq (Nat.eq_dec (s y) 0).
   - intros e H3. unfold add_2 in H0.
     case_eq (T_eq_dec y x).
     * intros e0. pose(e0':=e0).  symmetry in e0'. contradiction.
     * intros n0 H4. rewrite H4 in H0. rewrite e in H0. simpl in H0. discriminate H0.
   - intros n0 H3. reflexivity.
 + unfold member_2 in H0. apply inMultiset_2_intro. unfold member_2. unfold add_2.
     case_eq (T_eq_dec y x ) ; intros e H2.
   - pose(e0':=e). symmetry in e0'. contradiction.
   - exact H0.
Qed.

Lemma proof_7_2_1: forall x s, s x <> 0 -> InMultiset_2 x s.
Proof.
intros x s H. apply inMultiset_2_intro. unfold member_2.
case_eq (Nat.eq_dec (s x) 0) ; intros e H1.
+ contradiction.
+ reflexivity.
Qed.

Theorem proof_7_2_2 : forall x s, multiplicity_2 x s = 0 <-> ~InMultiset_2 x s.
Proof.
 intros x s. unfold iff.
 split.
 + intros H. unfold multiplicity_2 in H. unfold not. intros H2. inversion H2. 
   unfold member_2 in H0. rewrite H in H0. simpl in H0. discriminate H0.
 + unfold not. intros H. unfold multiplicity_2.
   case_eq (Nat.eq_dec (s x) 0) ; intros e H1.
   - exact e.
   - pose (n':=e). apply proof_7_2_1 in n'. pose (H2:=H n'). destruct H2.
Qed.


Theorem proof_8_2 : forall x n s, multiplicity_2 x (add_2 x n s) = n + (multiplicity_2 x s).
Proof.
intros x n s. unfold multiplicity_2. unfold add_2.
destruct (T_eq_dec x x).
+ omega.
+ contradiction.
Qed.

Theorem proof_9_2 : forall x n y s, x <> y -> multiplicity_2 y (add_2 x n s) = multiplicity_2 y s.
Proof.
intros x n y s H. unfold multiplicity_2. unfold add_2.
destruct (T_eq_dec y x).
+ pose(e0':=e). symmetry in e0'. contradiction.
+ reflexivity.
Qed.

Theorem proof_10_2 : forall s t x, (InMultiset_2 x (union_2 s t) <-> InMultiset_2 x s \/ InMultiset_2 x t).
Proof.
 intros s t x. unfold iff.
 split.
 + intros H. inversion H. unfold member_2 in H0. unfold union_2 in H0.
   case_eq (Nat.eq_dec (s x) 0).
   - intros e H1. right. rewrite e in H0. simpl in H0.
     case_eq (Nat.eq_dec (t x) 0) ;intros e0 H2.
     * rewrite H2 in H0. discriminate H0.
     * apply inMultiset_2_intro. unfold member_2. rewrite H2. reflexivity.
   - case_eq (Nat.eq_dec (s x + t x) 0) ;intros e H1 ;rewrite H1 in H0.
     * discriminate H0.
     * intros n0 H2. left. apply inMultiset_2_intro. unfold member_2. rewrite H2. reflexivity.
 + intros H. destruct H ; inversion H ; unfold member_2 in H0 ; 
   apply inMultiset_2_intro ; unfold member_2 ; unfold union_2.
   - case_eq (Nat.eq_dec (s x) 0) ;intros n H1.
     * rewrite n in H0. simpl in H0.  discriminate H0.
     * case_eq (Nat.eq_dec (s x + t x) 0).
       ** intros e. omega. 
       ** intros n0 H2. reflexivity.
   - case_eq (Nat.eq_dec (t x) 0) ; intros n H1.
     * rewrite n in H0. simpl in H0. discriminate H0.
     * case_eq (Nat.eq_dec (s x + t x) 0). 
       ** intros e. omega.
       ** intros n0 H2. reflexivity.
Qed.

Theorem proof_11_2 : forall x, multiplicity_2 x (removeOne_2 x (singleton_2 x)) = 0.
Proof.
intros x. unfold multiplicity_2. unfold removeOne_2.
case_eq(T_eq_dec x x).
+ intros H. unfold member_2.
  case_eq(Nat.eq_dec (singleton_2 x x) 0) ; intros n H1.
  - reflexivity.
  - unfold singleton_2 in n. unfold singleton_2.
    case_eq(T_eq_dec x x).
    * intros e H2. omega.
    * contradiction.
+ contradiction.
Qed.

Theorem proof_12_2 : forall x, multiplicity_2 x (removeAll_2 x (singleton_2 x)) = 0.
Proof.
intros x. unfold multiplicity_2. unfold removeAll_2.
destruct (T_eq_dec x x).
+ reflexivity.
+ contradiction.
Qed.

Theorem proof_13_2 : forall x l n, multiplicity_2 x l = n -> n > 1 -> multiplicity_2 x (removeOne_2 x l) = n-1.
Proof.
intros x l n H1 H2. unfold multiplicity_2. unfold removeOne_2.
destruct (T_eq_dec x x).
+ unfold member_2.
  case_eq(Nat.eq_dec (l x) 0) ; intros e0 H3 ;unfold multiplicity_2 in H1.
  - rewrite e0 in H1. omega.
  - rewrite H1. reflexivity.
+ contradiction.
Qed.

Theorem proof_14_2 : forall x l, ~(InMultiset_2 x (removeAll_2 x l)).
Proof.
intros x l. unfold not. intros H. inversion H. unfold member_2 in H0.
case_eq(Nat.eq_dec (removeAll_2 x l x) 0) ; intros n H1.
+ rewrite H1 in H0. discriminate H0.
+ unfold removeAll_2 in n.
  case_eq(T_eq_dec x x).
  - intros e H2. pose(n':=n). rewrite H2 in n'. contradiction.
  - contradiction.
Qed.

Theorem proof_15_2 : forall x l, multiplicity_2 x l > 1 -> InMultiset_2 x (removeOne_2 x l).
Proof.
intros x l H. apply inMultiset_2_intro. unfold member_2. unfold removeOne_2.
case_eq(T_eq_dec x x).
+ intros e H1. unfold member_2.
  case(Nat.eq_dec (l x) 0) ; intros H2.
  - unfold multiplicity_2 in H. rewrite H2 in H. omega.
  - case_eq(Nat.eq_dec (l x - 1) 0) ; intros e0 H3.
    * unfold multiplicity_2 in H. omega.
    * reflexivity.
+ contradiction.
Qed.
