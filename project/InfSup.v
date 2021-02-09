(** This section gather theorems about infima and suprema of subset of R and Rbar*)

From Coq Require Import ssrbool ssreflect Reals Image Decidable.
From Coquelicot Require Import Rbar.
From Coquelicot Require Import Compactness Lim_seq Rcomplements Hierarchy Lub.
From mathcomp Require Import ssrnat.
Require Import FunImage SetTheory.
Require Import RbarComp.


(*inf S is the infimum of S*)
Theorem is_inf_inf: forall A, Rbar_is_glb A (Rbar_glb A).
intros.
unfold Rbar_glb.
by case: Rbar_ex_glb.
Qed.

(*sup S is the supremum of S*)
Theorem is_sup_sup: forall A, Rbar_is_lub A (Rbar_lub A).
intros.
unfold Rbar_lub.
by case: Rbar_ex_lub.
Qed.

(** * Finite infimum and supremum of real sets*)

Section Reals.

  (** ** Definitions*)
  
  Definition ex_sup (S: Ensemble R) := exists l, is_lub S l.
  
   (* Definition of a finite lower bound of a real set*)
  Definition is_lower_bound (E:R -> Prop) (m:R) := forall x:R, E x -> x >= m.
  
  (* Condition of the infimum*)
  Definition is_glb (E:R -> Prop) (m:R) :=
    is_lower_bound E m /\ (forall b:R, is_lower_bound E b -> m >= b).
    
  Definition ex_inf (S: Ensemble R) := exists l, is_glb S l.
  
  Definition sup_ex (S: Ensemble R) := { m : R | is_lub S m}.

    (* If s is a supremum of S then there exists a supremum for S*)
    Theorem is_sup_ex (S: Ensemble R) (s: R) :
    is_lub S s -> sup_ex S.
    intros.
    exists s.
    tauto.
    Qed.

    Definition sup (S: Ensemble R)  (ex: sup_ex S) := proj1_sig(ex).

    Axiom ex_sup_cond : forall S, R_bounded S -> S <> Empty_set R -> sup_ex S.

    (*The supremum is unique*)
    Theorem sup_unique (S: Ensemble R) (p: sup_ex S) (s: R) :
    is_lub S s -> sup S p = s.
    Proof.
    intros.
    pose p as l.
    unfold sup_ex in p.
    destruct p.
    unfold is_lub in i, H.
    destruct i, H.
    pose (r s H).
    pose (H0 x i).
    pose (Rle_antisym s x r1 r0).
    rewrite e.
    unfold set_maximum.
    simpl.
    auto.
    Qed.

    (*The supremum of the set is a supremum of the set*)
    Theorem sup_is_sup (S: Ensemble R) (ex: sup_ex S) :
    is_lub S (sup S ex).
    unfold set_maximum.
    induction ex.
    simpl.
    tauto.
    Qed.


  (** ** Relations between supremum and infimum*)

  (*The infimum of a set is equal to the opposite of the supremum of the opposite set*)
  Theorem is_lub_opp: forall E l,
  is_glb E l <-> is_lub (set_opp E) (- l).
  unfold is_glb.
  unfold is_lower_bound.
  unfold is_lub.
  unfold is_upper_bound.
  unfold set_opp.
  split.
  intros.
  destruct H.
  split.
  intros.
  pose (H (-x) H1).
  apply Rge_le.
  apply Ropp_ge_cancel.
  rewrite Ropp_involutive.
  tauto.
  intros.
  pose (H0 (-b)).
  assert ((forall x : R, E x -> x >= - b)).
  intros.
  pose (H1 (-x)).
  setoid_rewrite Ropp_involutive in r0.
  apply r0 in H2.
  apply Rle_ge.
  apply Ropp_le_cancel.
  rewrite Ropp_involutive.
  tauto.
  apply r in H2.
  apply Rge_le.
  apply Ropp_ge_cancel.
  rewrite Ropp_involutive.
  tauto.
  intros.
  destruct H.
  split.
  intros.
  pose (H (-x)).
  setoid_rewrite Ropp_involutive in r.
  apply Ropp_le_cancel in r.
  apply Rle_ge.
  tauto.
  tauto.
  intros.
  assert (forall x : R, E (- x) -> x <= -b).
  intros.
  pose (H1 (-x) H2).
  apply Rge_le.
  apply Ropp_ge_cancel.
  rewrite Ropp_involutive.
  tauto.
  pose (H0 (-b) H2).
  apply Ropp_le_cancel in r.
  apply Rle_ge.
  tauto.
  Qed.
  
  (*The supremum of a set is equal to the opposite of the infimum of the opposite set*)
  Theorem is_glb_opp: forall E l,
  is_lub E l <-> is_glb (set_opp E) (- l).
  intros.
  pose (is_lub_opp (set_opp E) (-l)).
  setoid_rewrite Ropp_involutive in i.
  rewrite set_opp_involutive in i.
  tauto.
  Qed.
  
  (*If a set has a supremum then the opposite set has a infimum*)
  Theorem ex_inf_opp : forall S, ex_sup S <-> ex_inf (set_opp S).
  unfold ex_sup.
  unfold ex_inf.
  split.
  intros.
  destruct H.
  exists (-x).
  apply is_glb_opp.
  tauto.
  intros.
  destruct H.
  exists (-x).
  apply is_glb_opp.
  rewrite Ropp_involutive.
  tauto.
  Qed.
  
  (*If a set has a supremum then the opposite set has a supremum*)
  Theorem ex_sup_opp : forall S, ex_inf S <-> ex_sup (set_opp S).
  unfold ex_sup.
  unfold ex_inf.
  split.
  intros.
  destruct H.
  exists (-x).
  apply is_lub_opp.
  tauto.
  intros.
  destruct H.
  exists (-x).
  apply is_lub_opp.
  rewrite Ropp_involutive.
  tauto.
  Qed.
 
   (*If a set has a supremum then it is not empty *)
  Theorem sup_non_empty : forall S l, is_lub S l -> exists s, S s.
  intros.
  apply not_not.
  unfold Decidable.decidable.
  tauto.
  unfold not at 1.
  intros.
  pose (not_ex_all_not R S H0).
  unfold is_lub in H.
  unfold is_upper_bound in H.
  destruct H.
  assert (forall b x : R, S x -> x <= b).
  intros.
  pose (n x).
  tauto.
  assert (forall b: R, l <= b).
  intros.
  apply (H1 b (H2 b)).
  pose (H3 (l - 1)).
  apply (Rplus_le_compat_l (- l)) in r.
  rewrite Rplus_opp_l in r.
  unfold Rminus in r.
  rewrite <- Rplus_assoc in r.
  rewrite Rplus_opp_l in r.
  rewrite Rplus_0_l in r.
  apply (Rplus_le_compat_l 1) in r.
  rewrite Rplus_0_r in r.
  rewrite Rplus_opp_r in r.
  apply Rle_not_lt in r.
  pose (r Rlt_0_1).
  case f.
  Qed.
  
    (*If a  set has an infimum then it is not empty*)
  Theorem inf_non_empty: forall S l, is_glb S l -> exists s, S s.
  intros.
  apply is_lub_opp in H.
  apply sup_non_empty in H.
  apply non_empty.
  apply non_empty in H.
  apply set_opp_non_empty.
  tauto.
  Qed.
    
End Reals.

(** * Non finite infimum and supremum of a real set*)

Section RToRbar.

  (** ** Relation between infimum and supremum*)


(*The supremum of a set is equal to the opposite of the infimum of the opposite set*)
Theorem Lub_Rbar_opp : forall S, Glb_Rbar S = Rbar_opp (Lub_Rbar (set_opp S)).
intros.
apply is_glb_Rbar_unique.
apply (is_lub_Rbar_opp S _).
rewrite Rbar_opp_involutive.
apply Lub_Rbar_correct.
Qed.


(*The infimum of a set is equal to the opposite of the supremum of the opposite set*)
Theorem Glb_Rbar_opp : forall S, Lub_Rbar S = Rbar_opp (Glb_Rbar (set_opp S)).
intros.
apply is_lub_Rbar_unique.
apply (is_glb_Rbar_opp S _).
rewrite Rbar_opp_involutive.
apply Glb_Rbar_correct.
Qed.


  (** ** Supremum*)
  
  (* If the set has a supremum then it is finite*)
Theorem sup_is_finite : forall S, ex_sup S <-> is_finite (Lub_Rbar S).
  unfold ex_sup.
  intros.
  split.
  intros.
  unfold ex_sup in H.
  destruct H.
  pose (sup_non_empty S x H) as k.
  unfold is_lub in H.
  unfold is_upper_bound in H.
  destruct H.
  apply not_not.
  unfold decidable.
  tauto.
  intros p.
  apply (Rbar_not_finite (Lub_Rbar S)) in p.
  case p.
  intros.
  assert (~is_lub_Rbar S p_infty).
  intro p2.
  unfold is_lub_Rbar in p2.
  unfold is_ub_Rbar in p2.
  destruct p2.
  pose (H1 x r).
  simpl in r1.
  case r1.
  rewrite <- H in H0.
  pose (H0 (Lub_Rbar_correct S)).
  case f.
  intros.
  assert (~is_lub_Rbar S m_infty).
  intro p2.
  unfold is_lub_Rbar in p2.
  unfold is_ub_Rbar in p2.
  destruct p2.
  destruct k.
  pose (H0 x0 H2).
  simpl in r1.
  case r1.
  rewrite <- H in H0.
  pose (H0 (Lub_Rbar_correct S)).
  case f.
  intros.
  pose (Lub_Rbar_correct S).
  unfold is_finite in H.
  exists (Lub_Rbar S).
  rewrite <- H in i.
  unfold is_lub_Rbar in i.
  unfold is_ub_Rbar in i.
  destruct i.
  unfold is_lub.
  unfold is_upper_bound.
  split.
  tauto.
  intros b.
  pose (H1 b).
  simpl in r.
  tauto.
  Qed.
  
    (*If the supremum of a set exists then it is equal to the non finite one*)
  Theorem is_sup_R_R : forall S l, is_lub S l -> is_lub_Rbar S l.
  intros.
  pose (sup_non_empty S l H).
  unfold is_lub in H.
  unfold is_upper_bound in H.
  destruct H.
  unfold is_lub_Rbar.
  unfold is_ub_Rbar.
  split.
  tauto.
  intros.
  pose (Rbar_dec b).
  case o.
  intros.
  rewrite H0.
  simpl.
  exact I.
  intros.
  case H0.
  intros.
  destruct e.
  pose (H x H2).
  setoid_rewrite H1 in r1.
  simpl in r1.
  case r1.
  intros.
  unfold is_finite in H1.
  rewrite <- H1 in H.
  pose (r0 b H).
  rewrite <- H1.
  tauto.
  Qed.
  
  (** ** Infimum*)

  (*If a set has an infimum then it is finite*)
  Theorem inf_is_finite : forall S, ex_inf S <-> is_finite (Glb_Rbar S).
  intros.
  rewrite Lub_Rbar_opp.
  setoid_rewrite ex_sup_opp.
  split.
  intros.
  apply (sup_is_finite (set_opp S)) in H.
  unfold is_finite in H.
  rewrite <- H.
  unfold is_finite.
  tauto.
  intros.
  unfold is_finite in H.
  rewrite Rbar_opp_real in H.
  setoid_rewrite <- Rbar_opp_eq in H.
  rewrite Rbar_opp_involutive in H.
  simpl in H.
  rewrite Ropp_involutive in H.
  fold (is_finite (Lub_Rbar (set_opp S))) in H.
  apply sup_is_finite.
  tauto.
  Qed.
  
   (*If the supremum of a set exists then it is equal to the non finite one*)  
  Theorem is_inf_R_R : forall S l, is_glb S l -> is_glb_Rbar S l.
  intros.
  apply is_lub_opp in H.
  apply is_sup_R_R in H.
  pose (is_lub_Rbar_opp S l).
  simpl in i.
  apply i in H.
  tauto.
  Qed.


End RToRbar.


(** * Infimum and supremum in Rbar*)

Section RbarToRbar.

(** ** Relation between infimum and supremum*)

(*The supremum of a set is equal to the opposite of the infimum of the opposite set*)

Theorem Rbar_is_lub_opp: forall S l, Rbar_is_lub S l <-> Rbar_is_glb (set_opp_Rbar S) (Rbar_opp l).
intros.
unfold Rbar_is_lub.
unfold Rbar_is_upper_bound.
unfold Rbar_is_glb.
unfold Rbar_is_lower_bound.
unfold set_opp_Rbar.
split.
intros.
destruct H.
split.
intros.
pose (H (Rbar_opp x) H1).
apply Rbar_opp_le.
rewrite Rbar_opp_involutive.
tauto.
intros.
pose (H0 (Rbar_opp b)).
assert ((forall x : Rbar, S x -> Rbar_le x (Rbar_opp b))).
intros.
pose(H1 (Rbar_opp x)).
setoid_rewrite Rbar_opp_involutive in r0.
pose (r0 H2).
apply Rbar_opp_le.
rewrite Rbar_opp_involutive.
tauto.
pose (r H2).
apply Rbar_opp_le.
rewrite Rbar_opp_involutive.
tauto.
intros.
destruct H.
split.
intros.
pose (H (Rbar_opp x)).
setoid_rewrite Rbar_opp_involutive in r.
apply Rbar_opp_le.
apply (r H1).
intros.
pose (H0 (Rbar_opp b)).
assert ((forall x : Rbar, S (Rbar_opp x) -> Rbar_le (Rbar_opp b) x)).
intros.
pose(H1 (Rbar_opp x)).
pose (r0 H2).
apply Rbar_opp_le.
rewrite Rbar_opp_involutive.
tauto.
pose (r H2).
apply Rbar_opp_le.
tauto.
Qed.

(*The infimum of a set is equal to the opposite of the supremum of the opposite set*)
Theorem Rbar_is_glb_opp: forall E l,
  Rbar_is_glb E l <-> Rbar_is_lub (set_opp_Rbar E) (Rbar_opp l).
  intros.
  pose (Rbar_is_lub_opp (set_opp_Rbar E) (Rbar_opp l)).
  setoid_rewrite Rbar_opp_involutive in i.
  rewrite set_opp_Rbar_involutive in i.
  tauto.
  Qed.
  
(*The supremum of a set is equal to the opposite of the infimum of the opposite set*)
Theorem Rbar_lub_opp : forall S, Rbar_lub S = Rbar_opp (Rbar_glb (set_opp_Rbar S)).
intros.
pose (Rbar_opp_glb_lub S).
rewrite  e.
rewrite Rbar_opp_involutive.
tauto.
Qed.

(*The infimum of a set is equal to the opposite of the supremum of the opposite set*)
Theorem Rbar_glb_opp : forall S, Rbar_glb S = Rbar_opp (Rbar_lub (set_opp_Rbar S)).
intros.
pose (Rbar_opp_lub_glb S).
rewrite  e.
rewrite Rbar_opp_involutive.
tauto.
Qed.

(** ** Supremum*)

(* The supremum remains the same when a subset of R is converted in a subset of Rbar *)
Theorem is_sup_R_Rbar : forall S l, is_lub S l <-> Rbar_is_lub (set_R_to_Rbar S) l.
  intros.
  split.
  intros.
  pose (sup_non_empty S l H).
  unfold is_lub in H.
  unfold is_upper_bound in H.
  destruct H.
  unfold Rbar_is_lub.
  unfold Rbar_is_upper_bound.
  split.
  intros.
  unfold set_R_to_Rbar in H.
  destruct H.
  unfold is_finite in H.
  rewrite <- H.
  simpl.
  apply (r x H0).
  intros.
  case (Rbar_dec b).
  intros.
  rewrite H0.
  simpl.
  tauto.
  intros.
  case H0.
  intros.
  unfold set_R_to_Rbar in H.
  destruct e.
  pose (H x).
  assert(Rbar_le x b).
  apply r1.
  unfold is_finite.
  tauto.
  rewrite H1 in H3.
  simpl in H3.
  case H3.
  intros.
  unfold is_finite in H1.
  rewrite <- H1.
  simpl.
  assert(forall x : R, S x -> x <= b).
  intros.
  pose (H x).
  unfold set_R_to_Rbar in r1.
  rewrite <- H1 in r1.
  simpl in r1.
  apply r1.
  unfold is_finite.
  tauto.
  apply (r0 b H2).
  intros.
  unfold is_lub.
  unfold is_upper_bound.
  unfold Rbar_is_lub in H.
  unfold Rbar_is_upper_bound in H.
  destruct H.
  split.
  intros.
  pose (H x).
  unfold set_R_to_Rbar in r.
  simpl in r.
  apply r.
  unfold is_finite.
  tauto.
  intros.
  pose (H0 b).
  simpl in r.
  apply r.
  intros.
  unfold set_R_to_Rbar in H2.
  destruct H2.
  unfold is_finite in H2.
  rewrite <- H2.
  simpl.
  apply (H1 x H3).
  Qed.

(* The supremum remains the same when a subset of R is converted in a subset of Rbar *)
Corollary sup_R_Rbar: forall (S: Ensemble R) (l: R), is_lub S l <-> Rbar_lub (set_R_to_Rbar S) = l.
  intros S l.
  split.
  intros.
  apply is_sup_R_Rbar in H.
  apply Rbar_is_lub_unique.
  tauto.
  intros.
  setoid_rewrite is_sup_R_Rbar.
  rewrite <- H.
  apply (is_sup_sup).
  Qed.
  
  (* The supremum remains the same when a subset of R is converted in a subset of Rbar *)
  Theorem is_sup_Rbar_Rbar: forall S l, is_lub_Rbar S l <-> Rbar_is_lub (set_R_to_Rbar S) l.
  intros.
  unfold is_lub_Rbar.
  unfold Rbar_is_lub.
  unfold Rbar_is_upper_bound.
  unfold is_ub_Rbar.
  unfold set_R_to_Rbar.
  split.
  intros.
  destruct H.
  split.
  intros.
  destruct H1.
  unfold is_finite in H1.
  pose (H x H2).
  rewrite <- H1.
  tauto.
  intros.
  pose (H0 b).
  assert (forall x : R, S x -> Rbar_le x b).
  intros.
  assert (is_finite x).
  unfold is_finite.
  tauto.
  apply (H1 x (conj H3 H2)).
  apply r in H2.
  tauto.
  split.
  destruct H.
  intros.
  assert(is_finite x).
  unfold is_finite.
  tauto.
  apply (H x (conj H2 H1)).
  intros.
  destruct H.
  pose (H1 b).
  assert ((forall x : Rbar, is_finite x /\ S x -> Rbar_le x b)).
  intros.
  destruct H2.
  pose (H0 x H3).
  unfold is_finite in H2.
  setoid_rewrite H2 in r0.
  tauto.
  apply (r H2).
  Qed.
  
  (* The supremum remains the same when a subset of R is converted in a subset of Rbar *)
  Theorem sup_Rbar_Rbar: forall S, Lub_Rbar S = Rbar_lub (set_R_to_Rbar S).
  intros.
  apply is_lub_Rbar_unique.
  apply is_sup_Rbar_Rbar.
  apply is_sup_sup.
  Qed.

    (* The supremum of a set is smaller than the supremum of the union of this set with an other one *)
    Lemma sup_le_union_l : forall A B: Ensemble Rbar, Rbar_le (Rbar_lub A) (Rbar_lub (Union Rbar A B)) .
  Proof.
  intros.
  apply Rbar_lub_subset.
  intros.
  apply Union_introl .
  exact H.
  Qed.
  
      (* The supremum of a set is smaller than the supremum of the union of this set with an other one *)
  Lemma sup_le_union_r : forall A B: Ensemble Rbar, Rbar_le (Rbar_lub B) (Rbar_lub (Union Rbar A B)) .
  Proof.
  intros.
  apply Rbar_lub_subset.
  intros.
  apply Union_intror.
  exact H.
  Qed.
  
  (* The supremum of a singleton is its unique element*)
  Lemma sup_singleton : forall x: Rbar, Rbar_is_lub (Singleton Rbar x) x.
  Proof.
  intros.
  unfold Rbar_is_lub.
  unfold Rbar_is_upper_bound.
  split.
  intros.
  apply Singleton_inv in H.
  rewrite H.
  apply Rbar_le_refl.
  intros.
  apply H.
  apply In_singleton.
  Qed.
  
  (* The supremum of the intersection of two sets is smaller than the minimum between the two suprema*) 
  Lemma sup_le_inter: forall A B: Ensemble Rbar, Rbar_le (Rbar_lub (Intersection Rbar A B)) (Rbar_min (Rbar_lub A) (Rbar_lub B)).
  intros A B.
  pose (Rbar_is_lub_subset (Intersection Rbar A B) A).
  pose (Rbar_is_lub_subset (Intersection Rbar A B)  B).
  assert(forall l0 l1 l2, Rbar_is_lub A l0 -> Rbar_is_lub B l1 -> Rbar_is_lub (Intersection Rbar A B) l2 -> Rbar_le l2 (Rbar_min l0 l1)).
  intros.
  pose (r l2 l0).
  pose (r0 l2 l1).
  pose (Intersection_inv Rbar A B).
  assert (forall x : Rbar, Intersection Rbar A B x -> A x).
  intros.
  pose (a x H2).
  tauto.
  assert (forall x : Rbar, Intersection Rbar A B x -> B x).
  intros.
  pose (a x H3).
  tauto.
  pose (r1 H2 H1 H).
  pose (r2 H3 H1 H0).
  apply (Rbar_min_case l0 l1 (fun t => Rbar_le l2 t) r3 r4).
  apply (H (Rbar_lub A) (Rbar_lub B) (Rbar_lub (Intersection Rbar A B)) (is_sup_sup _) (is_sup_sup _) (is_sup_sup _)).
  Qed.
  
  (*If the set has a maximum and all the elements of the set are greater than a given a then the supremum will also be greater than a*)
  Theorem ge_is_sup : forall (a l: Rbar) (S : Ensemble Rbar), (forall x, S x -> Rbar_le x a) /\ Rbar_is_lub S l -> Rbar_le (Rbar_lub S) a.
  intros.
  destruct H.
  pose (Rbar_is_lub_unique S l H0).
  unfold Rbar_is_lub in H0.
  unfold Rbar_is_upper_bound in H0.
  destruct H0.
  pose (r0 a H).
  rewrite e.
  tauto.
  Qed.
  
    (*If the set has a maximum and all the elements of the set are smaller than a given a then the supremum will also be smaller than a*)
  Corollary ge_sup : forall (a: Rbar) (S: Ensemble Rbar), ((forall x, S x -> Rbar_le x a) <-> Rbar_le (Rbar_lub S) a).
  intros a S.
  split.
  intros.
  pose (ge_is_sup a (Rbar_lub S) S).
  pose (conj H (is_sup_sup S)).
  tauto.
  intros.
  pose (is_sup_sup S).
  unfold Rbar_is_lub in r.
  unfold Rbar_is_upper_bound in r.
  destruct r.
  pose (H1 x H0).
  apply (Rbar_le_trans x (Rbar_lub S) a r H).
  Qed.
  
    (*If an element of the set is greater than a given a the supremum is also greater than a*)
  Theorem le_sup : forall (a: Rbar) (S: Ensemble Rbar), (exists x, S x /\ Rbar_le a x) -> Rbar_le a (Rbar_lub S).
  intros a S H.
  assert (forall l, Rbar_is_lub S l -> Rbar_le a l).
  intros.
  unfold Rbar_is_lub in H0.
  unfold Rbar_is_upper_bound in H0.
  destruct H0.
  destruct H.
  destruct H.
  pose (H0 x H).
  apply (Rbar_le_trans a x l H2 r).
  pose (H0 (Rbar_lub S) (is_sup_sup S)).
  tauto.
  Qed.
  
  (*If the supremum is greater and smaller than a value then it is equal to that value*)
  Theorem sup_eq : forall (S: Ensemble Rbar) (l : Rbar), (forall x, S x -> Rbar_le x l) /\ (exists s, S s /\ s = l)  -> Rbar_lub S = l.
  intros S l H.
  destruct H.
  pose (le_sup l S).
  pose (ge_sup l S).
  destruct i.
  apply H1 in H.
  destruct H0.
  destruct H0.
  pose (Rbar_le_refl l).
  rewrite <- H3 in r0 at 2.
  pose (conj H0 r0).
  pose (ex_intro (fun x => S x /\ Rbar_le l x) x a).
  apply r in e.
  apply Rbar_le_antisym.
  tauto.
  tauto.
  Qed.
  
  (*If a given a is stricly smaller than the supremum of the set then there exist an element of the set that is greater than a*)
  Theorem lt_sup : forall (a: Rbar) (S: Ensemble Rbar), Rbar_lt a (Rbar_lub S) -> (exists x, S x /\ Rbar_le a x).
  intros.
  pose (ge_sup a S).
  destruct i.
  setoid_rewrite <- contrapositive in H0.
  apply not_all_ex_not in H0.
  destruct H0.
  apply not_imp in H0.
  exists x.
  intuition.
  pose (Rbar_not_le_lt _ _ H3).
  apply (Rbar_lt_le) in r.
  tauto.
  unfold decidable.
  tauto.
  apply Rbar_lt_not_le in H.
  tauto.
  unfold decidable.
  tauto.
  Qed.
  
  (*If a function is greater than another then its supremum will also be greater than the supremum of the other function*)
  Theorem sup_le_sup_image: forall (X: Ensemble R) (f g: R -> Rbar), (forall x: R, In R X x -> Rbar_le (f x) (g x)) -> Rbar_le (Rbar_lub (Im R Rbar X f)) (Rbar_lub (Im R Rbar X g)).
  intros.
  assert (forall l0 l1, Rbar_is_lub (Im R Rbar X f) l0 -> Rbar_is_lub (Im R Rbar X g) l1 -> Rbar_le l0 l1).
  unfold Rbar_is_lub.
  unfold Rbar_is_upper_bound.
  intros.
  destruct H0.
  destruct H1.
  assert(forall h a, (forall y, Im R Rbar X h y -> Rbar_le y a) <-> (forall x, In R X x -> forall y : Rbar, y = h x -> Rbar_le y a)).
  split.
  intros.
  pose (Im_intro R Rbar X h x H5 y H6).
  pose (H4 y i).
  tauto.
  intros.
  pose (Im_inv R Rbar X h y H5).
  destruct e.
  destruct H6.
  pose (H4 x H6 y (eq_sym H7)).
  tauto.
  Admitted.
 
  (*The supremum of a function plus a constant is the supremum of the function plus a constant*)
  Theorem sup_independence: forall (a: Rbar) (X: Ensemble R) (f: R -> Rbar), Rbar_plus a (Rbar_lub (Im R Rbar X f)) = Rbar_lub (Im R Rbar X (fun x => Rbar_plus (f x) a)). 
  Admitted.
  
  (* the supremum of ]-infinity, l[ is l*)
  Theorem sup_R_set_lt (l : R) : is_lub (fun t => t < l) l.
  unfold is_lub.
  unfold is_upper_bound.
  split.
  intros.
  apply Rlt_le.
  tauto.
  intros.
  apply le_epsilon.
  intros.
  pose (H (l - eps)).
  apply Ropp_lt_contravar in H0.
  rewrite Ropp_0 in H0.
  apply (Rplus_lt_compat_l l) in H0.
  rewrite Rplus_0_r in H0.
  apply r in H0.
  apply (Rplus_le_compat_r eps) in H0.
  unfold Rminus in H0.
  rewrite Rplus_assoc in H0.
  rewrite Rplus_opp_l in H0.
  rewrite Rplus_0_r in H0.
  tauto.
  Qed.
  
  (*if b < l then the supremum of ]b, l[ is l*)
  Theorem sup_R_set_ge_lt (l b : R) : b < l -> is_lub (fun t => b <= t < l) l.
  Admitted.

(** ** Infimunm *)

(* The infimum remains the same when a subset of R is converted in a subset of Rbar *)
  Theorem is_inf_R_Rbar : forall S l, is_glb S l <-> Rbar_is_glb (set_R_to_Rbar S) l.
  intros.
  setoid_rewrite is_lub_opp.
  setoid_rewrite is_sup_R_Rbar.
  setoid_rewrite Rbar_is_lub_opp.
  rewrite set_opp_R_Rbar.
  rewrite set_opp_involutive.
  simpl.
  rewrite Ropp_involutive.
  tauto.
  Qed.
  
  (* The infimum remains the same when a subset of R is converted in a subset of Rbar *)
  Corollary inf_R_Rbar: forall (S: Ensemble R) (l: R), (is_glb S l <-> Rbar_glb (set_R_to_Rbar S) = l).
  intros.
  setoid_rewrite is_lub_opp.
  setoid_rewrite sup_R_Rbar.
  setoid_rewrite <- set_opp_R_Rbar.
  setoid_rewrite Rbar_opp_lub_glb.
  setoid_rewrite <- Rbar_opp_eq at 2.
  tauto.
  Qed.
  
    (* The infimum remains the same when a subset of R is converted in a subset of Rbar *)
  Theorem is_inf_Rbar_Rbar: forall S l, is_glb_Rbar S l <-> Rbar_is_glb (set_R_to_Rbar S) l.
  intros.
  setoid_rewrite is_lub_Rbar_opp.
  setoid_rewrite is_sup_Rbar_Rbar.
  setoid_rewrite <- set_opp_R_Rbar.
  setoid_rewrite <- Rbar_lub_glb.
  setoid_rewrite set_opp_R_Rbar.
  tauto.
  Qed.

    (* The infimum remains the same when a subset of R is converted in a subset of Rbar *)
  Theorem inf_Rbar_Rbar: forall S, Glb_Rbar S = Rbar_glb (set_R_to_Rbar S).
  intros.
  apply is_glb_Rbar_unique.
  apply is_inf_Rbar_Rbar.
  apply is_inf_inf.
  Qed.

  (* The supremum of a set is smaller than the supremum of the union of this set with an other one *)
  Lemma inf_le_union_l : forall A B: Ensemble Rbar, Rbar_le (Rbar_glb (Union Rbar A B)) (Rbar_glb A).
  Proof.
  intros.
  apply Rbar_glb_subset.
  intros.
  apply Union_introl .
  exact H.
  Qed.
  
  (* The supremum of a set is smaller than the supremum of the union of this set with an other one *)
  Lemma inf_le_union_r : forall A B: Ensemble Rbar, Rbar_le (Rbar_glb (Union Rbar A B)) (Rbar_glb B).
  Proof.
  intros.
  apply Rbar_glb_subset.
  intros.
  apply Union_intror.
  exact H.
  Qed.
  
  (* The supremum of a set is smaller than the supremum of the union of this set with an other one *)
  Lemma is_inf_union : forall (A B: Ensemble Rbar) (l0 l1: Rbar), Rbar_is_glb A l0 /\ Rbar_is_glb B l1 -> Rbar_is_glb (Union Rbar A B) (Rbar_min l0 l1).
  Proof.
  unfold Rbar_is_glb.
  unfold Rbar_is_lower_bound.
  intros.
  destruct H.
  destruct H.
  destruct H0.
  split.
  intros.
  apply Union_inv in H3.
  case H3.
  intros.
  pose (H x H4).
  pose (Rbar_min_l l0 l1).
  pose (Rbar_le_trans (Rbar_min l0 l1) l0 x).
  tauto.
  intros.
  pose (H0 x H4).
  pose (Rbar_min_r l0 l1).
  pose (Rbar_le_trans (Rbar_min l0 l1) l1 x).
  tauto.
  intros.
  pose (H1 b); pose (H2 b).
  pose (Union_introl Rbar A B); pose (Union_intror Rbar A B).
  unfold In in i; unfold In in i0.
  assert (forall x : Rbar, A x -> Rbar_le b x).
  intros.
  pose (i x H4).
  pose (H3 x u).
  tauto.
  assert (forall x : Rbar, B x -> Rbar_le b x).
  intros.
  pose (i0 x H5).
  pose (H3 x u).
  tauto.
  assert (Rbar_le b l0 /\ Rbar_le b l1).
  tauto.
  destruct H6.
  apply (Rbar_min_case l0 l1 (fun x => Rbar_le b x) H6 H7).
  Qed. 
  
  (* The supremum of a set is smaller than the supremum of the union of this set with an other one *)
  Corollary inf_union : forall A B: Ensemble Rbar, Rbar_glb (Union Rbar A B) = (Rbar_min (Rbar_glb A)(Rbar_glb B)).
  Proof.
  intros.
  apply Rbar_is_glb_unique.
  apply is_inf_union.
  split.
  apply (is_inf_inf A).
  apply (is_inf_inf B).
  Qed.
    
    (* The supremum of a singleton is its unique element*)
  Lemma is_inf_singleton : forall x: Rbar, Rbar_is_glb (Singleton Rbar x) x.
  Proof.
  intros.
  unfold Rbar_is_glb.
  unfold Rbar_is_lower_bound.
  split.
  intros.
  apply Singleton_inv in H.
  rewrite H.
  apply Rbar_le_refl.
  intros.
  apply H.
  apply In_singleton.
  Qed.
  
    (* The supremum of a singleton is its unique element*)
  Corollary inf_singleton : forall x: Rbar, Rbar_glb (Singleton Rbar x) = x.
  Proof.
  intros.
  pose (is_inf_singleton x).
  apply Rbar_is_glb_unique.
  tauto.
  Qed.
  
      (*If the set has a minimum and all the elements of the set are greater than a given a then the infimum will also be greater than a*)
  Theorem le_is_inf : forall (a l: Rbar) (S : Ensemble Rbar), (forall x, S x -> Rbar_le a x) /\ Rbar_is_glb S l -> Rbar_le a (Rbar_glb S).
  intros.
  destruct H.
  pose (Rbar_is_glb_unique S l H0).
  unfold Rbar_is_glb in H0.
  unfold Rbar_is_lower_bound in H0.
  destruct H0.
  pose (r0 a H).
  rewrite e.
  tauto.
  Qed.
  
(*If the set has a minimum and all the elements of the set are greater than a given a then the infimum will also be greater than a*)

  Corollary le_inf : forall (a: Rbar) (S: Ensemble Rbar), ((forall x, S x -> Rbar_le a x) <-> Rbar_le a (Rbar_glb S)).
  split.
  intros.
  pose (le_is_inf a (Rbar_glb S) S).
  pose (conj H (is_inf_inf S)).
  tauto.
  intros.
  pose (is_inf_inf).
  unfold Rbar_is_glb in r.
  unfold Rbar_is_lower_bound in r.
  pose (r S).
  destruct a0.
  pose (H1 x H0).
  apply (Rbar_le_trans a (Rbar_glb S) x H r0).
  Qed.
  
     (*If an element of the set is smaller than a given a the infimum is also smaller than a*)
  Theorem ge_inf : forall (a: Rbar) (S: Ensemble Rbar), (exists x, S x /\ Rbar_le x a) -> Rbar_le (Rbar_glb S) a.
  intros.
  assert (forall l, Rbar_is_glb S l -> Rbar_le l a).
  intros.
  unfold Rbar_is_glb in H0.
  unfold Rbar_is_lower_bound in H0.
destruct H0.
  destruct H.
  destruct H.
  pose (H0 x H).
  apply (Rbar_le_trans l x a r H2).
  pose (H0 (Rbar_glb S) (is_inf_inf S)).
  tauto.
  Qed.
  
  (*If a given a is stricly smaller than the supremum of the set then there exist an element of the set that is greater than a*)
  Theorem gt_inf : forall (a: Rbar) (S: Ensemble Rbar), Rbar_lt (Rbar_glb S) a -> (exists x, S x /\ Rbar_le x a).
  intros.
  pose (le_inf a S).
  destruct i.
  setoid_rewrite <- contrapositive in H0.
  apply not_all_ex_not in H0.
  destruct H0.
  apply not_imp in H0.
  exists x.
  intuition.
  pose (Rbar_not_le_lt _ _ H3).
  apply (Rbar_lt_le) in r.
  tauto.
  unfold decidable.
  tauto.
  apply Rbar_lt_not_le in H.
  tauto.
  unfold decidable.
  tauto.
  Qed.
  
  (* if a is strictly smaller than the infimum of a set then it is not in the set*)
  Theorem lt_inf : forall (a: Rbar) (S: Ensemble Rbar), Rbar_lt a (Rbar_glb S) -> ~ S a.
  intros a S H.
  unfold not.
  intros.
  pose (is_inf_inf S).
  unfold Rbar_is_glb in r.
  unfold Rbar_is_lower_bound in r.
  destruct r.
  pose (H1 a H0).
  pose (Rbar_lt_le_trans _ _ _ H r).
  apply Rbar_lt_not_eq in r0.
  intuition.
  Qed.
  
  (*The infimum of a function plus a constant is the supremum of the function plus a constant*)
  Theorem inf_independence: forall  (X: Ensemble R) (f: R -> Rbar) (a: R), Rbar_plus a (Rbar_glb (Im R Rbar X f)) = Rbar_glb (Im R Rbar X (fun x => Rbar_plus (f x) a)). 
  Admitted.
  
 (*If the infimum is greater and smaller than a value then it is equal to that value*)
 Theorem inf_eq : forall (S: Ensemble Rbar) (l : Rbar), (forall x, S x -> Rbar_le l x) /\ (exists s, S s /\ s = l)  -> Rbar_glb S = l.
  intros S l H.
  destruct H.
  pose (le_inf l S).
  pose (ge_inf l S).
  destruct i.
  apply H1 in H.
  destruct H0.
  destruct H0.
  pose (Rbar_le_refl l).
  rewrite <- H3 in r0 at 1.
  pose (conj H0 r0).
  pose (ex_intro (fun x => S x /\ Rbar_le x l) x a).
  apply r in e.
  apply Rbar_le_antisym.
  tauto.
  tauto.
  Qed. 
  
End RbarToRbar.
  