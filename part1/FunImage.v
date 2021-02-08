(** This section covers theorems about functions image*)

From Coq Require Import Reals ssreflect FunctionalExtensionality Setoid Image Decidable.
From Coquelicot Require Import Rbar.
From Coquelicot Require Import Rcomplements.
From Coquelicot Require Import Compactness Lim_seq Rcomplements Hierarchy Lub.
From mathcomp Require Import ssrnat.
Require Import SetTheory.



(** * Generic function images*)

Section Image.

(* Two functions that are equal have the same image*)
Theorem image_eq_fun {U: Set}{V: Set} : forall (X: Ensemble U) (f g: U -> V), (forall x, f(x) = g(x)) -> Im U V X f = Im U V X g.
  Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set.
  unfold Included.
  unfold In.
  split.
  intros.
  apply Im_inv in H0.
  destruct H0.
  unfold In in H0.
  apply (Im_intro U V X g x0).
  pose (H x0).
  unfold In.
  tauto.
  destruct H0.
  pose (H x0).
  rewrite <- e.
  auto.
  intros.
  apply Im_inv in H0.
  destruct H0.
  unfold In in H0.
  apply (Im_intro U V X f x0).
  pose (H x0).
  unfold In.
  tauto.
  destruct H0.
  pose (H x0).
  rewrite e.
  auto.
  Qed.
  
  (* A function has the same image with respect to two equal domains*)
  Theorem image_eq_set {U: Set}{V: Set}: forall (X X':Ensemble U) (f: U -> V) , (forall x: U, X x <-> X' x) -> Im U V X f = Im U V X' f.
  Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set.
  unfold Included.
  unfold In.
  split.
  intros.
  apply Im_inv in H0.
  destruct H0.
  apply (Im_intro U V X' f x0).
  destruct H0.
  pose (H x0).
  unfold In in H0.
  unfold In.
  tauto.
  apply eq_sym.
  tauto.
  intros.
  apply Im_inv in H0.
  destruct H0.
  apply (Im_intro U V X f x0).
  destruct H0.
  pose (H x0).
  unfold In in H0.
  unfold In.
  tauto.
  apply eq_sym.
  tauto.
  Qed.
  
  (* If the domain of the function is the empty set then the image of the function will be the empty set as well*)
  Theorem image_empty {U: Set}{V: Set} : forall X f, X = Empty_set U <-> Im U V X f = Empty_set V.
  split.
  intros.
  apply is_empty.
  setoid_rewrite <- is_empty in H.
  intros x p.
  apply Im_inv in p.
  destruct p.
  destruct H0.
  pose (H  x0 H0).
  case f0.
  intros.
  apply is_empty.
  setoid_rewrite <- is_empty in H.
  intros x p.
  pose (Im_intro U V X f x p (f x) (eq_refl (f x))).
  case (H (f x) i).
  Qed.
  
  (* If the domain of the function is non empty set then the image of the function will not be empty either*)
  Theorem image_non_empty {U: Set}{V: Set} : forall X f, X <> Empty_set U <-> Im U V X f <> Empty_set V.
  intros.
  split.
  intros p p2.
  setoid_rewrite <- image_empty in p2.
  tauto.
  intros p p2.
  apply (image_empty X f) in p2.
  tauto.
  Qed.
  
  (* If a set A is included in a set B then the image of f with respect to A will be included in the image of f with respect to B*)
  Theorem image_included {U: Set}{V: Set} : forall (X X': Ensemble U) (f: U -> V), Included U X X' -> Included V (Im U V X f) (Im U V X' f).
  unfold Included.
  intros.
  apply Im_inv in H0.
  destruct H0.
  destruct H0.
  pose (H x0 H0).
  apply (Im_intro _ _ _ _ x0).
  tauto.
  intuition.
  Qed.
  
  (* The image of f with respect to the union between A and B is the union of the image with respect to A and the image with respect to B*) 
  Theorem image_union {U: Set}{V: Set} : forall (X X': Ensemble U) (f: U -> V), Union V (Im U V X f) (Im U V X' f) = Im U V (Union U X X') f.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set.
  unfold Included.
  split.
  intros.
  unfold In in H.
  apply Union_inv in H.
  unfold In.
  destruct H.
  apply Im_inv in H.
  destruct H.
  apply (Im_intro U V _ f x0).
  destruct H.
  apply Union_introl.
  tauto.
  apply eq_sym.
  tauto.
  apply Im_inv in H.
  destruct H.
  apply (Im_intro U V _ f x0).
  destruct H.
  apply Union_intror.
  tauto.
  apply eq_sym.
  tauto.
  
  intros.
  apply Im_inv in H.
  destruct H.
  destruct H.
  apply Union_inv in H.
  destruct H.
  apply Union_introl.
  apply (Im_intro U V X f x0 H x (eq_sym H0)).
  apply Union_intror.
  apply (Im_intro U V X' f x0 H x (eq_sym H0)).
  Qed.
    
 End Image.
 
 (** * Images of functions from R to Rbar*)
 
 Section RbarImages.
  
  Corollary image_eq_fun_r_rbar : forall (X: Ensemble R) (f g: R -> Rbar), (forall x, f(x) = g(x)) -> Im R Rbar X f = Im R Rbar X g.
  Proof.
  intros X f g.
  apply (image_eq_fun X f g).
  Qed.


  (* The image of a function is the image of the flipped and shifted function with respect to the flipped and shifted domain*)
  Theorem image_f_t_shift_flip : forall f from to s, Im R Rbar (fun x0: R => x0 >= from /\ x0 <= to) f = Im _ _ (fun x1: R => x1 <= s -from /\ x1 >= s -to) (fun x2 : R => f (s - x2)).
  Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set.
  unfold Included.
  split.
  -intros.
  apply Im_inv in H.
  destruct H as [x4].
  destruct H.
  unfold In in H.
  apply (Im_intro R Rbar (fun x2: R => x2 <= s - from /\ x2 >= s -to) (fun x3 => f (s - x3)) (s - x4)).
  unfold In.
  split.
  destruct H.
  apply Rplus_le_compat_l.
  intuition.
  apply Rplus_ge_compat_l.
  intuition.
  unfold Rminus.
  rewrite (Ropp_plus_distr s (- x4)).
  rewrite Ropp_involutive.
  rewrite <- Rplus_assoc.
  rewrite Rplus_opp_r.
  rewrite Rplus_0_l.
  auto.
  -intros.
  apply Im_inv in H.
  destruct H as [x4].
  destruct H.
  unfold In in H.
  apply (Im_intro R Rbar (fun x2: R => x2 >= from /\ x2 <= to) (fun x3 => f (x3)) (s -x4)).
  unfold In.
  split.
  destruct H.
  apply (Rplus_ge_reg_l (-s) (s - x4) from).
  unfold Rminus.
  rewrite <- (Rplus_assoc).
  rewrite Rplus_opp_l.
  rewrite Rplus_0_l.
  apply Ropp_ge_cancel.
  rewrite Ropp_plus_distr.
  rewrite Ropp_involutive.
  rewrite Ropp_involutive.
  intuition.
  intuition.
  apply (Rplus_le_reg_l (-s)).
  unfold Rminus.
  rewrite <- (Rplus_assoc).
  rewrite Rplus_opp_l.
  rewrite Rplus_0_l.
  apply Ropp_le_cancel.
  rewrite Ropp_plus_distr.
  rewrite Ropp_involutive.
  rewrite Ropp_involutive.
  apply Rge_le.
  auto.
  auto.
  Qed.


  (* The image of a function is the image of the shifted function with respect to the shifted domain*)
Theorem image_f_t_shifted : forall f from to s, Im R Rbar (fun x0: R => x0 >= from /\ x0 <= to) f = Im _ _ (fun x2: R => x2 >= from + s /\ x2 <= to + s) (fun x3 : R => f (x3 - s)).
  Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set.
  unfold Included.
  split.
  -intros.
  apply Im_inv in H.
  destruct H as [x4].
  destruct H.
  unfold In in H.
  apply (Im_intro R Rbar (fun x2: R => x2 >= from + s /\ x2 <= to + s) (fun x3 => f (x3 - s)) (x4 + s)).
  unfold In.
  split.
  destruct H.
  intuition.
  intuition.
  unfold Rminus.
  rewrite (Rplus_assoc x4 s (-s)).
  rewrite (Rplus_opp_r s).
  rewrite Rplus_0_r.
  auto.
  -intros.
  apply Im_inv in H.
  destruct H as [x4].
  destruct H.
  unfold In in H.
  apply (Im_intro R Rbar (fun x2: R => x2 >= from /\ x2 <= to) (fun x3 => f (x3)) (x4 - s)).
  unfold In.
  split.
  destruct H.
  apply Rle_ge.
  apply (Rplus_le_reg_r s).
  apply Rge_le.
  rewrite (Rplus_assoc x4 (-s) s).
  rewrite (Rplus_opp_l s).
  rewrite Rplus_0_r.
  auto.
  apply (Rplus_le_reg_r s).
  rewrite (Rplus_assoc x4 (-s) s).
  rewrite (Rplus_opp_l s).
  rewrite Rplus_0_r.
  intuition.
  intuition.
  Qed.
  
  (* The image of a function is the image of the flipped function with respect to the flipped domain*)
  Corollary image_f_t_flipped : forall f from to, Im R Rbar (fun x0: R => x0 >= from /\ x0 <= to) f = Im _ _ (fun x2: R => x2 <= -from /\ x2 >= -to) (fun x3 : R => f (-x3)).
  Proof.
  intros.
  rewrite (image_eq_fun (fun x2 : R => x2 <= - from /\ x2 >= - to) (fun x3 : R => f (- x3)) (fun x => f(0 - x))). 
  rewrite (image_eq_set (fun x1 => x1 <= - from /\ x1 >= - to) (fun x1 => x1 <= 0 - from /\ x1 >= 0 - to) (fun x : R => f (0 - x))).
  apply (image_f_t_shift_flip f from to 0).
  intros.
  unfold Rminus.
  rewrite Rplus_0_l.
  rewrite Rplus_0_l.
  tauto.
  intros.
  unfold Rminus.
  rewrite Rplus_0_l.
  auto.
  Qed.
  
  
  Corollary image_t_f_is_f_t : forall f from to, Im R Rbar (fun x0: R => x0 >= from /\ x0 <= to) f = Im _ _ (fun x2: R => x2 <= to /\ x2 >= from) f.
  Proof.
  intros.
  assert (forall x0: R, (fun x => x >= from /\ x <= to) x0 <->  (fun x => x <= to /\ x >= from) x0).
  intros.
  tauto.
  rewrite (image_eq_set (fun x0 => x0 >= from /\ x0 <= to) (fun x0 => x0 <= to /\ x0 >= from) f H).
  intros.
  tauto.
  Qed.
  
  (*The image of f with respect to [a, a] is the image of f with respect to {a}*)
  Corollary image_f_f : forall f from, Im R Rbar (fun x0 : R => x0 >= from /\ x0 <= from) f =Im _ _ (fun x0: R => x0 = from) f.
  intros.
  assert (forall x0: R, (fun x => x >= from /\ x <= from) x0 <->  (fun x => x = from) x0).
  intros.
  split.
  intros.
  destruct H.
  apply Rge_le in H.
  apply Rle_le_eq.
  tauto.
  intros.
  pose (Rle_refl x0).
  rewrite <- H.
  tauto.
  rewrite (image_eq_set (fun x0 => x0 >= from /\ x0 <= from) (fun x0 => x0 = from) f H).
  tauto.
  Qed.
  
  (*The image of a singleton is also a singleton*)
  Theorem image_singleton : forall f x0, Im R Rbar (fun x => x = x0) f = Singleton Rbar (f x0).
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set.
  unfold Included.
  split.
  intros.
  apply Im_inv in H.
  destruct H.
  destruct H.
  unfold In in H.
  unfold In.
  apply Singleton_intro.
  rewrite <- H.
  tauto.
  intros.
  unfold In in H.
  apply Singleton_inv in H.
  apply (Im_intro R Rbar _ f (x0)).
  unfold In.
  tauto.
  intuition.
  Qed.
  
  (*The image of f with respect to ]a, a] is the empty set*)
  Lemma image_lt_le: forall f from, Im R Rbar (fun x => x > from /\ x <= from) f = Empty_set Rbar.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set.
  unfold Included.
  split.
  intros.
  apply Im_inv in H.
  destruct H.
  destruct H.
  unfold In in H. 
  destruct H.
  apply Rle_not_gt in H1.
  tauto.
  intros.
  unfold In in H.
  case H.
  Qed.
  
  (*The image of f with respect to [a, a[ is the empty set*)
  Lemma image_le_lt: forall f from, Im R Rbar (fun x => x >= from /\ x < from) f = Empty_set Rbar.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set.
  unfold Included.
  split.
  intros.
  apply Im_inv in H.
  destruct H.
  destruct H.
  unfold In in H. 
  destruct H.
  apply Rlt_not_ge in H1.
  tauto.
  intros.
  unfold In in H.
  case H.
  Qed.
  
  (*The image of f with respect to ]a, a[ is the empty set*)
  Lemma image_lt_lt: forall f from, Im R Rbar (fun x => x > from /\ x < from) f = Empty_set Rbar.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set.
  unfold Included.
  split.
  intros.
  apply Im_inv in H.
  destruct H.
  destruct H.
  unfold In in H. 
  destruct H.
  apply Rgt_ge in H.
  apply Rlt_not_ge in H1.
  tauto.
  intros.
  unfold In in H.
  case H.
  Qed.
  
  (* If a <= b, then the image of f with respect to [a, b] is not empty*)
  Corollary image_f_t_non_empty : forall f from to, from <= to -> Im R Rbar (fun x => x >= from /\ x <= to) f <> Empty_set Rbar.
  intros.
  apply image_non_empty.
  intro p.
  setoid_rewrite <- is_empty in p.
  assert (forall x, ~x >= from \/ ~x <= to).
  intros.
  apply not_and.
  unfold decidable.
  tauto.
  apply (p x).
  assert (forall x : R, x < from \/ x > to).
  intros.
  pose (H0 x).
  case o.
  intros.
  apply Rnot_ge_lt in H1.
  tauto.
  intros.
  apply Rnot_le_gt in H1.
  tauto.
  pose (H1 from).
  case o.
  intros.
  apply Rlt_not_eq in H2.
  tauto.
  intros.
  apply Rgt_not_le in H2.
  tauto.
  Qed.
  
  (* The image of [a, infinity[ is not empty*)
  Corollary image_f_non_empty : forall f from, Im R Rbar (fun x => x >= from) f <> Empty_set Rbar.
  intros.
  apply image_non_empty.
  apply (non_empty).
  exists (from + 1).
  apply Rle_ge.
  rewrite <- (Rplus_0_r) at 1.
  apply (Rplus_le_compat_l (from) _ _).
  apply Rle_0_1.
  Qed.
  
  (*The image of the opposite of f is the opposite of the image of f*)
  Theorem image_opp : forall X f, set_opp_Rbar (Im R Rbar X f) = Im R Rbar X (fun x => Rbar_opp (f x)).
  Admitted.
  
  (* The image of f with respect to [a, b[, is the union of the images of f with respect to [a, e] and [e, b] for any e between a and b*)
  Theorem image_f_t_union: forall f from to eps,  from <= eps <= to -> Im R Rbar (fun x0: R => x0 >= from /\ x0 <= to) f = Union Rbar (Im R Rbar (fun x0: R => x0 >= from /\ x0 <= eps) f) (Im R Rbar (fun x0: R => x0 >= eps /\ x0 <= to) f).
  intros.
  rewrite image_union.
  apply image_eq_set.
  intros.
  split.
  intros.
  case (Rle_dec x eps).
  intros.
  apply Union_introl.
  unfold In.
  tauto.
  intros.
  apply Union_intror.
  apply Rnot_le_gt in n.
  apply Rgt_ge in n.
  unfold In.
  tauto.
  intros.
  apply Union_inv in H0.
  unfold In in H0.
  destruct H.
  case H0.
  intros.
  destruct H2.
  pose (Rle_trans _ _ _ H3 H1).
  tauto.
  intros.
  destruct H2.
  apply Rle_ge in H.
  pose (Rge_trans _ _ _ H2 H).
  tauto.
  Qed.
  


End RbarImages.
  

  
  
  
  
 
  
    
  
  
  
  
  