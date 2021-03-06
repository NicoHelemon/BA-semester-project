(** This section introduces the basic definitions and theorems of network calculus.
It introduces:
- Arrival curves
- Minimal service curve
- Backlog
-Delay

*)

From Coq Require Import Reals ssreflect FunctionalExtensionality Setoid Image Bool Decidable.
From Coq Require List Datatypes.
From Coquelicot Require Import Rbar.
From Coquelicot Require Import Rcomplements.
From Coquelicot Require Import Compactness Lim_seq Rcomplements Hierarchy Lub.
From mathcomp Require Import ssrnat.
Require Import FunImage.
Require Import InfSup.
Require Import RbarComp.
Require Import Definitions SetTheory.

Section NCDefinitions.

Generalizable Variables a al s b d beta da l c lmax n A.

(** * Arrival curves*)

(* Definition of arrival curve*)
Definition is_arrival_curve (a: R -> Rbar) `(alpha: NonDecreasingPositive al) := 
forall x, Cumulative a -> x >= 0 -> Rbar_le (a(x)) (conv al a x).

(* Definition of arrival curve for continuous functions*)
Definition is_arrival_curve_2 (a: R -> Rbar) `(alpha: NonDecreasingPositive al) :=
Cumulative a -> forall s t, s >= 0 -> t >= 0 -> s <= t -> Rbar_le (Rbar_minus (a t) (a s)) (al(t - s)).

(* Those definitions are equivalent if the function is continuous*)
Theorem arr_cur_eq `(alpha: NonDecreasingPositive al) : forall a, is_finite_f a -> (is_arrival_curve a alpha <-> is_arrival_curve_2 a alpha).
intros a p.
unfold is_arrival_curve, is_arrival_curve_2.
unfold is_finite_f in p.
split.
intros.
unfold conv in H.
pose (H t H0 H2).
setoid_rewrite <- le_inf in r.
pose (r (Rbar_plus (al (t - s)) (a s))).
assert (Im R Rbar (fun x : R => x >= 0 /\ x <= t)
     (fun s : R => Rbar_plus (al (t - s)) (a s))
     (Rbar_plus (al (t - s)) (a s))).
pose (Im_def R Rbar (fun x : R => x >= 0 /\ x <= t) (fun s0 : R => Rbar_plus (al (t - s0)) (a s0)) s).
simpl in i.
apply i.
unfold In.
tauto.
apply r0 in H4.
unfold is_finite in p.
pose (p t H2).
rewrite <- e.
pose (p s H1).
rewrite <- e0.
case (Rbar_dec (al(t-s))).
intros.
rewrite H5.
simpl.
exact I.
intros.
case H5.
intros.
destruct alpha.
destruct positive.
apply (Rplus_le_compat_r (-s)) in H3.
rewrite Rplus_opp_r in H3.
apply Rle_ge in H3.
pose (pos_to_pos (t - s) H3).
assert (Rbar_lt m_infty 0).
simpl.
exact I.
pose (Rbar_lt_le_trans _ _ _ H7 r1).
apply Rbar_lt_not_eq in r2.
apply eq_sym in H6.
case (r2 H6).
intros.
unfold is_finite in H6.
rewrite <- H6.
simpl.
rewrite <- H6 in H4.
rewrite <- e in H4.
rewrite <- e0 in H4.
simpl in H4.
apply (Rplus_le_compat_r (-(a s))) in H4.
rewrite Rplus_assoc in H4.
rewrite Rplus_opp_r in H4.
rewrite Rplus_0_r in H4.
tauto.
intros.
unfold conv.
setoid_rewrite <- le_inf.
intros.
apply Im_inv in H2.
destruct H2.
destruct H2.
unfold In in H2.
destruct H2.
pose (H H0 x1 x H2 H1 H4).
rewrite <- H3.
pose (p x H1).
pose (p x1 H2).
unfold is_finite in i.
unfold is_finite in i0.
rewrite <- i.
rewrite <- i0.
case (Rbar_dec (al(x - x1))).
intros.
rewrite H5.
simpl.
exact I.
intros.
case H5.
intros.
destruct alpha.
destruct positive.
pose H4.
apply (Rplus_le_compat_r (- x1)) in  r0.
rewrite Rplus_opp_r in r0.
apply Rle_ge in r0.
pose (pos_to_pos (x - x1) r0).
assert (Rbar_lt m_infty 0).
simpl.
exact I.
pose (Rbar_lt_le_trans _ _ _ H7 r1).
apply Rbar_lt_not_eq in r2.
apply eq_sym in H6.
case (r2 H6).
intros.
unfold is_finite in H6.
rewrite <- H6.
simpl.
rewrite <- H6 in r.
rewrite <- i in r.
rewrite <- i0 in r.
simpl in r.
apply (Rplus_le_compat_r (a x1)) in r.
rewrite Rplus_assoc in r.
rewrite Rplus_opp_l in r.
rewrite Rplus_0_r in r.
tauto.
Qed.

(* If the arrival curve is a cumulative function then a is equal to the arrival curve of a convolution with a*)
Theorem arr_cur_eq_start_0 `(A: Cumulative a)`(alpha: NonDecreasingPositive al) : al 0 = 0 -> (is_arrival_curve a alpha <-> forall x, x >= 0 -> a(x) = conv al a x).
Admitted.

(*The subadditive closure of a an arrival curve is also an arrival curve*)
Theorem subadd_clos_is_arr_curve `(A: Cumulative a) `(alpha: NonDecreasingPositive al) : is_arrival_curve a alpha -> is_arrival_curve a (SubaddClos alpha).
Admitted.

(** * Minimal service curve*)

(* Definition of a minimal service curve*)
Definition is_minimal_service `(S: Server s) `(Beta: NonDecreasingPositive beta) := forall a d t, s a d -> t >= 0 -> Rbar_le (conv a beta t) (d t).

(* Definition of a minimal service curve for continuous functions*)
Definition is_minimal_service_2 `(S: Server s) `(Beta: NonDecreasingPositive beta) := forall a d t, s a d -> t >= 0 -> (exists s, s >= 0 /\ s <= t /\ Rbar_le (Rbar_plus (a (t - s)) (beta s)) (d t)).

(* Those two definitions are equivalent if the function is continuous*)
Theorem min_ser_eq `(S: Server s) `(Beta: NonDecreasingPositive beta) : continuous beta -> (is_minimal_service S Beta <-> is_minimal_service_2 S Beta).
unfold is_minimal_service, is_minimal_service_2.
intros p.
split.
2:{
intros.
pose (H a d t H0 H1).
unfold conv.
destruct e.
destruct H2.
destruct H3.
pose (Im_def R Rbar (fun x => x >= 0 /\ x <= t) (fun s => Rbar_plus (a (t -s)) (beta s)) x (conj H2 H3)).
simpl in i.
apply ge_inf.
exists (Rbar_plus (a (t - x)) (beta x)).
split.
tauto.
tauto.
}Admitted.


(* the zero function is always a minimal service curve*)
Theorem is_minimal_service_0 `(S: Server) : is_minimal_service S (zero_f_non_decr).
unfold is_minimal_service.
intros.
destruct S.
destruct (subset_c_c a d H).
destruct H1.
rewrite (conv_zero_f non_decr_pos t H0).
rewrite start_0.
destruct H2.
destruct non_decr_pos0.
destruct positive.
apply (pos_to_pos t H0).
Qed.




Generalizable Variables p ndp.

(* The composition of the relu function and a minimal service curve is also a minimal service curve*)
Theorem minimal_service_plus `(S: Server s) `(P: non_decreasing p) : (forall a d t, s a d -> t >= 0 -> Rbar_le (conv a p t) (d t)) -> is_minimal_service S (NonDecrFPlus P).
Admitted.
(*intros.
pose (non_decr_split p 0 P).
unfold is_minimal_service.
intros.
case o.
2:{
intros.
case H3.
2:{
intros.
case H4.
intros.
destruct H5.
case (Rlt_dec t x).
intros.
unfold conv.
pose (image_f_t_union).
Admitted.*)



(** * Backlog*)

(* Backlog between a and d at time t*)
Definition backlog_t (a d: R -> Rbar)(t: R) := Rbar_minus (a t) (d t).

(* Greatest backlog among all the times*)
Definition backlog (a d: R -> Rbar) := Rbar_lub(Im R Rbar (fun x => x >= 0) (backlog_t a d)).

(*The backlog is greater than 0*)
Definition is_backlogged (a d: R -> Rbar)(t: R) := t >= 0 -> Rbar_lt 0 (backlog_t a d t).

(* The backlog between the input and the ouput of a system is always smaller than the backlog between the arrival curve of the input and the service curve of the system*)
Theorem backlog_bound `(S: Server s) `(alpha: NonDecreasingPositive al) `(Beta: NonDecreasingPositive beta):
forall a d, is_finite_f a -> s a d -> (is_arrival_curve a alpha) -> (is_minimal_service S Beta) -> Rbar_le (backlog a d) (backlog al beta).
intros a d p H H0 H1.
unfold backlog.
unfold is_finite_f in p.
apply ge_sup.
intros.
apply Im_inv in H2.
destruct H2.
destruct H2.
unfold In in H2.
unfold backlog_t in H3.
unfold is_minimal_service in H1.
pose (H1 a d x0 H H2).
apply Rbar_opp_le in r.
apply (Rbar_plus_le_l _ _(a x0)) in r.
unfold backlog.
unfold backlog_t.
unfold conv in r.
rewrite Rbar_glb_opp in r.
rewrite Rbar_opp_involutive in r.
rewrite image_opp in r.
rewrite (sup_independence) in r.
pose (arr_cur_eq alpha a).
setoid_rewrite arr_cur_eq in H0.
unfold Rbar_minus in H3.
rewrite H3 in r.
unfold is_arrival_curve_2 in H0.
destruct S.
destruct (subset_c_c a d H).
remember (fun x : R => x >= 0 /\ x <= x0) as X.
assert(forall x1 : R, (In R X x1) -> Rbar_le (Rbar_plus (Rbar_opp (Rbar_plus (a (x0 - x1)) (beta x1))) (a x0))  (Rbar_minus (al x1) (beta x1))).
intros.
unfold In in H6.
rewrite HeqX in H6.
destruct H6.
apply (Rplus_le_compat_r (- x1)) in H7.
rewrite Rplus_opp_r in H7.
apply Rle_ge in H7.
apply Ropp_ge_contravar in H6.
apply (Rplus_ge_compat_l (x0)) in H6.
fold (Rminus x0 0) in H6. 
rewrite Rminus_0_r in H6.
apply Rge_le in H6.
pose (H0 H4 (x0 -x1) x0 H7 H2 H6).
unfold Rminus in r0.
setoid_rewrite Ropp_plus_distr in r0.
rewrite Ropp_involutive in r0.
rewrite <- Rplus_assoc in r0.
rewrite Rplus_opp_r in r0.
rewrite Rplus_0_l in r0.
rewrite Rbar_plus_comm.
unfold Rbar_minus.
rewrite <- Rbar_plus_opp.
assert ((Rbar_plus (a x0) (Rbar_plus (Rbar_opp (a (x0 - x1))) (Rbar_opp (beta x1)))) = 
(Rbar_plus (Rbar_plus (a x0) (Rbar_opp (a (x0 - x1)))) (Rbar_opp (beta x1)))).
rewrite <- Rbar_assoc_x_y_f.
tauto.
pose (p x0 H2).
tauto.
pose (p (x0 - x1) H7).
unfold is_finite in i0.
rewrite <- i0.
simpl.
rewrite <- Rbar_opp_real.
unfold is_finite.
tauto.
rewrite H8.
fold (Rbar_minus (a x0) (a (x0 - x1))).
apply (Rbar_plus_le_r).
apply r0.
pose (sup_le_sup_image X _ _ H6).
pose (Rbar_le_trans _ _ _ r r0).
assert (Included R X (fun t => t >= 0)).
unfold Included.
intros.
unfold In.
rewrite HeqX in H7.
unfold In in H7.
tauto.
apply (image_included _ _ (fun t : R => Rbar_minus (al t) (beta t))) in H7.
pose (Rbar_lub_subset _ _ H7).
unfold In in r2.
setoid_rewrite (set_eq (Im R Rbar X (fun t : R => Rbar_minus (al t) (beta t)))) in r2.
setoid_rewrite (set_eq) in r2.
apply (Rbar_le_trans _ _ _ r1 r2).
tauto.
Qed.

(* begin of a backlogged period *)
Definition ex_begin_backlogged_period (a d: R -> Rbar)(t: R) := exists l, 0 <= l <= t /\ forall s, l < s <= t -> is_backlogged a d s.

(* end of a backlogged period *)
Definition ex_end_backlogged_period (a d: R -> Rbar)(t: R) := exists h, t <= h /\ forall s, t <= s < h -> is_backlogged a d s.


(** ** Delay*)

(* Delay between a and d at time t*)
Definition delay_t (a d: R -> Rbar) (t:  R): Rbar := Glb_Rbar(fun delta: R => Rbar_le (a t) (d(t + delta))).

(* Greatest delay among all the times*)
Definition delay (a d: R -> Rbar): Rbar := Rbar_lub(Im R Rbar (fun x => x >= 0) (delay_t a d)).

(* if the delay between at time t is greater than a given tao, then a(t) is greater than d(t + tao)*)
Theorem lt_delay_t : forall (a d: R -> Rbar) (t tao: R), Rbar_lt tao (delay_t a d t) -> Rbar_lt (d (t + tao) ) (a t).
intros.
unfold delay_t in H.
rewrite inf_Rbar_Rbar in H.
apply (lt_inf tao _) in H.
unfold set_R_to_Rbar in H.
apply not_and in H.
apply Rbar_not_le_lt.
case H.
intros.
unfold is_finite in H0.
intuition.
tauto.
unfold decidable.
tauto.
Qed.


(* The delay between a and d is the delay between the arrival curve f a and the service curve of the server*)
Theorem delay_bound `(S: Server s) `(alpha: NonDecreasingPositive al) `(Beta: NonDecreasingPositive beta):
forall a d, s a d -> is_finite_f a -> (is_arrival_curve a alpha) -> (is_minimal_service S Beta) -> Rbar_le (delay a d) (delay al beta).
intros a d H p H0 H1.
unfold is_finite_f in p.
assert (forall (t tao :R), t >= 0 -> tao >= 0 -> Rbar_lt tao (delay_t a d t) -> Rbar_le tao (delay al beta)).
intros.
apply lt_delay_t in H4.
unfold is_arrival_curve in H0.
pose (Rplus_ge_compat t 0 tao 0 H2 H3).
setoid_rewrite Rplus_0_l in r.
unfold is_minimal_service in H1.
pose (H1 a d (t + tao) H r).
destruct S.
destruct (subset_c_c a d H).
pose (Rbar_le_lt_trans _ _ _ r0 H4) as r2.
unfold conv in r2.
apply gt_inf in r2.
destruct r2.
destruct H7.
apply Im_inv in H7.
destruct H7.
unfold In in H7.
destruct H7.
rewrite <- H9 in H8.
assert ( Rbar_le (beta x0) (Rbar_minus (a t) (a (t + tao - x0)))).
admit.
assert(t + tao - x0 <= t /\ t + tao - x0 >= 0 ).
split.
destruct Beta.
destruct positive.
destruct H7.
pose (pos_to_pos x0 H7).
pose (Rbar_le_trans _ _ _ r1 H10).


admit.
admit.
pose (H0 t H5 H2).
unfold conv in r1.
setoid_rewrite <- le_inf in r1.
pose (r1 (Rbar_plus (al (x0 - tao)) (a (t + tao - x0)))).
assert (Rbar_le (a t) (Rbar_plus (al (x0 - tao)) (a (t + tao - x0)))).
apply r2.
pose (Im_def R Rbar (fun x : R => x >= 0 /\ x <= t) (fun s : R => Rbar_plus (al (t - s)) (a s)) (t + tao - x0)).
simpl in i.
unfold Rminus in i.
setoid_rewrite Ropp_plus_distr in i.
setoid_rewrite Ropp_involutive in i.
setoid_rewrite Ropp_plus_distr in i.
setoid_rewrite <- Rplus_assoc in i.
setoid_rewrite <- Rplus_assoc in i.
setoid_rewrite Rplus_opp_r in i.
setoid_rewrite Rplus_0_l in i.
setoid_rewrite (Rplus_comm (-tao) (x0)) in i.
fold (Rminus x0 (tao)) in i.
apply i.
unfold In.
apply (and_comm) in H11.
apply H11.
assert(Rbar_le (Rbar_minus (a (t)) (a (t + tao - x0)))  (al (x0 - tao))).
destruct H11.
Check Rbar_plus_le_r.
apply (Rbar_plus_le_r _ _ (Rbar_opp (a (t + tao - x0)))) in H12.
rewrite (Rbar_assoc_y_z_f) in H12.
fold (Rbar_minus (a (t + tao - x0)) ((a (t + tao - x0)))) in H12.
rewrite Rbar_minus_eq_0 in H12.
rewrite Rbar_plus_0_r in H12.
tauto.
pose (p (t + tao - x0) H13).
tauto.
pose (p (t + tao - x0) H13).
unfold is_finite in i.
rewrite <- i.
simpl.
rewrite <- Rbar_opp_real.
unfold is_finite.
tauto.
pose (Rbar_le_trans _ _ _ H10 H13).

assert (Rbar_le tao (delay_t al beta (x0 - tao))).
unfold delay_t.
rewrite inf_Rbar_Rbar.
apply le_inf.
intros.
unfold set_R_to_Rbar in H14.
destruct H14.
admit.

unfold delay.
apply le_sup.
exists (delay_t al beta (x0 - tao)).
split.
apply Im_def.
unfold In.
destruct H11.
apply (Rplus_le_compat_l (-t)) in H11.
unfold Rminus in H11.
rewrite Rplus_assoc in H11.
rewrite <- Rplus_assoc in H11.
rewrite Rplus_opp_l in H11.
rewrite Rplus_0_l in H11.
apply Ropp_le_contravar in H11.
rewrite Ropp_minus_distr in H11.
rewrite Ropp_0 in H11.
apply Rle_ge.
tauto.

tauto.
unfold delay.
apply ge_sup.
intros.
apply Im_inv in H3.
destruct H3.
destruct H3.
pose (sup_R_set_ge_lt (delay_t a d x0) 0).
assert(0 < delay_t a d x0).
admit.
apply i in H5.
apply is_sup_R_Rbar in H5.
Admitted.

(** * Relation between arrival and service curves*)

(*the arrival curve of the input of a server  is always greater than a service curve of a server in 0*)
Theorem arrival_service_0 `(alpha: NonDecreasingPositive al) `(S: Server s)`(Beta: NonDecreasingPositive beta) : forall a d , s a d /\ is_arrival_curve a alpha /\ is_minimal_service S Beta -> Rbar_le (beta 0) (al 0).
intros.
destruct H.
unfold is_arrival_curve in H0.
unfold is_minimal_service in H0.
destruct H0.
pose (H1 a d 0 H (Rge_refl 0)).
destruct S.
pose (subset_c_c a d H).
destruct a0.
pose (H0 0 H2 (Rge_refl 0)).
pose (causality a d 0 H).
pose (Rbar_le_trans _ _ _ (r1 (Rle_refl 0)) r0).
pose (Rbar_le_trans _ _ _ r r2).
unfold conv in r3.
setoid_rewrite (image_f_f ) in r3. 
rewrite (image_singleton _ 0) in r3.
rewrite (image_singleton _ 0) in r3.
rewrite inf_singleton in r3.
rewrite inf_singleton in r3.
rewrite Rminus_0_r in r3.
destruct H2.
rewrite start_0 in r3.
rewrite Rbar_plus_0_l in r3.
rewrite Rbar_plus_0_r in r3.
tauto.
Qed.

(* The deconvolution between the arrival curve of an input and a service curve of a server is always non decreasing and positive*)
Global Instance DeconvAlphaBeta `(S: Server s) `(alpha: NonDecreasingPositive al) `(Beta: NonDecreasingPositive beta): forall a d, s a d /\ is_arrival_curve a alpha /\ is_minimal_service S Beta
-> NonDecreasingPositive(deconv al beta).
intros.
assert (non_decreasing (deconv al beta)).
apply deconv_non_decr.
tauto.
split.
2:{tauto.
}
apply non_decr_eq in H0.
unfold non_decreasing_2 in H0.
split.
intros.
pose (H0 0 x (conj (Rle_refl 0) H1) (Rge_le x 0 H1)).
pose (Rbar_le_refl (al 0)).
pose (arrival_service_0 alpha S  Beta a d H).
apply Rbar_opp_le in r1.
pose (Rbar_plus_le_compat (al 0) (al 0) (Rbar_opp (al 0)) (Rbar_opp (beta 0)) r0 r1).
fold (Rbar_minus (al 0) (al 0)) in r2.
fold (Rbar_minus (al 0) (beta 0)) in r2.
setoid_rewrite (Rbar_minus_eq_0 (al 0)) in r2.
apply (Rbar_le_trans 0  (deconv al beta 0) (deconv al beta x)).
assert (Rbar_le (Rbar_minus (al 0) (beta 0)) (deconv al beta 0)).
unfold deconv.
apply le_sup. 
exists (Rbar_minus (al 0) (beta 0)).
split.
apply (Im_intro R Rbar _ _ 0).
unfold In.
apply Rle_refl.
rewrite Rplus_0_l.
tauto.
apply Rbar_le_refl.
apply (Rbar_le_trans _ _ _ r2 H2).
tauto.
Qed.


Theorem server_arrival_curve `(S: Server s) `(alpha: NonDecreasingPositive al) `(Beta: NonDecreasingPositive beta) :
forall a d (proof: s a d /\ is_arrival_curve a alpha /\ is_minimal_service S Beta)  , is_arrival_curve d (DeconvAlphaBeta S alpha Beta a d proof).
Admitted.

(*if the delay between a and d is bounded for any input output pair, then there exist a delta function that is a minimal service curve for the server*)
Theorem delta_service_curve `(S: Server s) :
forall a d T, s a d -> (Rbar_le (delay a d) T <-> is_minimal_service S (DeltaIncr T)).
Admitted.

End NCDefinitions.