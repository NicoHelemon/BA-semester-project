(** This section illustrates network calculus concepts through examples*)

From Coq Require Import Reals ssreflect FunctionalExtensionality Setoid Image.
From Coquelicot Require Import Rbar.
From Coquelicot Require Import Rcomplements.
From Coquelicot Require Import Compactness Lim_seq Rcomplements Hierarchy Lub.
From mathcomp Require Import ssrnat.
Require Import FunImage.
Require Import InfSup.
Require Import RbarComp.
Require Import Main Definitions.

Generalizable Variables a.

(* Definition of a leaky bucket*)
Definition leaky_bucket (r: R) (b : Rbar) : R -> Rbar := fun t: R => match Req_appart_dec 0 t with
| left _ => 0
| right _ => Rplus (r * t) b
end.

(*Definition of a rate latency service curve*)
Definition rate_latency (r T: R):= f_plus(fun t => r * (t - T)).

(* A leaky bucket is non decreasing and postive*)
Global Instance leaky_bucket_incr (r b : R) : Rbar_le 0 r -> Rbar_le 0 b -> NonDecreasingPositive (leaky_bucket r b).
intros.
pose (Rle_refl 0).
simpl in H.
simpl in H0.
split.
split.
intros.
unfold leaky_bucket.
destruct Req_appart_dec.
simpl.
intuition.
simpl.
apply Rge_le in H1.
pose (Rmult_le_compat 0 r 0 x r0 r0 H H1).
setoid_rewrite Rmult_0_l in r1.
pose (Rplus_le_compat 0 (r * x) 0 b r1 H0).
setoid_rewrite Rplus_0_l in r2.
tauto.
unfold non_decreasing.
intros.
unfold leaky_bucket.
destruct Req_appart_dec.
destruct Req_appart_dec.
simpl.
intuition.
simpl.
destruct H1.
apply Rge_le in H3.
pose (Rmult_le_compat 0 r 0 t r0 r0 H H3).
setoid_rewrite Rmult_0_l in r1.
pose (Rplus_le_compat 0 (r * t) 0 b r1 H0).
setoid_rewrite Rplus_0_l in r2.
tauto.
destruct Req_appart_dec.
rewrite <- e in H2.
destruct H1.
apply Rge_not_lt in H1.
tauto.
simpl.
apply (Rplus_le_compat_r).
apply (Rmult_le_compat_l).
intuition.
intuition.
Qed.

(*A leaky bucket with a positive rate and a burst equal to 0 is cumulative*)
Global Instance leaky_bucket_cumul (r: R) : Rbar_le 0 r -> Cumulative (leaky_bucket r 0).
intros.
pose (Rge_refl 0).
pose (leaky_bucket_incr r 0 H r0).
split.
tauto.
admit.
unfold leaky_bucket.
destruct Req_appart_dec.
reflexivity.
rewrite Rmult_0_r.
rewrite Rplus_0_l.
reflexivity.
Admitted.

Generalizable Variables s.

(* The deconvolution between a leaky bucket and a rate latency curve is also a leaky bucket*)
Theorem deconv_leaky_latency : forall r b r' T x: R, r' > r /\ r >= 0 /\ T >= 0 -> deconv (leaky_bucket r b) (rate_latency r' T) x = leaky_bucket r (b + T) x.
Proof.
intros.
destruct H as [p0].
destruct H as [p1].
pose (Rgt_ge r' r p0).
pose (Rge_trans r' r 0 r0 p1).
unfold leaky_bucket, deconv, rate_latency.
unfold f_plus.
unfold Rbar_max.
unfold Rbar_minus.
simpl.
rewrite Ropp_0.
apply sup_eq.
destruct Req_appart_dec.
rewrite <- e.
split.
intros.
apply Im_inv in H0.
destruct H0.
destruct H0.
unfold In in H0.
rewrite <- H1.
destruct Req_appart_dec.
setoid_rewrite Rbar_plus_0_l.
rewrite Rplus_0_l in e0.
rewrite <- e0.
unfold Rminus.
rewrite  Rplus_0_l.
rewrite Rmult_comm.
rewrite Ropp_involutive.
pose (Rmult_ge_compat r' 0 T 0 (Rge_refl 0) (Rge_refl 0) r1 H).
setoid_rewrite (Rmult_0_l) in r2.
rewrite <- Ropp_mult_distr_l.
rewrite Ropp_involutive.
apply Rge_le in r2.
rewrite Rmin_left.
simpl.
intuition.
rewrite Rmult_comm.
trivial.
rewrite Ropp_involutive.
rewrite Rplus_0_l.
simpl.
apply Rmin_case.
Admitted.






