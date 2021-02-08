(** This section defines a packetizer and proves theorems about it.
After that the concatenation between a bit by bit system and a scheduler is analysed.*)

From Coq Require Import Reals Setoid Image Decidable PeanoNat Plus ClassicalDescription FunctionalExtensionality.
Require Import FunImage Definitions RbarComp SetTheory Seq Main InfSup.
From Coquelicot Require Import Rbar Lub.

(** * Packet below*)

(*The set of i such that the partial sum of l from 0 to i is less than a given value*)
Definition packet_below (l: nat -> nat) (b: R): Ensemble nat :=
match Rle_dec 0 b with
|left _ => (fun n: nat => Rle (INR (nat_sum l n)) b)
|right _ => Singleton nat O
end.

(*If b1 <= b2 than packet_below b1 included in packet_below b2*)
Theorem packet_below_incl: forall (l: nat -> nat) (c: l O = O) (b1 b2 : R), b1 <= b2 -> Included nat (packet_below l b1) (packet_below l b2).
Proof.
unfold Included.
unfold packet_below.
unfold nat_sum.
unfold In.
intros.
induction (Rle_dec 0 b1) in H0.
induction (Rle_dec 0 b2).
apply (Rle_trans _ _ _ H0 H).
apply Rnot_le_lt in b.
pose (Rle_lt_trans _ _ _ H b).
pose (Rle_lt_trans _ _ _ a r).
apply (Rlt_not_le) in r0.
case (r0 (Rle_refl 0)).
induction (Rle_dec 0 b2).
apply Singleton_inv in H0.
rewrite <-  H0.
simpl.
rewrite c.
tauto.
tauto.
Qed.

(*packet_below is bounded above*)
Theorem packet_below_bounded : forall l b, nat_bounded (packet_below l b).
Admitted.

(*packet_below is never empty*)
Theorem packet_below_non_empty: forall l b, l O = O -> packet_below l b <> Empty_set nat.
Proof.
intros.
apply non_empty.
exists O.
unfold packet_below.
unfold nat_sum.
induction (Rle_dec 0 b).
simpl.
rewrite H.
tauto.
apply Singleton_intro.
tauto.
Qed.

(*Definition of the maximum of packet_below*)
Definition last_packet (l: nat -> nat) (z: l O = O) (b: R):=
nat_max (packet_below l b) (packet_below_bounded l b) (packet_below_non_empty l b z). 


(*The maximum of packet_below 0 is 0*)
Theorem last_packet_0 : forall l z (sp: strict_pos l), last_packet l z 0 = O.
intros.
unfold last_packet.
unfold nat_max.
pose (ex_nat_max (packet_below l 0) (packet_below_bounded l 0) (packet_below_non_empty l 0 z)).
assert (set_is_maximum (packet_below l 0) le le_order O).
unfold set_is_maximum.
split.
unfold packet_below.
induction Rle_dec.
unfold nat_sum.
simpl.
rewrite z.
apply (Rle_refl 0).
apply Singleton_intro.
tauto.
unfold packet_below.
intros.
induction (Rle_dec 0 0) in H.
pose (pos_INR (nat_sum l s')).
pose (Rle_antisym _ _ H r).
fold (INR O) in e.
apply INR_eq in e.
apply nat_sum_length_0 in e.
intuition.
apply z.
apply sp.
apply Singleton_inv in H.
intuition.
apply set_maximum_unique.
apply H.
Qed.

(*If b1 <= b2 than the maximum of packet_below b1 is smaller than the maximum of packet_below b2*)
Theorem last_packet_le : forall l b1 b2 (z: l O = O), b1 <= b2 -> le (last_packet l z b1) (last_packet l z b2).
Proof.
intros.
pose (packet_below_incl l z b1 b2 H).
apply (set_maximum_included _ _ le le_order (ex_nat_max _ (packet_below_bounded l b1) (packet_below_non_empty l b1 z)) (ex_nat_max _ (packet_below_bounded l b2) (packet_below_non_empty l b2 z)) i).
Qed.

(*If b lies between two terms of the partial sum, then this n is the maximum of packet_below b*)
Theorem last_packet_bounds : forall l z b n (p: b >= 0), INR(nat_sum l n) <= b < INR(nat_sum l (S n)) <-> last_packet l z b = n.
intros.
split.
intros.
unfold last_packet.
unfold nat_max.
apply set_maximum_unique.
unfold set_is_maximum.
split.
unfold packet_below.
induction (Rle_dec 0 b).
tauto.
apply Rge_le in p.
tauto.
intros.
unfold packet_below in H0.
induction (Rle_dec 0 b).
destruct H.
pose (Rle_lt_trans _ _ _ H0 H1).
apply INR_lt in r.
pose (nat_sum_incr l).
apply seq_increasing_eq in s.
pose (seq_increasing_imp le le_order (nat_sum l) s s' (S n)).
pose (Nat.lt_le_incl _ _ r).
pose (Nat.lt_neq _ _ r).
pose (l0 l1 n0).
apply Nat.lt_succ_r.
tauto.
apply Singleton_inv in H0.
rewrite <- H0.
apply le_0_n.
intros.
unfold last_packet in H.
unfold nat_max in H.
pose (set_maximum_is_maximum (packet_below l b) le le_order (ex_nat_max (packet_below l b) (packet_below_bounded l b) (packet_below_non_empty l b z))).
rewrite H in s.
unfold set_is_maximum in s.
unfold packet_below in s.
destruct s.
induction (Rle_dec 0 b).
split.
tauto.
apply not_not.
unfold decidable.
tauto.
intro pp.
apply Rnot_lt_le in pp.
pose (H1 (S n ) pp).
pose (Nat.le_succ_l n n).
destruct i.
pose (H2 l0).
intuition.
apply Rge_le in p.
tauto.
Qed.

(** ** Cumul below*)

(*set of the partial sums of l from 0 to i such that they are below a given value*)
Definition cumul_below (l: nat -> nat) (b: R) := fun r => exists n, packet_below l b n /\ r = INR (nat_sum l n).

(*cumul_below is never empty*)
Theorem cumul_below_non_empty: forall l b, l O = O -> cumul_below l b <> Empty_set R.
intros.
unfold cumul_below.
pose (packet_below_non_empty l b H).
apply non_empty in n.
destruct n.
apply non_empty.
exists (INR (nat_sum l x)).
exists x.
split.
tauto.
tauto.
Qed.

(*cumul_below is always bounded*)
Theorem cumul_below_bounded : forall l b, set_bounded_above (cumul_below l b) Rle Rle_order.
intros.
pose (packet_below_bounded l b).
unfold nat_bounded in n.
unfold cumul_below.
unfold set_bounded_above.
unfold set_is_bound_above.
unfold set_bounded_above in n.
unfold set_is_bound_above in n.
destruct n.
exists (INR (nat_sum l x)).
intros.
destruct H0.
destruct H0.
pose (H x0 H0).
pose (nat_sum_incr l).
apply seq_increasing_eq in s0.
unfold seq_increasing in s0.
pose (s0 x0 x l0).
apply le_INR in l1.
rewrite <- H1 in l1.
tauto.
Qed.

(*Definition if the maximum of cumul_below*)
Definition last_cumul (l: nat -> nat) (z: l O = O) (b: R) : R:=
R_max (cumul_below l b) (cumul_below_bounded l b) (cumul_below_non_empty l b z).

(*If b1 <= b2 than cumul_below b1 included in cumul_below b2*)
Theorem cumul_below_incl: forall (l: nat -> nat) (c: l O = O) (b1 b2 : R), b1 <= b2 -> Included R (cumul_below l b1) (cumul_below l b2).
Proof.
intros l c b1 b2 p.
pose (packet_below_incl l c b1 b2 p).
unfold Included.
unfold cumul_below.
unfold nat_sum.
unfold In.
intros.
unfold Included in i.
unfold In in i.
destruct H.
exists x0.
destruct H.
split.
apply i.
tauto.
tauto.
Qed.

(*If b1 <= b2 than the maximum of cumul_below b1 is smaller than the maximum of cumul_below b2*)
Theorem last_cumul_le : forall l b1 b2 (z: l O = O), b1 <= b2 -> Rle (last_cumul l z b1) (last_cumul l z b2).
Proof.
intros.
pose (cumul_below_incl l z b1 b2 H).
apply (set_maximum_included _ _ Rle Rle_order (ex_R_max _ (cumul_below_bounded l b1) (cumul_below_non_empty l b1 z)) (ex_R_max _ (cumul_below_bounded l b2) (cumul_below_non_empty l b2 z)) i).
Qed.

(** * Relation between last packet and last cumul*)

(*The partial sum of n until the maximum of packet_below belongs to cumul_below*)
Theorem last_packet_in_cumul (l: nat -> nat) (z: l O = O) (b: R) : cumul_below l b (INR (nat_sum l (last_packet l z b))).
unfold cumul_below.
exists (last_packet l z b).
split.
unfold last_packet.
unfold nat_max.
apply set_maximum_in.
tauto.
Qed.

(*The partial sum of n until the maximum of packet_below is the maximum of cumul_below*)
Theorem last_cumul_packet (l: nat -> nat) (z: l O = O) (b: R) :
last_cumul l z b = INR(nat_sum l (last_packet l z b)).
unfold last_cumul.
unfold R_max.
assert(set_is_maximum (cumul_below l b) Rle Rle_order (INR (nat_sum l (last_packet l z b)))).
split.
apply last_packet_in_cumul.
intros.
unfold cumul_below in H.
destruct H.
destruct H.
rewrite H0.
pose (set_maximum_is_maximum (packet_below l b) le le_order).
pose (ex_nat_max _  (packet_below_bounded l b) (packet_below_non_empty l b z)).
pose (s s0).
unfold set_is_maximum in s1.
destruct s1.
pose (H2 x H).
assert (le x (last_packet l z b)).
unfold last_packet.
unfold nat_max.
apply l0.
pose (nat_sum_incr l).
apply seq_increasing_eq in s1.
unfold seq_increasing in s1.
pose (s1 x (last_packet l z b) H3).
apply le_INR in l1.
tauto.
apply set_maximum_unique.
tauto.
Qed.

(** * Packetization*)

Generalizable Variables a al l.

(*Sequence of packet lengths*)
Class LengthSequence (l: nat -> nat) := {
  str_pos : strict_pos l;
  im_0: l O = O;
  ex_max: nat_seq_ex_max l
}.

(*Greatest packket lenngth*)
Definition lmax `(ls: LengthSequence l) := nat_seq_max l ex_max.


(*Definition of the packetization of a value*)
Definition packetization (l: nat -> nat) (ls: LengthSequence l) (v: Rbar): Rbar := 
  match v with
  |Finite x => last_cumul l im_0 x
  |p_infty => p_infty
  |m_infty => 0
  end.
 

(*The packetization of 0 is always equal to 0*)
Theorem packetization_0 (l: nat -> nat) (ls: LengthSequence l): packetization l ls 0 = 0.
intros.
unfold packetization.
rewrite last_cumul_packet.
rewrite last_packet_0.
unfold nat_sum.
simpl.
destruct ls.
rewrite im_1.
tauto.
destruct ls.
tauto.
Qed.

(*Equivalent description of the packetization*)
Theorem packetization_eq : forall l ls (v: R) (p: v >= 0) n, packetization l ls v = INR(nat_sum l n) <-> INR(nat_sum l n) <= v < INR(nat_sum l (S n)).
intros.
destruct ls.
assert(is_finite v).
unfold is_finite.
simpl.
tauto.
unfold is_finite in H.
rewrite <- H.
unfold packetization.
split.
2:{intros.
pose (last_packet_bounds l im_1 v n p).
destruct i.
pose (H1 H0).
rewrite <- e.
apply finite_eq.
apply (last_cumul_packet l im_1 v).
}
intros.
pose (last_packet_bounds l im_1 v n p).
destruct i.
apply H2.
unfold last_cumul in H0.
unfold R_max in H0.
pose (set_maximum_is_maximum (cumul_below l v) Rle Rle_order (ex_R_max (cumul_below l v) (cumul_below_bounded l v) (cumul_below_non_empty l v im_1))).
apply finite_eq in H0.
setoid_rewrite H0 in s.
unfold set_is_maximum in s.
unfold cumul_below in s.
destruct s.
apply set_maximum_unique.
destruct H3.
destruct H3.
unfold set_is_maximum.
split.
unfold packet_below in H3.
unfold packet_below.
induction (Rle_dec 0 v).
rewrite H5.
tauto.
apply Rge_le in p.
tauto.
intros.
pose (nat_sum_length_strict_incr l im_1 str_pos0).
apply nat_seq_strict_incr_eq in n0.
pose (nat_seq_strict_incr_imp _ n0).
pose (H4 (INR (nat_sum l s'))).
apply l0.
apply INR_le.
apply r.
exists s'.
split.
tauto.
tauto.
Qed.

(* the image of the packetization function is a susbet the image of the partial sum of l*)
Theorem packetization_is_sum: forall l ls (v: R), exists n, packetization l ls v = INR(nat_sum l n).
intros.
unfold packetization.
destruct ls.
exists (last_packet l im_1 v).
rewrite last_cumul_packet.
tauto.
Qed.

(* the packetization of v is bounded betweeen v- lmax and v*)
Theorem packetization_bounds: forall l ls (v: R) (p: v >= 0), v - (INR(lmax ls)) < packetization l ls v <= v.
intros.
unfold lmax.
pose (packetization_is_sum l ls v).
destruct e.
pose (packetization_eq l ls v p x).
destruct i.
pose (H0 H).
split.
2:{rewrite H.
tauto.
}
destruct a.
unfold nat_sum in H3.
simpl in H3.
rewrite plus_INR in H3.
assert ((INR(l(S x))) <= (INR(nat_seq_max l ex_max))).
apply le_INR.
unfold nat_seq_max.
unfold seq_max.
assert (forall m, set_is_maximum (im_seq l) le le_order m -> le (l (S x))  m).
intros.
unfold set_is_maximum in H4.
destruct H4.
apply H5.
unfold im_seq.
pose (Im_intro nat nat universe l (S x)).
apply i.
unfold In.
unfold universe.
tauto.
tauto.
apply H4.
apply set_maximum_is_maximum.
apply (Rplus_le_compat_l (INR (partial_sum Init.Nat.add l x)) _ _) in H4.
rewrite H.
pose (Rlt_le_trans _ _ _ H3 H4).
apply (Rplus_lt_compat_r (- INR (nat_seq_max l ex_max)) _ _) in r.
rewrite Rplus_assoc in r.
rewrite Rplus_opp_r in r.
rewrite Rplus_0_r in r.
tauto.
Qed.

(*The packetization function is idempotent*)
Theorem packetization_idempotent (a: R -> Rbar) (l: nat -> nat) ls v : packetization l ls (packetization l ls v) = packetization l ls v.
pose (packetization_is_sum l ls v).
destruct e.
unfold packetization in H.
unfold packetization.
induction v.
pose (finite_eq (last_cumul l im_0 r) (INR(nat_sum l x))).
destruct i.
apply H1 in H.
rewrite H.
rewrite last_cumul_packet.
assert (last_packet l im_0 (INR (nat_sum l x)) = x).
unfold last_packet.
unfold nat_max.
apply set_maximum_unique.
unfold set_is_maximum.
split.
unfold packet_below.
induction (Rle_dec 0 (INR (nat_sum l x))).
intuition.
pose (pos_INR (nat_sum l x)).
tauto.
destruct ls.
intros.
unfold packet_below in H2.
induction (Rle_dec).
pose (nat_sum_length_strict_incr l).
apply nat_seq_strict_incr_eq in n.
pose (nat_seq_strict_incr_imp (nat_sum l) n).
apply INR_le in H2.
apply l0 in H2.
tauto.
tauto.
tauto.
apply Singleton_inv in H2.
rewrite <- H2.
apply le_0_n.
rewrite H2.
tauto.
tauto.
rewrite last_cumul_packet.
rewrite last_packet_0.
unfold nat_sum.
simpl.
destruct ls.
rewrite im_1.
tauto.
destruct ls.
tauto.
Qed.

(*The packetization function is isotone*)
Definition packetization_isotone_2 : forall (a: R -> Rbar) (l: nat -> nat) ls (x: Rbar) (y: Rbar), Rbar_le x y -> Rbar_le (packetization l ls x) (packetization l ls y).
intros.
induction x.
induction y.
2:{simpl.
tauto.
}
2:{
case H.
}
2:{
induction y.
case H.
simpl.
tauto.
case H.
}
2:{induction y.
simpl.
rewrite last_cumul_packet.
apply pos_INR.
simpl.
tauto.
simpl.
apply Rle_refl.
}
simpl.
destruct ls.
simpl in H.
apply (last_cumul_le l r r0 im_0 H).
Qed.

(** * Packetizer*)

Generalizable Variables p s beta.

 
(*Definition of the packetizer*)
Definition packetizer (a: R -> Rbar) (l: nat -> nat) ls : R -> Rbar := fun t => packetization l ls (a t).

(*Output of a packetizer*)
Definition packetized `(ls : LengthSequence l) (a: R -> Rbar) : Prop := packetizer a l ls = a.  

(*The output of a packetizer that takes a cumulative function as input is a also cumulative*)
Theorem packetizer_cumul `(A: Cumulative a) : forall l ls, Cumulative (packetizer a l ls).
intros.
destruct ls.
unfold packetizer.
unfold packetization.
destruct A.
destruct non_decr_pos.
pose (PosNotMInf positive).
destruct positive.
destruct n.
split.
split.
split.
intros.
induction (a x).
simpl.
rewrite last_cumul_packet.
apply pos_INR.
simpl.
tauto.
apply Rle_refl.
  
unfold non_decreasing.
intros.
destruct H.
pose (Rbar_dec (a s)).
pose (Rbar_dec (a t)).
case o.
intros.
rewrite H2.
case o0.
intros.
rewrite H3.
apply Rbar_le_refl.
intros.
case H3.
intros.
pose (not_inf t H1).
apply (eq_sym) in H4.
case (n H4).
intros.
unfold is_finite in H4.
unfold non_decreasing in non_decr.
pose (non_decr s t (conj H H1) H0).
rewrite H2 in r.
rewrite <- H4 in r.
simpl in r.
case r.
intros.
case H2.
intros.
pose (not_inf s H).
apply (eq_sym) in H3.
case (n H3).
intros.
unfold is_finite in H3.
rewrite <- H3.
case o0.
intros.
rewrite H4.
simpl.
tauto.
intros.
case H4.
intros.
pose (not_inf t H1).
apply (eq_sym) in H5.
case (n H5).
intros.
unfold is_finite in H5.
rewrite <- H5.
rewrite last_cumul_packet.
rewrite last_cumul_packet.
apply le_INR.
pose (last_packet_le).
unfold non_decreasing in non_decr.
pose (non_decr s t (conj H H1) H0).
rewrite <- H3 in r.
rewrite <- H5 in r.
simpl in r.
pose (l0 l (a s) (a t) im_1).
pose (nat_sum_incr l).
apply (seq_increasing_eq) in s0.
unfold seq_increasing_2 in s0.
pose (s0 _ _ (l1 r)).
apply l2.
2:{
rewrite start_0.
rewrite last_cumul_packet.
rewrite last_packet_0.
unfold nat_sum.
simpl.
rewrite im_1.
simpl.
tauto.
Admitted.

(*Definition of the packetizer as a server*)
Definition packetizer_serv `(ls: LengthSequence l) := fun a d => Cumulative a /\ d = packetizer a l ls.

(*The packetizer is a server*)
Global Instance Packetizer `(ls: LengthSequence l) : Server (packetizer_serv ls).
unfold packetizer_serv.
split.
intros.
destruct H.
split.
tauto.
rewrite H0.
apply packetizer_cumul.
tauto.
intros.
exists (packetizer a l ls).
tauto.
intros.
destruct H.
rewrite H1.
unfold packetizer.
unfold packetization.
destruct H.
destruct non_decr_pos.
destruct positive.
pose (pos_to_pos t H0).
pose (Rbar_dec (a t)).
case o.
intros.
rewrite H.
simpl.
tauto.
intros.
case H.
intros.
rewrite H2 in r.
simpl in r.
case r.
intros.
unfold is_finite in H2.
rewrite <- H2.
simpl.
rewrite <- H2 in r.
simpl in r.
pose (packetization_bounds l ls (a t)).
case (Rlt_dec 0 (a t)).
intros.
rewrite <- H2 in r0.
apply Rlt_gt in r0.
apply Rgt_ge in r0.
apply a0 in r0.
unfold packetization in r0.
destruct r0.
intuition.
intros.
apply Rnot_lt_le in n.
pose (Rle_antisym 0 (a t) r n).
rewrite <- e.
rewrite last_cumul_packet.
rewrite last_packet_0.
unfold nat_sum.
simpl.
destruct ls.
rewrite im_1. 

apply Rle_refl.
destruct ls.
tauto.
Qed.

(*the backlog between the input and output of the packetizer is smaller than lmax*)

Theorem backlog_packetizer : forall `(A: Cumulative a) (l: nat -> nat) (ls: LengthSequence l), 
Rbar_le (backlog a (packetizer a l ls)) (INR (lmax ls)).
intros.
unfold lmax.
assert (forall t, t >= 0 -> Rbar_le (backlog_t a (packetizer a l ls) t) (INR (nat_seq_max l ex_max))).
intros.
unfold backlog_t.
unfold packetizer.
destruct A.
destruct non_decr_pos.
destruct positive.
pose (pos_to_pos t H).
case (Rbar_dec (a t)).
intros.
rewrite H0.
simpl.
apply pos_INR.
intros.
case H0.
intros.
rewrite H1.
simpl.
exact I.
intros.
unfold is_finite in H1.
rewrite <- H1.
rewrite <- H1 in r.
simpl in r.
simpl.
apply Rle_ge in r.
pose (packetization_bounds l ls (a t) r).
rewrite <- H1 in a0.
simpl in a0.
destruct a0.
pose (Rplus_lt_compat_r (INR (nat_seq_max l ex_max)) _ _ H2).
unfold Rminus in r0.
rewrite Rplus_assoc in r0.
rewrite Rplus_opp_l in r0.
rewrite Rplus_0_r in r0.
pose (Rplus_lt_compat_l (- last_cumul l im_0 (a t)) _ _ r0).
rewrite <- Rplus_assoc in r1.
rewrite Rplus_opp_l in r1.
rewrite Rplus_0_l in r1.
rewrite Rplus_comm in r1.
apply Rlt_le in r1.
tauto.
unfold backlog.
apply ge_sup.
intros.
apply Im_inv in H0.
destruct H0.
destruct H0.
unfold In in H0.
pose (H x0 H0).
rewrite H1 in r.
exact r.
Qed.

(*If the input of a packetizer is finite then its output is finite as well*)
Theorem packetizer_finite_t `(A: Cumulative a): forall l ls t, t >= 0 -> is_finite (a t) <-> is_finite (packetizer a l ls t).
split.
unfold is_finite.
intros.
unfold packetizer.
rewrite <- H0.
simpl.
tauto.

apply contrapositive.
unfold decidable.
tauto.
intros.
apply Rbar_not_finite in H0.
case H0.
intros.
unfold packetizer in H1.
rewrite H2 in H1.
unfold is_finite in H1.
simpl in H1.
pose (Rbar_le_refl p_infty).
rewrite <- H1 in r at 2.
case r.
intros.
destruct A.
destruct non_decr_pos.
destruct positive.
pose (pos_to_pos t H).
rewrite H2 in r.
case r.
Qed.


(*If the input of a packetizer is finite then its output is finite as well*)
Theorem packetizer_finite `(A: Cumulative a): forall l ls, is_finite_f a <-> is_finite_f (packetizer a l ls ).
split.
unfold is_finite_f.
intros.
pose (H x H0).
unfold is_finite.
unfold is_finite in i.
unfold packetizer.
rewrite <- i.
simpl.
tauto.

apply contrapositive.
unfold decidable.
tauto.
intros.
unfold is_finite_f in H.
apply not_all_ex_not in H.
destruct H.
unfold is_finite_f in H0.
apply not_imp in H.
destruct H.
apply Rbar_not_finite in H1.
case H1.
intros.
pose (H0 x H).
unfold packetizer in i.
rewrite H2 in i.
simpl in i.
unfold is_finite in i.
simpl in i.
pose (Rbar_le_refl p_infty).
rewrite <- i in r at 2.
case r.
intros.
destruct A.
destruct non_decr_pos.
destruct positive.
pose (pos_to_pos x H).
rewrite H2 in r.
case r.
unfold decidable.
tauto.
Qed.

(* A non decreasing positive function plus lmax remains non decreasing and positive*)
Global Instance NonDecrPlusLmax `(P: NonDecreasingPositive p) `(ls: LengthSequence l): NonDecreasingPositive (fun t => Rbar_plus (p t) (INR(lmax ls))).
apply NonDecrPlus.
tauto.
simpl.
apply pos_INR.
Qed.

(*Arrival curve of the output of the packetizer*)
Theorem packetizer_arrival_curve `(A: Cumulative a) `(alpha: NonDecreasingPositive al) `(ls: LengthSequence l) :
is_finite_f a -> is_arrival_curve a alpha -> is_arrival_curve (packetizer a l ls) (NonDecrPlusLmax alpha ls).
intros.
pose (proj1(packetizer_finite A l ls) H).
apply arr_cur_eq.
tauto.
unfold is_arrival_curve_2.
intros.
unfold is_finite_f in i.
pose (i s H2).
pose (i t H3).
unfold is_finite in i0, i1.
rewrite <- i0.
rewrite <- i1.
apply arr_cur_eq in H0.
unfold is_arrival_curve_2 in H0.
pose (H0 A s t H2 H3 H4).
case (Rbar_dec (al (t - s))).
intros.
rewrite H5.
simpl.
exact I.
intros.
case H5.
intros.
rewrite H6.
destruct alpha.
destruct positive.
pose(pos_to_pos (t - s)).
pose  H4.
apply (Rplus_le_compat_r (-s) s t) in r1.
rewrite Rplus_opp_r in r1.
apply Rle_ge in r1.
apply r0 in r1.
rewrite H6 in r1.
simpl in r1.
case r1.
intros.
unfold is_finite in H6.
rewrite <- H6.
unfold is_finite_f in H.
pose (H s H2).
pose (H t H3).
unfold is_finite in i2, i3.
unfold packetizer.
pose (packetization_bounds l ls).
rewrite <- i2 in r.
rewrite <- i3 in r.
rewrite <- H6 in r.
destruct A.
destruct non_decr_pos.
destruct positive.
pose (pos_to_pos s H2).
pose (pos_to_pos t H3).
rewrite <- i2 in r0.
rewrite <- i3 in r1.
apply Rle_ge in r0.
apply Rle_ge in r1.
pose (a0 (a s) r0).
pose (a0 (a t) r1).
destruct a1.
destruct a2.
simpl in r.
apply (Ropp_lt_contravar) in H7.
apply Rlt_le in H7.
pose (Rplus_le_compat _ _ _ _ H10 H7).
unfold Rminus in r2.
rewrite Ropp_plus_distr in r2.
rewrite Ropp_involutive in r2.
rewrite <- Rplus_assoc in r2.
pose (Rplus_le_compat_r (INR(lmax ls)) _ _ r).
pose (Rle_trans _ _ _ r2 r3).
simpl.
rewrite <- i2.
rewrite <- i3.
apply r4.
tauto.
Qed.

(** * Arrival times*)

(* Definition of the arrival time of the nth packet*)
Definition arrival_time `(ls: LengthSequence l) (a: R -> Rbar) := (fun n => Glb_Rbar (fun t => t >= 0 /\ (packetizer a l ls) t = INR(nat_sum l n))).

(* The arrival time of the 0th packet is 0*)
Theorem arrival_time_0 `(ls : LengthSequence l) : forall a (A: Cumulative a), arrival_time ls a 0 = 0.
intros.
apply is_glb_Rbar_unique.
unfold is_glb_Rbar.
unfold is_lb_Rbar.
split.
intros.
apply Rge_le.
tauto.
intros.
unfold nat_sum in H.
simpl in H.
rewrite im_0 in H.
destruct ls.
unfold packetizer in H.
unfold packetization in H.
simpl in H.
destruct A.
pose (H 0).
apply r.
split.
intuition.
rewrite start_0.
rewrite last_cumul_packet.
rewrite last_packet_0.
unfold nat_sum.
simpl.
rewrite im_1.
tauto.
tauto.
Qed.

(*If the output of a packetizer is bounded then from a given n, the arrival time of the packets will be infinite*)
Theorem arrival_time_bounded `(ls : LengthSequence l) : forall a (A: Cumulative a) (t: R) n, set_is_bound_above (Im R Rbar (fun x => x >= 0) (packetizer a l ls)) Rbar_le Rbar_le_order (INR(nat_sum l n)) -> (arrival_time ls a (S n)) = p_infty.
intros.
unfold set_is_bound_above in H.
unfold arrival_time.
apply is_glb_Rbar_unique.
unfold is_glb_Rbar.
unfold is_lb_Rbar.
split.
intros.
destruct H0.
pose (H (packetizer a l ls x)).
assert (Im R Rbar (fun x : R => x >= 0) (packetizer a l ls) (packetizer a l ls x)).
apply (Im_intro R Rbar _ _ x).
unfold In.
tauto.
tauto.
pose (r H2).
rewrite H1 in r0.
simpl in r0.
apply INR_le in r0.

assert(nat_seq_strict_incr (nat_sum l)).
destruct ls.
apply (nat_sum_length_strict_incr l im_1 str_pos0).

unfold nat_seq_strict_incr in H3.
pose (H3 n).
apply le_not_lt in r0.
tauto.

intros.
induction b.
simpl.
tauto.
simpl.
tauto.
simpl.
tauto.
Qed.

(* The arrival times of the packets partition n*)
Theorem arrival_time_partition `(ls : LengthSequence l) : forall a (A: Cumulative a) (t: R), exists i, Rbar_le t (arrival_time ls a i).
intros.
case (classic (set_bounded_above (Im R Rbar (fun x => x >= 0) (packetizer a l ls)) Rbar_le Rbar_le_order)).
2:{
intros.
unfold set_bounded_above in H.
pose(not_ex_all_not Rbar _ H).
unfold set_is_bound_above in n.
unfold arrival_time.

assert(forall n : Rbar, exists s : Rbar, Im R Rbar (fun x : R => x >= 0) (packetizer a l ls) s /\ Rbar_lt n s).
intros.
pose (n n0).
apply not_all_ex_not in n1.
destruct n1.
exists x.
apply not_imp in H0.
split.
tauto.
destruct H0.
apply Rbar_not_le_lt in H1.
tauto.
unfold decidable.
tauto.

apply not_not.
unfold decidable.
tauto.
intro p.
pose(not_ex_all_not nat _ p).

pose (H0 (packetizer a l ls t)).
destruct e.
destruct H1.
apply Im_inv in H1.
destruct H1.
destruct H1.
rewrite <- H3 in H2.
case (Rbar_dec (packetizer a l ls x0)).
2:{
intros.
case H4.
2:{
intros.
assert(is_finite(a x0)).
unfold In in H1.
setoid_rewrite <- (packetizer_finite_t A l ls x0 H1) in H5.
tauto.
pose (packetization_is_sum l ls (real(a x0))).
destruct e.
unfold is_finite in H6.
rewrite H6 in H7.
fold (packetizer a l ls x0) in H7.
pose (n0 x1).
apply Rbar_not_le_lt in n1.
rewrite inf_Rbar_Rbar in n1.
apply gt_inf in n1.
destruct n1.
destruct H8.
unfold set_R_to_Rbar in H8.
destruct H8.
destruct H10.
unfold is_finite in H8.
rewrite <- H8 in H9.
simpl in H9.
pose (packetizer_cumul A l ls).
destruct c.
destruct non_decr_pos.
apply non_decr_eq in non_decr.
unfold non_decreasing_2 in non_decr.
pose (Rge_trans t x2 0 (Rle_ge _ _ H9) H10).
pose (non_decr x2 t (conj H10 r) H9).
rewrite <- H11 in H7.
rewrite <- H7 in r0.
apply Rbar_le_not_lt in r0.
tauto.
}
intros.
unfold In in H1.
pose (packetizer_cumul A l ls).
destruct c.
destruct non_decr_pos.
destruct positive.
pose(pos_to_pos x0 H1).
rewrite H5 in r.
case r.
}
intros.
pose (H0 p_infty).
destruct e.
destruct H5.
simpl in H6.
case H6.
Admitted.

(** * Combined systems*)

(*Definition of a the concatenation between a bit by bit system and a packetizer*)
Definition combined_system `(S: Server s) `(ls: LengthSequence l) := server_concat S (Packetizer ls).

(*The concatenation of a bit by bit system and a packetizer is a system*)
Global Instance CombinedSystem `(S: Server s) `(ls: LengthSequence l) : Server (combined_system S ls).
apply ServerConcat.
Qed.

(*Gives bounds on the backlog of a combined system*)

Theorem combined_backlog `(S: Server s) `(ls : LengthSequence l) : forall a d d',s a d -> packetizer_serv ls d d' -> Rbar_le(backlog a d) (backlog a d') /\ Rbar_le (backlog a d') (Rbar_plus (backlog a d) (INR(lmax ls))).
(*intros a d d' H0 H1.
assert(forall t, t >= 0 -> Rbar_le (backlog_t a d t) (backlog_t a d' t) /\
Rbar_le (backlog_t a d' t) (Rbar_plus (backlog_t a d t) (INR (lmax ls)))).
intros.
unfold backlog_t.
pose (finite_server_t S a d H0 H).
pose (finite_server (Packetizer2 ls) d d' H1 i).
unfold is_finite_f in H, i, i0.
pose (H t H2).
pose (i t H2).                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              
pose (i0 t H2).
unfold is_finite in i1, i2, i3.
rewrite <- i1.
rewrite <- i2.
rewrite <- i3.
simpl.
unfold packetizer_serv in H1.
destruct H1.
rewrite e.
pose (packetization_bounds l ls (d t)).
destruct c.
destruct non_decr_pos.
destruct positive.
pose(pos_to_pos t H2).
rewrite <- i2 in r.
simpl in r.
apply Rle_ge in r.
destruct (a0 r).
unfold packetizer.
rewrite <- i2.

split.
apply Rplus_le_compat_l.
apply Ropp_le_cancel.
rewrite Ropp_involutive.
rewrite Ropp_involutive.
tauto.
rewrite Rplus_assoc.
apply Rplus_le_compat_l.
apply Ropp_le_cancel.
rewrite Ropp_plus_distr.
rewrite Ropp_involutive.
rewrite Ropp_involutive.
apply Rlt_le in H1.
tauto.
unfold backlog.
split.
apply sup_le_sup_image.
intros.
unfold In in H3.
pose (H2 x H3).
tauto.
rewrite Rbar_plus_comm.
rewrite sup_independence.
apply sup_le_sup_image.
intros.
unfold In in H3.
pose (H2 x H3).
tauto.
Qed.*)
Admitted.

(*Service curve of the combined system*)
Theorem combined_service `(S: Server s) `(ls : LengthSequence l) `(Beta: NonDecreasingPositive beta): is_minimal_service S Beta -> is_minimal_service (CombinedSystem S ls) (NonDecrFPlus (non_decr_plus non_decr (-INR (lmax ls)))).
intros.
apply minimal_service_plus.
intros.
unfold is_minimal_service in H.
unfold combined_system in H0.
unfold server_concat in H0.
destruct H0.
destruct H0.
pose (finite_server_t (Packetizer ls) x d t H1 H2) as u.
unfold packetizer_serv in H2.
destruct H2 as [H2 H3].
pose (Rbar_dec (x t)).
unfold packetizer in H3.
case o.
intros.
pose (equal_f H3 t).
simpl in e.
rewrite H4 in e.
unfold packetization in e.
rewrite e.
induction (conv a (fun t0 : R => Rbar_plus (beta t0) (-INR (lmax ls))) t).
simpl.
tauto.
simpl.
tauto.
simpl.
tauto.
intros.
pose (packetizer_cumul H2 l ls).
case H4.
destruct H2.
destruct non_decr_pos.
destruct positive.
pose (pos_to_pos t H1).
intros.
rewrite H2 in r.
case r.
intros.
pose (u H5) as u'.
unfold is_finite in H5.
pose (equal_f H3 t).
simpl in e.
rewrite <- H5 in e.
pose (packetization_bounds l ls (x t)).
rewrite <- e in a0.
destruct H2.
destruct S.
destruct (subset_c_c a x H0) as [yo1 yo2].
destruct yo1.
pose (ConvNonDecr non_decr_pos0 Beta).
destruct n.
destruct positive.
pose (pos_to_pos t H1) as j.
destruct non_decr_pos.
destruct positive.
pose (pos_to_pos0 t H1).
rewrite <- H5 in r.
simpl in r.
apply Rle_ge in r.
destruct (a0 r).
pose (H a x t H0 H1).
rewrite <- H5 in r0.
destruct Beta.
destruct non_decr_pos0.
pose (convolution_plus (- INR(lmax ls)) positive0 positive t H1).
rewrite <- e0.
assert (is_finite(conv a beta t)).
case (Rbar_dec (conv a beta t)).
intros.
rewrite H7 in r0.
case r0.
intros.
case H7.
intros.
rewrite H8 in j.
case j.
tauto.
unfold is_finite in H7, u'.
rewrite <- H7 in r0.
simpl in r0.
rewrite <- H7.
rewrite <- u'.
simpl.
apply (Rplus_le_compat_r (- INR(lmax ls)) _ _ ) in r0.
pose (Rle_lt_trans _ _ _ r0 H2).
rewrite Rplus_comm.
apply Rlt_le in r1.
tauto.
Qed.

(* The delay of the combined system is equal to the delay of the bit by bit system*)
Theorem combined_delay `(S: Server s) `(ls: LengthSequence l) : forall a d d' (p: packetized ls a), s a d -> (combined_system S ls) d d' -> delay a d = delay a d'.
Admitted.


