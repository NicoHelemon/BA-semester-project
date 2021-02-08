(** This sections introduces definitions and theorems about sequences and more specifically natural sequences*)

From Coq Require Import Reals Setoid Image Decidable PeanoNat Plus ClassicalDescription.
Require Import FunImage Definitions RbarComp SetTheory.
From Coquelicot Require Import Rbar.

(** * Generic sequences*)
Section Generic.

Context {T: Type}.

(** ** Non decreasing sequences*)

(*Definition of increasing sequence*)
Definition seq_increasing (ord_le : relation T) (po: order T ord_le) (s: nat -> T): Prop := forall n: nat, ord_le (s n) (s (S n)).

Definition seq_increasing_2 (ord_le : relation T) (po: order T ord_le) (s: nat -> T): Prop := forall n n': nat, le n n' -> ord_le (s n) (s n').

(*If a sequence is increasing then s(n) < s(n') implies n < n'*)
Theorem seq_increasing_imp (ord_le : relation T) (po: order T ord_le) (s: nat -> T) : 
 seq_increasing_2 ord_le po s -> (forall n n', ord_le (s n) (s n') -> s n <> s n' -> lt n n').
intros.
unfold seq_increasing_2 in H.
apply not_not.
unfold decidable.
tauto.
intro p.
apply not_lt in p.
unfold ge in p.
pose (H n' n p).
destruct po.
unfold antisymmetric in ord_antisym.
pose (ord_antisym (s n) (s n') H0 o).
tauto.
Qed.

(*Those two definitions are equivalent*)
Theorem seq_increasing_eq :forall ord_le po s, seq_increasing ord_le po s <-> seq_increasing_2 ord_le po s.
intros.
destruct po.
unfold reflexive in ord_refl.
unfold transitive in ord_trans.
unfold seq_increasing, seq_increasing_2.
split.
intros.
induction n'.
induction n.
apply (ord_refl (s 0%nat)).
apply -> (Nat.le_succ_l n 0) in H0.
pose (lt_not_le _ _ H0).
case (n0 (le_0_n n)).
case (le_dec n n').
intros.
apply (ord_trans _ _ _ (IHn' l) (H n')).
intros.
apply not_le in n0.
unfold gt in n0.
apply <- (Nat.le_succ_l) in n0.
pose (le_antisym n (S n') H0 n0).
rewrite e.
apply (ord_refl).
intros.
apply (H n (S n)).
apply (Nat.le_succ_r).
pose (le_refl n).
tauto.
Qed.


(** ** Sequence image*)
(*Definition of the image of a sequence*)
Definition im_seq (s: nat -> T) := Im nat T universe s.

(*The image of a sequence is never empty*)
Theorem im_seq_non_empty (s: nat -> T) : im_seq s <> Empty_set T.
apply non_empty.
exists (s O).
unfold im_seq.
pose (Im_intro nat T universe s O).
apply i.
unfold In.
unfold universe.
tauto.
tauto.
Qed.

(** ** Sequence maximum and minimum*)

(*Definitions of a bounded sequence*)
Definition seq_bounded_above (ord_le: relation T) (po: order T ord_le) (s: nat -> T) :=
set_bounded_above (im_seq s) ord_le po.

Definition seq_bounded_below (ord_le: relation T) (po: order T ord_le) (s: nat -> T) :=
set_bounded_below (im_seq s) ord_le po.

(*Checks if the sequence has a maximum*)
Definition seq_ex_max (ord_le: relation T) (po: order T ord_le) (s: nat -> T) :=
set_ex_maximum (im_seq s) ord_le po.

(*Finds the maximum of a sequence*)
Definition seq_max (ord_le: relation T) (po: order T ord_le) (s: nat -> T) (ex: seq_ex_max ord_le po s):=
set_maximum (im_seq s) ord_le po ex.

(** ** Special sequences*)

(*Definition of the partial sum of a sequence*)
Fixpoint partial_sum (op: T -> T -> T) (s: nat -> T)(n: nat): T := 
match n with
| O => s O
| S n' => op (partial_sum op s n') (s (S n'))
end.

(*Definition of a "list" ie a sequence with all the terms equals to 0 after a given n*)
Definition seq_is_list (z: T) (s: nat -> T) :=
exists n0, forall n, le n0 n -> s n = z. 

End Generic.


(** * Natural sequences*)

Section MinMax.

(*The image of a natural sequence is never empty*)
Definition nat_im_not_empty (s: nat -> nat): im_seq s <> Empty_set nat := (proj1 (image_non_empty universe s )) n_non_empty.

Definition nat_seq_ex_max (s: nat -> nat) := seq_ex_max le le_order s.

(* If a natural sequence is bounded above then it has a maximum*)
Theorem nat_seq_ex_max_bounded (s: nat -> nat) : seq_bounded_above le le_order s -> nat_seq_ex_max s.
unfold seq_bounded_above.
intros.
unfold nat_seq_ex_max.
unfold seq_ex_max.
pose (ex_nat_max (im_seq s)).
unfold nat_bounded in s0.
apply (s0 H (im_seq_non_empty s)).
Qed.

(*Maximum of a natural sequence*)
Definition nat_seq_max (s: nat -> nat) (ex: seq_ex_max le le_order s): nat := seq_max le le_order s ex.

End MinMax.

(*Definition of a sequence that is always greater than 0 except for n = 0*)
Definition strict_pos (l: nat -> nat) := forall n, lt O n -> lt O (l n).

(** ** Natural sequences limit*)

Section NatLimit.

(*Checks if l is the limit of s*)
Definition nat_seq_is_lim (s: nat -> nat) (l: nat) := exists n0, forall n, le n0 n -> s n = l.

(*Definition of convergence*)
Definition nat_seq_conver (s: nat -> nat) := {l: nat | nat_seq_is_lim s l}.

(*Definition of limit*)
Definition nat_seq_lim (s: nat -> nat) (conv: nat_seq_conver s) := proj1_sig (conv).

(*The limit of a sequence is unique*)
Theorem nat_seq_lim_unique (s: nat -> nat) (conv: nat_seq_conver s): forall l, nat_seq_is_lim s l -> nat_seq_lim s conv = l.
Admitted.

(*The limit of a sequence is the limit of s*)
Theorem nat_seq_lim_is_lim (s: nat -> nat) (conv: nat_seq_conver s): nat_seq_is_lim s (nat_seq_lim s conv).
Admitted.

(*If a sequence converges then it is bounded above*)
Theorem nat_seq_conver_bound (s: nat -> nat): nat_seq_conver s -> seq_bounded_above le le_order s.
Admitted.

(*If a sequence is increasing than its limit is the maximum*)                      
Theorem nat_seq_lim_incr : forall s (conv: nat_seq_conver s), seq_increasing le le_order s ->  (forall n, le (s n) (nat_seq_lim s conv)).
Proof.
intros.
assert (forall l, nat_seq_is_lim s l -> le (s n) l).
intros.
unfold nat_seq_is_lim in H0.
destruct H0.
pose (H0 n).
induction (le_dec x n).
pose (e a).
rewrite e0.
apply le_refl.
apply not_le in b.
unfold gt in b.
apply seq_increasing_eq in H.
unfold seq_increasing_2 in H.
pose (H n x (Nat.lt_le_incl _ _ b)).
pose (H0 x (le_refl x)).
rewrite e0 in l0.
tauto.
pose (nat_seq_lim_is_lim s conv).
apply (H0 (nat_seq_lim s conv) n0).
Qed.

End NatLimit.

(** ** Increasing natural sequences*)

(*Definitions of a strictly increasing sequence*)
Definition nat_seq_strict_incr (s: nat -> nat) := forall n, lt (s n) (s (S n)).

Definition nat_seq_strict_incr_2 (s: nat -> nat) := forall n n', lt n n' -> lt (s n) (s n').

(*Those two definitions are equivalent*)
Theorem nat_seq_strict_incr_eq :forall s, nat_seq_strict_incr s <-> nat_seq_strict_incr_2 s.
intros.
unfold nat_seq_strict_incr, nat_seq_strict_incr_2.
split.
intros.
induction n'.
induction n.
intuition.
intuition.
case (lt_dec n n').
intros.
apply (lt_trans _ _ _ (IHn' l) (H n')).
intros.
apply not_lt in n0.
apply (Nat.lt_succ_r n n') in H0.
pose (le_antisym n n' H0 n0).
rewrite e.
apply H.
intros.
apply (H n (S n)).
apply (Nat.le_succ_r).
pose (le_refl n).
tauto.
Qed.

(*If a sequence is strictly increasing then s(n) <= s(n') implies n <= n'*)
Theorem nat_seq_strict_incr_imp : forall s, nat_seq_strict_incr_2 s -> (forall n n', le (s n) (s n') -> le n n').
intros.
unfold seq_increasing_2 in H.
apply not_not.
unfold decidable.
tauto.
intro p.
apply not_le in p.
unfold gt in p.
pose (H n' n p).
apply (lt_not_le) in l.
tauto.
Qed.

(** ** Natural partial sums*)

(*Partial sum of a natural sequence*)
Definition nat_sum s n : nat := partial_sum plus s n.

(*The partial sum of a natural sequence is increasing*)
Theorem nat_sum_incr : forall l, seq_increasing le le_order (nat_sum l).
Proof.
unfold seq_increasing.
unfold nat_sum.
intros.
intros.
simpl.
apply le_plus_l.
Qed.



(*The partial sum of a sequence of lengths is strictly increasing*)
Theorem nat_sum_length_strict_incr : forall l, l O = O -> strict_pos l -> nat_seq_strict_incr (nat_sum l).
Proof.
intros.
unfold nat_seq_strict_incr.
intros.
unfold nat_sum.
simpl.
apply INR_lt.
rewrite plus_INR.
rewrite <- (Rplus_0_r) at 1.
apply Rplus_lt_compat_l.
fold (INR 0).
apply lt_INR.
apply H0.
apply Nat.lt_succ_r.
apply le_0_n.
Qed.

Theorem nat_sum_length_0 : forall l n, l O = O -> strict_pos l -> nat_sum l n = O -> n = O.
intros.
induction n.
tauto.
unfold nat_sum in H1.
simpl in H1.
fold (nat_sum l n) in H1.
pose (le_0_n (l (S n))).
pose (le_0_n (nat_sum l n)).
rewrite <- H1 in l0, l1.
apply le_INR in l0.
apply le_INR in l1.
rewrite plus_INR in l0, l1.
rewrite <- Rplus_0_l in l0.
rewrite <- Rplus_0_r in l1.
apply Rplus_le_reg_r in l0.
apply Rplus_le_reg_l in l1.
fold (INR O) in l0, l1.
apply INR_le in l0.
apply INR_le in l1.
pose (le_0_n (l (S n))).
pose (le_0_n (nat_sum l n)).
pose (le_antisym _ _ l0 l3).
pose (le_antisym _ _ l1 l2).
pose (IHn e).
unfold strict_pos in H0.
assert (lt 0 (S n)).
apply Nat.lt_succ_r.
apply le_0_n.
pose (H0 (S n) H2).
rewrite <- e0 in l4.
intuition.
Qed.

Search ((_ <> _)%nat -> lt _ _).

(*If a sequence is a list then its partial sum converges*)
Theorem nat_sum_conver: forall (l: nat -> nat), seq_is_list O l -> nat_seq_conver (nat_sum l).
Admitted.

(*If the partial sum of a natural sequence converges than the sequence is a list*)
Theorem nat_sum_conver_rec: forall (l: nat -> nat), nat_seq_conver (nat_sum l) -> seq_is_list O l.
Admitted.

(*The partial sequence of a natural sequence is bounded iff the sequence is a list*)
Theorem nat_sum_unbounded : forall (l: nat -> nat), (seq_is_list O l <-> seq_bounded_above le le_order (nat_sum l)).
Proof.
(*intros.
unfold seq_unbounded_high.
unfold seq_is_list.
unfold nat_sum.
split.
intros.
intro p.
destruct H as [n0].
pose (p (S (nat_sum l n0))).
destruct e.
assert((nat_sum l n0 < S (nat_sum l n0))%nat).
apply (Nat.lt_succ_r (nat_sum l n0) (nat_sum l n0)).
apply (le_refl).
pose (lt_le_trans _ _ _ H1 H0).
assert(forall n, le (nat_sum l n) (nat_sum l n0)).
intros.
pose (le_dec n0 n).
case s.
intros.
unfold nat_sum.
induction n.
simpl.
pose (le_0_n n0).
pose (nat_sum_incr l).
apply (seq_increasing_eq) in s0.
unfold seq_increasing_2 in s0.
pose (s0 0%nat n0 l2).
unfold nat_sum in l3.
simpl in l3.
tauto.
apply le_order.
simpl in IHn.
simpl.*)
Admitted.