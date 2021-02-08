(** This section contiains theorems and definitions of set theory, it includes
- Conversions between different types of subsets
- Bounds, minima and maxima
- Real and natural subsets*)

Require Import Ensembles Reals Image Reals Setoid Image Decidable PeanoNat Plus ClassicalDescription.
From Coquelicot Require Import Rbar.

(** * Empty set*)

Section Empty.

(* Equivalent definition of an empty set*)
Theorem is_empty {U: Type}: forall S, (forall x, ~ S x) <-> S = Empty_set U.
intros.
pose (Noone_in_empty U).
split.
intros.
apply Extensionality_Ensembles.
unfold Same_set.
unfold Included.
split.
intros.
case (H x H0).
intros.
case (n x H0).
intros.
rewrite <- H in n.
apply (n x).
Qed.

(* Equivalent definition of a set that is non empty*)
Theorem non_empty {U: Type}: forall S, (exists n,  S n) <-> S <> Empty_set U.
intros.
pose (is_empty S).
destruct i.
split.
intros p p2.
case (all_not_not_ex _ _ (H0 p2) p).
intros.
assert (~(forall x: U, ~ S x)).
intro p.
case (H1 (H p)).
apply not_all_not_ex in H2.
tauto.
Qed.

End Empty.

(** * Generic sets*)

Section Generic.


Context {T: Type}.

(*Definition of the universal set*)
Definition universe : Ensemble T := (fun e : T => True).

(* Two ways of representing a set are equivalent*)
Theorem set_eq {U: Type} : forall (S : Ensemble U), (fun x: U => S x) = S.
tauto.
Qed.

(** ** Set minima and extrema*)

(* Definition of an upper bound*)
Definition set_is_bound_above (S: Ensemble T) (ord_le: relation T) (po: order T ord_le) (b: T) :=
forall s, S s -> ord_le s b.

(* Definition of a set bounded above*)
Definition set_bounded_above (S: Ensemble T) (ord_le: relation T) (po: order T ord_le) :=
exists b, set_is_bound_above S ord_le po b.

(*Definition of a lower bound*)
Definition set_is_bound_below (S: Ensemble T) (ord_le: relation T) (po: order T ord_le) (b: T) :=
forall s, S s -> ord_le b s.

(*Definition of a set bounded below*)
Definition set_bounded_below (S: Ensemble T) (ord_le: relation T) (po: order T ord_le) :=
exists b, set_is_bound_below S ord_le po b.

(*Definition of the minimum*)
Definition set_is_minimum (S: Ensemble T) (ord_le: relation T) (po: order T ord_le) (s: T) :=
S s /\ forall s': T, S s' -> ord_le s s'.

(*Definition of the existence of the minimum*)
Definition set_ex_minimum (S: Ensemble T) (ord_le: relation T) (po: order T ord_le) :=
{m : T | set_is_minimum S ord_le po m}.

(*If an element of a set is the minumum, then the set has a minimum*)
Theorem set_is_minimum_ex (S: Ensemble T) (ord_le: relation T) (po: order T ord_le) (s: T):
set_is_minimum S ord_le po s -> set_ex_minimum S ord_le po.
intros.
exists s.
tauto.
Qed.

(*Gives the minimum of the set*)
Definition set_minimum (S: Ensemble T) (ord_le: relation T) (po: order T ord_le) (ex: set_ex_minimum S ord_le po) :=
proj1_sig(ex).

(*The minimum of a set is unique*)
Theorem set_minimum_unique (S: Ensemble T) (ord_le: relation T) (po: order T ord_le) (s: T) :
forall (p: set_is_minimum S ord_le po s), set_minimum S ord_le po (set_is_minimum_ex S ord_le po s p) = s.
Proof.
intros.
unfold set_minimum.
induction (set_is_minimum_ex S ord_le po s p).
simpl.
unfold set_is_minimum in p.
unfold set_is_minimum in p0.
destruct p.
destruct p0.
pose (H0 x H1).
pose (H2 s H).
destruct po.
unfold antisymmetric in ord_antisym.
pose (ord_antisym x s o0 o).
tauto.
Qed.

(*The minimum of the set is a minimum of the set*)
Theorem set_minimum_is_minimum (S: Ensemble T) (ord_le: relation T) (po: order T ord_le) (ex: set_ex_minimum S ord_le po) :
set_is_minimum S ord_le po (set_minimum S ord_le po ex).
unfold set_minimum.
induction ex.
simpl.
tauto.
Qed.

(*If one set is included in an other one that the greater set as a smaller minimum than the other one*)
Theorem set_minimum_included : forall (A B: Ensemble T) (ord_le: relation T) (po: order T ord_le) (exA: set_ex_minimum A ord_le po) (exB: set_ex_minimum B ord_le po),
Included T A B -> ord_le (set_minimum B ord_le po exB) (set_minimum A ord_le po exA).
intros.
assert (forall n0 n1, set_is_minimum B ord_le po n0 -> set_is_minimum A ord_le po n1 -> ord_le n0 n1).
unfold set_is_minimum.
intros.
destruct H0.
destruct H1.
unfold Included in H.
pose (H n1 H1).
unfold In in i.
apply (H2 n1 i).
pose (set_minimum_is_minimum A ord_le po exA).
pose (set_minimum_is_minimum B ord_le po exB).
apply (H0 (set_minimum B ord_le po exB) (set_minimum A ord_le po exA) s0 s).
Qed.

(*Definition of the maximum*)
Definition set_is_maximum (S: Ensemble T) (ord_le: relation T) (po: order T ord_le) (s: T) :=
S s /\ forall s': T, S s' -> ord_le s' s.

(*Definition of the existence of the maximum*)
Definition set_ex_maximum (S: Ensemble T) (ord_le: relation T) (po: order T ord_le) :=
{m : T | set_is_maximum S ord_le po m}.

(*If an element of a set is the maximum, then the set has a maximum*)
Theorem set_is_maximum_ex (S: Ensemble T) (ord_le: relation T) (po: order T ord_le) (s: T) :
set_is_maximum S ord_le po s -> set_ex_maximum S ord_le po.
intros.
exists s.
tauto.
Qed.

(*Gives the maximum of the set*)
Definition set_maximum (S: Ensemble T) (ord_le: relation T) (po: order T ord_le) (ex: set_ex_maximum S ord_le po) :=
proj1_sig(ex).

(*The maximum of a set is unique*)
Theorem set_maximum_unique (S: Ensemble T) (ord_le: relation T) (po: order T ord_le) (p: set_ex_maximum S ord_le po) (s: T) :
set_is_maximum S ord_le po s -> set_maximum S ord_le po p = s.
Proof.
intros.
pose p as l.
unfold set_ex_maximum in p.
destruct p.
unfold set_is_maximum in s0, H.
destruct s0, H.
pose (o s H).
pose (H0 x s0).
destruct po.
unfold antisymmetric in ord_antisym.
pose (ord_antisym s x o0 o1).
rewrite e.
unfold set_maximum.
simpl.
auto.
Qed.

(*The minimum of the set is a minimum of the set*)
Theorem set_maximum_is_maximum (S: Ensemble T) (ord_le: relation T) (po: order T ord_le) (ex: set_ex_maximum S ord_le po) :
set_is_maximum S ord_le po (set_maximum S ord_le po ex).
unfold set_maximum.
induction ex.
simpl.
tauto.
Qed.

(*If one set is included in an other one that the greater set as a greater maximum than the other one*)
Theorem set_maximum_included : forall (A B: Ensemble T) (ord_le: relation T) (po: order T ord_le) (exA: set_ex_maximum A ord_le po) (exB: set_ex_maximum B ord_le po),
Included T A B -> ord_le (set_maximum A ord_le po exA) (set_maximum B ord_le po exB).
intros.
assert (forall n0 n1, set_is_maximum A ord_le po n0 -> set_is_maximum B ord_le po n1 -> ord_le n0 n1).
unfold set_is_maximum.
intros.
destruct H0.
destruct H1.
unfold Included in H.
pose (H n0 H0).
unfold In in i.
apply (H3 n0 i).
pose (set_maximum_is_maximum A ord_le po exA).
pose (set_maximum_is_maximum B ord_le po exB).
apply (H0 (set_maximum A ord_le po exA) (set_maximum B ord_le po exB) s s0).
Qed.

(*If all the elemements of a set are smaller than a given value, then its maximum will also be smaller than this value*)
Theorem set_ge_maximum : forall (b: T) (S: Ensemble T) (ord_le: relation T) (po: order T ord_le) (ex: set_ex_maximum S ord_le po),
((forall s : T, S s -> ord_le s b) <-> ord_le (set_maximum S ord_le po ex) b).
intros.
assert(forall m, set_is_maximum S ord_le po m -> ((forall s, S s -> ord_le s b) <-> ord_le m b)).
intros.
unfold set_is_maximum in H.
destruct H.
split.
intros.
apply (H1 m H).
intros.
pose (H0 s H2).
destruct po.
unfold transitive in ord_trans.
apply (ord_trans _ _ _ o H1).
apply (H (set_maximum S ord_le po ex) (set_maximum_is_maximum S ord_le po ex)).
Qed.

(*The maximum always belongs to the set*)
Theorem set_maximum_in : forall (S: Ensemble T) (ord_le: relation T) (po: order T ord_le) (ex: set_ex_maximum S ord_le po),
S (set_maximum S ord_le po ex).
intros.
pose (set_maximum_is_maximum S ord_le po ex).
unfold set_is_maximum in s.
destruct s.
tauto.
Qed.

End Generic.

(** * Natural Numbers*)

Section NSets.


(* <= is a total order for natural numbers*)
Theorem le_order : order nat le.
split.
unfold reflexive.
apply le_refl.
unfold transitive.
apply le_trans.
unfold antisymmetric.
apply le_antisym.
Qed.

(* Well ordering principle*)
Axiom wop : forall (N: Ensemble nat), N <> Empty_set nat -> set_ex_minimum N le le_order.

(*Minimum of a natural set*)
Definition nat_min (N: Ensemble nat) (ne: N <> Empty_set nat) := set_minimum N le le_order (wop N ne).

Definition nat_bounded (N: Ensemble nat): Prop := set_bounded_above N le le_order.

(* A bounded non empty set has always a maximum *)
Theorem ex_nat_max : forall N, nat_bounded N -> N <> Empty_set nat -> set_ex_maximum N le le_order.
intros.
assert(exists x, set_is_maximum N le le_order x).
apply not_not.
unfold decidable.
tauto.
intro p.
pose (not_ex_all_not nat _ p).
unfold set_is_maximum in n.
assert (forall n : nat, ~N n \/ (exists s' : nat, N s' /\ (n < s')%nat)).
intros.
pose (n n0).
apply not_and in n1.
case n1.
intros.
tauto.
intros.
apply not_all_ex_not in H1.
destruct H1.
apply not_imp in H1.
destruct H1.
apply not_le in H2.
unfold gt in H2.
pose (conj H1 H2).
pose (ex_intro (fun n => N n /\ (n0 < n)%nat) x a).
tauto.
unfold decidable.
tauto.
unfold decidable.
tauto.
Admitted.


(* Maximum for natural numbers*)
Definition nat_max (N: Ensemble nat) (b: nat_bounded N) (ne: N <> Empty_set nat) : nat := set_maximum N le le_order (ex_nat_max N b ne).

(*N is not empty*)
Theorem n_non_empty : universe <> Empty_set nat.
apply non_empty.
exists O.
unfold universe.
exact I.
Qed.

End NSets.

(** ** Real Numbers*)

Section RSets.

(* <= is a total order for real numbers*)
Theorem Rle_order: order R Rle.
split.
unfold reflexive.
apply Rle_refl.
unfold transitive.
apply Rle_trans.
unfold antisymmetric.
apply Rle_antisym.
Qed.

(* <= is a total order for Rbar*)
Theorem Rbar_le_order: order Rbar Rbar_le.
split.
unfold reflexive.
apply Rbar_le_refl.
unfold transitive.
apply Rbar_le_trans.
unfold antisymmetric.
apply Rbar_le_antisym.
Qed.

Definition R_bounded (S: Ensemble R): Prop := set_bounded_above S Rle Rle_order.

(* This is not correct, this should be removed and cumul_below and packet_below shoud be natural sets instead*)
Theorem ex_R_max: forall S, R_bounded S -> S <> Empty_set R -> set_ex_maximum S Rle Rle_order.
Admitted.

Definition R_max (S: Ensemble R) (b: R_bounded S) (ne: S <> Empty_set R) : R := set_maximum S Rle Rle_order (ex_R_max S b ne).



(** ** Intervals*)

(* ]a, b] u {a} = [a, b]*)
Lemma set_f_t_plus_f : forall from to : R, (from <= to)%R -> Add R (fun x: R => (x > from)%R /\ (x <= to)%R) from = (fun x => (x >= from)%R /\ (x <= to)%R).
  intros.
  apply Extensionality_Ensembles.
  unfold Add.
  unfold Same_set.
  unfold Included.
  split.
  intros.
  Check Union_intror.
  apply Union_inv in H0.
  case H0.
  unfold In.
  intros.
  intuition.
  intros.
  apply Singleton_inv in H1.
  rewrite <- H1.
  unfold In.
  intuition.
  intros.
  pose (Req_dec x from).
  case o.
  intros.
  apply Union_intror.
  apply Singleton_intro.
  auto.
  intros.
  apply Union_introl.
  unfold In in H0.
  unfold In.
  split.
  destruct H0.
  apply Rnot_ge_gt.
  unfold not.
  intros.
  pose (conj H0 H3).
  pose (Rge_ge_eq x from).
  tauto.
  intuition.
  Qed.
  
  (* [a, b[ u {b} = [a, b]*)
  Lemma set_f_t_plus_t : forall from to :R, (from <= to)%R -> Add R (fun x: R => (x >= from)%R /\ (x < to)%R) to = (fun x => (x >= from)%R /\ (x <= to)%R).
  intros.
  apply Extensionality_Ensembles.
  unfold Add.
  unfold Same_set.
  unfold Included.
  split.
  intros.
  Check Union_intror.
  apply Union_inv in H0.
  case H0.
  unfold In.
  intros.
  intuition.
  intros.
  apply Singleton_inv in H1.
  rewrite <- H1.
  unfold In.
  intuition.
  intros.
  pose (Req_dec x to).
  case o.
  intros.
  apply Union_intror.
  apply Singleton_intro.
  auto.
  intros.
  apply Union_introl.
  unfold In in H0.
  unfold In.
  intuition.
  apply Rnot_le_gt.
  unfold not.
  intros.
  pose (conj H4 H3).
  pose (Rle_le_eq x to).
  tauto.
  Qed.

End RSets.


(** * Conversions and set operations*)

(** ** Opposite*)

(* Opposite of a real set*)
Definition set_opp (S: Ensemble R): Ensemble R := (fun x => S (-x)%R).

(*The opposite of the opposite of a set is the original set*)
Theorem set_opp_involutive: forall S, set_opp (set_opp S) = S.
intros.
unfold set_opp.
apply Extensionality_Ensembles.
unfold Same_set.
unfold Included.
unfold In.
split.
intros.
rewrite Ropp_involutive in H.
tauto.
intros.
rewrite Ropp_involutive.
tauto.
Qed.

(*If a set is non empty then its opposite will neither be empty*)
Theorem set_opp_non_empty: forall S, S <> Empty_set R <-> set_opp S <> Empty_set R.
intros.
unfold set_opp.
split.
intros.
apply non_empty in H.
apply non_empty.
destruct H.
exists ((-x)%R).
rewrite Ropp_involutive.
tauto.
intros.
apply non_empty.
apply non_empty in H.
destruct H.
exists ((-x)%R).
tauto.
Qed.

(* Opposite of a subset of Rbar*)
Definition set_opp_Rbar (S: Ensemble Rbar): Ensemble Rbar := (fun x => S (Rbar_opp x)).

(*The opposite of the opposite of a set is the original set*)
Theorem set_opp_Rbar_involutive: forall S, set_opp_Rbar (set_opp_Rbar S) = S.
intros.
unfold set_opp_Rbar.
apply Extensionality_Ensembles.
unfold Same_set.
unfold Included.
unfold In.
split.
intros.
rewrite Rbar_opp_involutive in H.
tauto.
intros.
rewrite Rbar_opp_involutive.
tauto.
Qed.

(*If a set is non empty then its opposite will neither be empty*)
Theorem set_opp_Rbar_non_empty: forall S, S <> Empty_set Rbar <-> set_opp_Rbar S <> Empty_set Rbar.
intros.
unfold set_opp_Rbar.
split.
intros.
apply non_empty in H.
apply non_empty.
destruct H.
exists (Rbar_opp x).
rewrite Rbar_opp_involutive.
tauto.
intros.
apply non_empty.
apply non_empty in H.
destruct H.
exists (Rbar_opp x).
tauto.
Qed.

(** ** N to R*)
Section NtoRSets.

(* Converts a natural set into a real one*)
Definition set_nat_to_r (N: Ensemble nat) := fun r => exists n, N n /\ r = INR n.

End NtoRSets.

(** ** R to Rbar*)

Section RToRbar.

(* Converts a subset of R into a subset of Rbar *) 
Definition set_R_to_Rbar (S: Ensemble R): Ensemble Rbar := (fun x: Rbar => is_finite(x) /\ S x).

(* Doing the opposite first and the conversion then or doing the opposite are equivalent*)
Theorem set_opp_R_Rbar : forall S: Ensemble R, set_opp_Rbar (set_R_to_Rbar S) = set_R_to_Rbar (set_opp S).
intros.
unfold set_opp, set_opp_Rbar, set_R_to_Rbar.
apply Extensionality_Ensembles.
unfold Same_set.
unfold Included.
unfold In.
split.
intros.
destruct H.
split.
unfold is_finite in H.
apply Rbar_opp_eq in H.
rewrite Rbar_opp_involutive in H.
rewrite Rbar_opp_real in H.
simpl in H.
rewrite Ropp_involutive in H.
unfold is_finite.
tauto.
unfold is_finite in H.
rewrite <- H in H0.
rewrite Rbar_opp_real in H0.
tauto.
intros.
destruct H.
split.
unfold is_finite.
unfold is_finite in H.
rewrite <- H.
tauto.
unfold is_finite in H.
rewrite <- H.
tauto.
Qed.

(*An empty subset of R will also be an empty subset of Rbar*)
Theorem set_R_to_Rbar_empty : forall S, S = Empty_set R <-> set_R_to_Rbar S = Empty_set Rbar.
intros.
split.
intros.
setoid_rewrite <- (is_empty S) in H.
apply is_empty.
unfold set_R_to_Rbar.
intros x p.
destruct p.
case (H x H1).
intros.
apply is_empty.
setoid_rewrite <- (is_empty) in H.
intros x p.
unfold set_R_to_Rbar in H.
assert (is_finite x).
unfold is_finite.
tauto.
case (H x (conj H0 p)).
Qed.

End RToRbar.  