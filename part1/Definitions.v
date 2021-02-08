(** This section introduces:
  - Dioids
  - Non decreasing, finite and continuous functions
  - ReLU operation
  - Convolution, deconvolution, minimum and maximum between functions
  - Delta function
  - Subadditive closure
  - Server and server concatenation

*)

Require Import Reals FunImage Image RbarComp InfSup SetTheory FunctionalExtensionality Decidable.
From Coquelicot Require Import Rbar.
From Coquelicot Require Import Compactness Lim_seq Rcomplements Hierarchy Lub.


(** * Dioids*)
Section Dioids.

(* Definition of a diod*)
Class Dioid {A: Type}(plus : A -> A -> A)(mult : A -> A -> A)(zero : A)(one : A) : Prop := {
plus_assoc : forall x y z, plus x (plus y z) = plus (plus x y) z;
mult_assoc : forall x y z, mult x (mult y z) = mult (mult x y) z;
plus_com : forall x y, plus x y = plus y x;
plus_neutral : forall x, plus zero x = x;
mult_neutral_l : forall x, mult one x = x;
mult_neutral_r : forall x, mult x one = x;
mult_abs_l : forall x, mult zero x = zero;
mult_abs_r : forall x, mult x zero = zero;
distrib_l : forall x y z, mult x (plus y z) = plus (mult x y) (mult x z);
distrib_r : forall x y z, mult (plus x y) z = plus (mult x z) (mult y z);
idempotent: forall x, plus x x = x
}.

End Dioids.

(** * Functions*)
Section FunctionSets.

Generalizable Variables p.

(** ** Non decreasing functions*)

(* Definitions of a non-decreasing function*)
Definition non_decreasing (f: R -> Rbar) := forall s t, (s >= 0 /\ t >= 0) -> (s < t -> Rbar_le (f(s)) (f(t))).
Definition non_decreasing_2 (f: R -> Rbar) := forall s t, (s >= 0 /\ t >= 0) -> (s <= t -> Rbar_le (f(s)) (f(t))).

(*The two definitions are equivalent*)
Theorem non_decr_eq : forall f, non_decreasing f <-> non_decreasing_2 f.
intros.
unfold non_decreasing.
unfold non_decreasing_2.
split.
intros.
pose (H s t H0).
unfold Rle in H1.
case H1.
intros.
apply (r H2).
intros.
rewrite H2.
apply Rbar_le_refl.
intros.
pose (H s t H0).
apply Rlt_le in H1.
apply (r H1).
Qed.

(*Exists distributes on logical or*)
Lemma ex_or_distrib {T: Type} : forall (P P' : T -> Prop), (exists s : T, (P s \/ P' s)) <-> (exists s : T, P s) \/ (exists s : T, P' s).
split.
intros.
destruct H.
case H.
intros.
apply or_introl.
exists x.
tauto.
intros.
apply or_intror.
exists x.
tauto.
intros.
case H.
intros.
destruct H0.
exists x.
tauto.
intros.
destruct H0.
exists x.
tauto.
Qed.

(* Adding a constant to a non decreasing function does not change this property*)
Theorem non_decr_plus `(P: non_decreasing p) (v : R) : non_decreasing (fun t => Rbar_plus (p t) v).
unfold non_decreasing.
unfold non_decreasing in P.
intros.
pose (P s t H H0).
case (Rbar_dec (p s)).
intros.
rewrite H1.
rewrite H1 in r.
case(Rbar_dec (p t)).
intros.
rewrite H2.
simpl.
tauto.
intros.
case H2.
intros.
rewrite H3.
rewrite H3 in r.
case r.
intros.
unfold is_finite in H3.
rewrite <- H3 in r.
case r.
intros.
case H1.
intros.
rewrite H2.
case(Rbar_dec (p t)).
intros.
rewrite H3.
simpl.
tauto.
intros.
case H3.
intros.
rewrite H4.
simpl.
tauto.
intros.
unfold is_finite in H4.
rewrite <- H4.
simpl.
tauto.
intros.
unfold is_finite in H2.
rewrite <- H2.
rewrite <- H2 in r.
case(Rbar_dec (p t)).
intros.
rewrite H3.
rewrite H3 in r.
simpl.
tauto.
intros.
case H3.
intros.
rewrite H4 in r.
case r.
intros.
unfold is_finite in H4.
rewrite <- H4.
rewrite <- H4 in r.
simpl.
apply Rplus_le_compat_r.
tauto.
Qed.

(** Let be f a non decreasing function, then for any a in R, one of the 4 cases can arise:
-   f is always greater than a
-   f is always smaller than a
-   there exists a epsilon such that f is smaller than a before epsilon excluded and greater after epsilon included
-   there exists a epsilon such that f is smaller than a before epsilon included and greater after epsilon excluded

I only have a proof sketch, thus it is admitted*)
Theorem non_decr_split: forall f a, non_decreasing f -> ((forall x, x >= 0 -> Rbar_le (f x) a) \/ (forall x, x >= 0 -> Rbar_le a (f x)) \/ 
(exists eps, forall x, (0 <= x < eps -> Rbar_le (f x) a) /\ (x >= eps -> Rbar_le a (f x))) \/
(exists eps, forall x, (0 <= x <= eps -> Rbar_le (f x) a) /\ (x > eps -> Rbar_le a (f x)))).
(*intros.
pose (non_decr_eq f) as P.
destruct P as [P1 P2].
pose (P1 H) as P'.
unfold non_decreasing in H.
case (Rbar_le_dec (f 0) a).
intros.
case ( classic (exists s, s >= 0 /\ Rbar_le a (f s))).
intros.
apply or_intror.
apply or_intror.
apply ex_or_distrib.
apply not_not.
unfold decidable.
tauto.
intro p.
pose (not_ex_all_not _ _ p).
simpl in n.
assert ( forall n : R,
   ((exists x : R, (0 <= x < n /\ ~Rbar_le (f x) a) \/ (x >= n /\ ~Rbar_le a (f x))) /\
    (exists x : R, (0 <= x <= n /\ ~Rbar_le (f x) a) \/ (x > n /\ ~Rbar_le a (f x))))).
    intros.
pose (n n0).
apply not_or in n1.
destruct n1.
apply not_all_ex_not in H1.
apply not_all_ex_not in H2.
split.
destruct H1.
exists x.
apply not_and in H1.
case H1.
intros.
apply not_imp in H3.
tauto.
apply not_imp in H3.
unfold decidable.
tauto.
unfold decidable.
tauto.
tauto.
unfold decidable.
tauto.
destruct H2.
exists x.
apply not_and in H2.
case H2.
intros.
apply not_imp in H3.
tauto.
apply not_imp in H3.
unfold decidable.
tauto.
unfold decidable.
tauto.
tauto.
unfold decidable.
tauto.
destruct H0.
pose (H1 x).
destruct a0.
destruct H0, H2, H3.
case H2.*)
Admitted.

(** ** Cumulative functions*)

(** *** Definitions*)

(*Function going from R to Rbar that is never equal to -infinity when t >= 0*)
Class NotMInf (f: R -> Rbar) := {
  not_inf: forall x, x >= 0 -> (m_infty) <> (f x)
}.

(*Function going from R to Rbar that is positive when t >= 0*)
Class Positive (f: R -> Rbar) := {
  pos_to_pos : forall x, x >= 0 -> Rbar_le 0 (f x)
}.

(*Function going from R to Rbar that is positive and non decreasing when t >= 0*)
Class NonDecreasingPositive (f: R -> Rbar) := {
  positive :> Positive f;
  non_decr: non_decreasing f
}.

(*Function going from R to Rbar that is cumulative *)
Class Cumulative (f: R -> Rbar) := {
  non_decr_pos :> NonDecreasingPositive f;
  left_cont: forall x, x >= 0 -> filterlim f (at_right x) (Rbar_locally (f x));
  start_0 : f(0) = 0;
}.

(** *** Zero function*)

(*A function always equal to 0*)
Definition zero_f: R -> Rbar := (fun t => 0).

(* The zero function is non decreasing and always positive*)
Global Instance zero_f_non_decr : NonDecreasingPositive(zero_f).
split.
split.
intros.
apply Rbar_le_refl.
unfold non_decreasing.
intros.
apply Rbar_le_refl.
Qed.

(* The zero function is a cumulative function*)
Global Instance zero_f_cumul : Cumulative(zero_f).
unfold zero_f.
split.
apply zero_f_non_decr.
admit.
tauto.
Admitted.

(** *** Theorems*)

(*Adding a positive constant to a non decreasing and positive function does not change those properties*)
Global Instance NonDecrPlus `(P: NonDecreasingPositive p) (v: Rbar) (pos: Rbar_le 0 v) : NonDecreasingPositive (fun t => Rbar_plus (p t) v).
destruct P.
destruct positive0.
split.
split.
intros.
pose (pos_to_pos0 x H).
apply (Rbar_plus_le_pos (p x) v r pos).
unfold non_decreasing.
unfold non_decreasing in non_decr0.
intros.
pose (non_decr0 s t H H0).
apply Rbar_plus_le_r.
tauto.
Qed.


(* a  positive function is always greater than minus infinity*)
Global Instance PosNotMInf `(P: Positive p) : NotMInf p. 
Proof.
split.
intros.
destruct P.
pose (pos_to_pos0 x H).
assert (Rbar_lt m_infty 0).
simpl.
exact I.
pose (Rbar_lt_le_trans _ _ _ H0 r).
apply Rbar_lt_not_eq in r0.
tauto.
Qed.


End FunctionSets.


Section FunctionOperations.
(** ** Continuity and finite functions*)

  (*Definition of a continuous function*)
  Definition continuous (f: R -> Rbar) := forall x: R, x >= 0 -> filterlim f (locally x) (Rbar_locally (f x)).
  
  (*Definition of a finite function (the image of f belongs to R)*)
  Definition is_finite_f (f: R -> Rbar) := forall x: R, x >= 0 -> is_finite (f x).
  
  (*Finite and cumulative function*)
  Definition is_fincumul (f : R -> Rbar) := is_finite_f f /\ Cumulative f.
  
  (*If a function is continuous and an element of the image is real than the whole image is real*)
  Theorem continuous_not_inf : forall (f: R -> Rbar), continuous f -> exists x, is_finite (f x) -> is_finite_f f.
  Admitted. 


(** * Function operations*)
Generalizable Variables p pa pb al fm c d.
(** ** Maximum*)
  
  (** *** Binary maximum*)
  (*Definition of the binary maximum between two elements of Rbar*)
  Definition Rbar_max (a b : Rbar) := Rbar_opp (Rbar_min (Rbar_opp a) (Rbar_opp b)).
  
    
  Theorem Rbar_max_case_strong : forall (r1 r2 : Rbar) (P : Rbar -> Type),
       (Rbar_le r2 r1 -> P r1) ->
       (Rbar_le r1 r2 -> P r2) -> P (Rbar_max r1 r2).
  intros.
  unfold Rbar_max.
  pose (Rbar_min_case_strong (Rbar_opp r1) (Rbar_opp r2) (fun x => P(Rbar_opp x))).
  apply p.
  intros.
  setoid_rewrite Rbar_opp_le in H.
  rewrite Rbar_opp_involutive.
  tauto.
   intros.
  setoid_rewrite Rbar_opp_le in H.
  rewrite Rbar_opp_involutive.
  tauto.
  Qed.
  
  (* The maximum between two numbers is commutative*)
    Theorem Rbar_max_comm (a b : Rbar) : Rbar_max a b = Rbar_max b a.
  unfold Rbar_max.
  apply Rbar_opp_eq.
  apply Rbar_min_comm.
  Qed.
  
  (** *** Maximum between two functions*)
  (* Maximum between two functions*)
  Definition Rbar_max_f (f g: R -> Rbar) := (fun x => Rbar_max (f x) (g x)).
  
  (* The maximum between a non decreasing and positive function and a non decreasing one is also non decreasing and positive*)
  Global Instance NonDecrMax `(P: NonDecreasingPositive p) `(D: non_decreasing d): NonDecreasingPositive (Rbar_max_f p d).
  unfold Rbar_max_f.
  unfold Rbar_max.
  destruct P.
  destruct positive0.
  split.
  split.
  intros.
  pose (pos_to_pos0 x H).
  apply Rbar_opp_le in r.
  simpl in r.
  rewrite Ropp_0 in r.
  apply Rbar_opp_le.
  rewrite Rbar_opp_involutive.
  simpl.
  rewrite Ropp_0.
  apply Rbar_min_case_strong.
  intros.
  tauto.
  intros.
  apply (Rbar_le_trans _ _ _ H0 r).
  unfold non_decreasing.
  intros.
  apply Rbar_opp_le.
  unfold non_decreasing in non_decr0.
  pose (non_decr0 s t H H0).
  apply Rbar_opp_le in r.
  unfold non_decreasing in D.
  pose (D s t H H0).
  apply Rbar_opp_le in r0.
  apply Rbar_min_case_strong.
  apply Rbar_min_case_strong.
  tauto.
  intros.
  apply (Rbar_le_trans _ _ _ H2 r0).
  intros.
  apply Rbar_min_case_strong.
  intros.
  apply (Rbar_le_trans _ _ _ H1 r).
  intros.
  tauto.
  Qed.
  
  (** ** ReLU*)
  (*Set all the negative values of the function to 0*)
  Definition f_plus (f : R -> Rbar) := fun x => Rbar_max 0 (f x).
  
  (* Applying ReLU on a non decreasing function makes it also positive*)
  Global Instance NonDecrFPlus `(P: non_decreasing p) : NonDecreasingPositive (f_plus p).
  intros.
  apply NonDecrMax.
  apply zero_f_non_decr.
  tauto.
  Qed.
  
  (* Applying ReLU on a non decreasing function plus a constant makes it also positive*)
  Global Instance NonDecrFPlusPlus `(P: non_decreasing p) (v: R) : NonDecreasingPositive (f_plus (fun t => Rbar_plus (p t) v)).
  intros.
  apply (NonDecrFPlus).
  apply non_decr_plus.
  tauto.
  Qed.
  
  (* f is always smaller than ReLU(f)*)
  Theorem f_plus_le: forall f t, Rbar_le (f t) (f_plus f t).
  intros.
  unfold f_plus.
  unfold Rbar_max.
  apply Rbar_opp_le.
  rewrite Rbar_opp_involutive.
  apply Rbar_min_case_strong.
  tauto.
  intros.
  apply Rbar_le_refl.
  Qed.
  
  (** ** Convolution *)
  
  Section Convolution.

  (*Definition of the min-plus convolution between two functions*)
  Definition conv (f g : R -> Rbar) := fun t: R => Rbar_glb (Im R Rbar (fun x: R => x >= 0 /\ x <= t) (fun s => Rbar_plus (f (t-s)) (g(s)))).

  
  (*The convolution is commutative*)
  Theorem conv_com : forall f g t, conv f g t = conv g f t.
  Proof.
  intros.
  unfold conv.
  rewrite (image_f_t_shift_flip (fun s: R => (Rbar_plus (f(t -s)) (g s))) 0 t t).
  unfold Rminus at 1 2 3.
  rewrite Rplus_opp_r.
  rewrite Ropp_0.
  rewrite Rplus_0_r.
  rewrite image_t_f_is_f_t.
  rewrite (image_eq_fun_r_rbar (fun x2 : R => x2 <= t /\ x2 >= 0)  (fun s : R => Rbar_plus (f (t + - (t - s))) (g (t - s))) (fun s : R => Rbar_plus (g (t - s)) (f s))).
  auto.
  intros.
  rewrite Ropp_minus_distr.
  unfold Rminus.
  rewrite (Rplus_comm x (-t)).
  rewrite <- Rplus_assoc.
  rewrite Rplus_opp_r.
  rewrite Rplus_0_l.
  rewrite Rbar_plus_comm.
  auto.
  Qed.
  
  (*The convolution  is isotone: f <= f' and g <= g' implies conv f g <= conv f' g'*)
  Theorem conv_isotone : forall f f' g g': R -> Rbar, (forall x, Rbar_le (f x) (f' x)) /\ (forall x, Rbar_le (g x) (g' x)) -> (forall x, Rbar_le (conv f g x) (conv f' g' x)).
  Admitted.
  
  (*The convolution of two positive functions is also positive*)
    Global Instance ConvPos`(Pa: Positive pa)`(Pb: Positive pb): Positive (conv pa pb).
    Proof.
    split.
    intros.
    destruct Pa.
    assert (forall s: R, 0 <= s <= x -> Rbar_le 0 (pa(x - s))).
    intros.
    destruct H0.
    apply (Rplus_le_compat_r (-s) s x) in H1.
    rewrite Rplus_opp_r in H1.
    apply Rle_ge in H1.
    apply (pos_to_pos0 (x - s) H1).
    assert (forall s: R, 0 <= s <= x -> Rbar_le 0 (Rbar_plus (pa(x - s)) (pb(s)))).
    intros.
    pose (H0 s H1).
    destruct Pb.
    pose (pos_to_pos1 s).
    pose H1.
    destruct H1.
    pose (Rle_ge 0 s r1).
    pose (r0 r3).
    pose (H0 s a).
    pose (Rbar_plus_le_pos (pa (x - s)) (pb s) r5 r4).
    tauto.
    unfold conv.
    apply le_inf.
    intros.
    fold (In Rbar (Im R Rbar (fun x0 : R => x0 >= 0 /\ x0 <= x)
       (fun s : R => Rbar_plus (pa (x - s)) (pb s))) x0) in H2.
    apply Im_inv in H2.
    destruct H2.
    destruct H2.
    unfold In in H2.
    destruct H2.
    apply Rge_le in H2.
    pose (conj H2 H4).
    pose (H1 x1 a).
    setoid_rewrite H3 in r.
    tauto.
    Qed.
    
    (*The convolution of two non decreasing positive functions is also non decreasing and positive*)
    Global Instance ConvNonDecr`(Pa: NonDecreasingPositive pa)`(Pb: NonDecreasingPositive pb): NonDecreasingPositive (conv pa pb).
    Admitted.
    
    (*The convolution between 0 and a non decreasing positive function is a constant function equal to f 0*)
    Theorem conv_zero_f `(P: NonDecreasingPositive p) : forall x, x >= 0 -> conv p zero_f x = p 0.
    intros.
    destruct P.
    destruct positive0.
    rewrite conv_com.
    unfold zero_f.
    unfold conv.
    apply inf_eq.
    split.
    intros.
    apply Im_inv in H0.
    destruct H0.
    destruct H0.
    rewrite Rbar_plus_0_l in H1.
    rewrite <- H1.
    unfold In in H0.
    destruct H0.
    unfold non_decreasing in non_decr0.
    case (Rlt_dec 0 x1).
    intros.
    apply (non_decr0 0 x1 (conj (Rge_refl 0) H0) r).
    intros.
    apply Rnot_lt_le in n.
    apply Rge_le in H0.
    pose (Rle_antisym x1 0 n H0).
    rewrite e.
    apply Rbar_le_refl.
    exists (p 0).
    split.
    apply (Im_intro R Rbar _ _ 0).
    unfold In.
    split.
    intuition.
    apply Rge_le.
    tauto.
    rewrite Rbar_plus_0_l.
    tauto.
    tauto.
    Qed.
    
    Generalizable Variables a.
    
    (*The convolution is linear with respect to constant addition*)
    Theorem convolution_plus: forall (v: R) `(A: Positive a) `(D: Positive d) t, t >= 0 -> Rbar_plus v (conv a d t) = conv a (fun t => Rbar_plus (d t) v) t.
    intros.
    unfold conv.
    pose (inf_independence).
    assert (Im R Rbar (fun x : R => x >= 0 /\ x <= t) (fun s : R => Rbar_plus (Rbar_plus (a (t - s)) (d s)) v) = Im R Rbar (fun x : R => x >= 0 /\ x <= t) (fun s : R => Rbar_plus (a (t - s)) (Rbar_plus (d s) v))).
    apply image_eq_fun.
    admit.
    rewrite <- H0.
    apply inf_independence.
    Admitted.
  
  (** *** Delta function*)
  
  (*Definition of delta(t - T): 0 for t <= T and infinity for t > T*)
  Definition delta (T: Rbar) : R -> Rbar := fun x => match Rle_lt_dec x T with
    | left _ => 0
    | right _ => p_infty
    end.
   
  
  (*Delta function is always positive*)
  Global Instance DeltaPos(T: R): Positive (delta T).
    split.
    intros.
    intros.
    unfold delta.
    destruct Rle_lt_dec.
    simpl.
    intuition.
    simpl.
    trivial.
    Qed.
  
  (*Delta function is increasing and positive*)
  Global Instance DeltaIncr (T: R): NonDecreasingPositive (delta T).
    split.
    apply (DeltaPos T).
    unfold non_decreasing.
    intros.
    unfold delta.
    destruct Rle_lt_dec.
    destruct Rle_lt_dec.
    simpl.
    intuition.
    simpl.
    trivial.
    destruct Rle_lt_dec.
    pose (Rlt_trans T s t r H0).
    apply Rlt_gt in r1.
    apply Rgt_not_le in r1.
    tauto.
    simpl.
    trivial.
    Qed.

  (*Delta function is a cumulative function*)
  Global Instance DeltaCumul (T: R): T >= 0 -> Cumulative (delta T).
    Proof.
    intros.
    split.
    apply DeltaIncr.
    admit.
    unfold delta.
    destruct Rle_lt_dec.
    trivial.
    apply Rlt_not_ge in r.
    tauto.
    Admitted.
  
  (*delta(t) is the neutral element of convolution*)
  Definition neutral_conv := delta 0.
      
  (*delta(0) = 0*)
  Lemma neutral_conv_0 : neutral_conv 0 = 0.
  pose (DeltaCumul 0).
  pose (Rle_refl 0).
  apply Rle_ge in r.
  pose (c r).
  destruct c0.
  tauto.
  Qed.  
    
  (*delta(t) = infinity for t > 0*)
  Lemma neutral_conv_gt_0 : forall t, t > 0 -> neutral_conv t = p_infty.
  intros.
  unfold neutral_conv.
  unfold delta.
  destruct Rle_lt_dec.
  apply Rle_not_gt in r.
  tauto.
  trivial.
  Qed.
  
  (*The convolution between a function and the neutral element is equal to the input function as long as it is not equal to -infinity*) 
  Theorem conv_with_neutral_r `(F: NotMInf fm): forall t, t >= 0 -> conv fm neutral_conv t = fm t.
  Proof.
  intros.
  unfold conv.
  apply Rge_le in H.
  rewrite <- (set_f_t_plus_f 0 t H).
  rewrite Im_add.
  unfold Add.
  rewrite inf_union.
  rewrite Rminus_0_r.
  rewrite neutral_conv_0.
  rewrite Rbar_plus_0_r.
  pose (inf_singleton (fm t)).
  rewrite <- e at 2.
  assert (Im R Rbar (fun x : R => x > 0 /\ x <= t)
        (fun s : R => Rbar_plus (fm (t - s)) (neutral_conv s)) = Singleton Rbar p_infty).
  apply Extensionality_Ensembles.
  unfold Same_set.
  unfold Included.
  split.
  intros.
  apply Im_inv in H0.
  destruct H0.
  destruct H0.
  apply Singleton_intro.
  unfold In in H0.
  destruct H0.
  pose (neutral_conv_gt_0 x0 H0).
  rewrite e0 in H1.
  destruct F.
  apply Rle_ge in H2.
  apply (Rplus_ge_compat_r (- x0) _ _) in H2.
  rewrite (Rplus_opp_r _) in H2.
  pose (not_inf0 (t - x0) H2).
  apply (Rbar_plus_inf_not_minf ) in n.
  rewrite <- H1.
  apply eq_sym.
  tauto.
  Admitted.

    
    (** ** Deconvolution*)
    
    (*Definition of the deconvolution of two functions*)
    Definition deconv(f g : R -> Rbar) := fun t: R => Rbar_lub (Im R Rbar (fun x: R => x >= 0) (fun s => Rbar_minus (f (t+s)) (g(s)))).
    
    (*The deconvolution of a non decreasing and positive function with an other function is also non decreasing*)
    Theorem deconv_non_decr `(Pa: NonDecreasingPositive pa)(g: R -> Rbar): non_decreasing (deconv pa g).
    Admitted.
    
    (*The deconvolution between a non decreasing positive function and an other one is also non decreasing and positive*)
    Global Instance DeconvNonDecrPos `(Pa: NonDecreasingPositive pa)(g: R -> Rbar): (forall x, pa x >= g x) -> NonDecreasingPositive (deconv pa g).
    Admitted.
    
  End Convolution.
  
  (** ** Minimum between two functions*)
  Section Min.

    (*Definition of the binary minimum between two functions: takes the minumum of the two functions at each point*)
    Definition min_f (f g : R -> Rbar) := fun t: R => Rbar_min (f t) (g t).

    (*The neutral element of the minimum is the function always equal to infinity*)
    Definition neutral_min: R -> Rbar := fun x: R => p_infty.
    
  End Min.

(*If f(0) or g(0) equals 0 then the convolution between f and g is always smaller than min f g*)
Theorem conv_le_min_if_0 : forall f g x, (f(0) = 0 /\ g(0) = 0) -> conv f g x <= min_f f g x.
Admitted.

(*The set of functions from R to Rbar with convolution and the minimum forms a dioid*)
Global Instance MinConv : Dioid min_f conv neutral_min neutral_conv.
Admitted.

(** ** Subadditive closure*)
  
  (*Definition of the convolution power*)
  Fixpoint conv_pow (f: R -> Rbar) (n: nat) :=
  match n with
  | O => neutral_conv
  | S n' => conv f (conv_pow f n')
  end.

(*Definition of the subadditive closure of a function*)
Definition subadd_clos (alpha: R -> Rbar): (R -> Rbar) :=
(fun x: R => Inf_seq (fun n: nat => conv_pow alpha n x)).

(*The subadditive closure of a non-decreasing positive function is also non-decreasing and positive*)
Global Instance SubaddClos`(alpha: NonDecreasingPositive al) : NonDecreasingPositive (subadd_clos al).
Admitted.

(*The subadditive closure of a function is also subadditive*)
Theorem subadd_cl_is_subadd `(alpha: NonDecreasingPositive al): forall a b, a >= 0 /\ b >= 0 -> subadd_clos al (a + b) <= subadd_clos al a + subadd_clos al b.
Admitted.

(*The subadditive closure of a function is equal to 0 for t = 0*)
Theorem subadd_cl_0_is_0 `(alpha: NonDecreasingPositive al): subadd_clos al 0 = 0.
Admitted.

End FunctionOperations.

(** * Server*)

Section Server.

(*Definition of a server/system with one inputs*)
Class Server (S : (R -> Rbar) -> (R -> Rbar) -> Prop) := {
  subset_c_c: forall a d : R -> Rbar, S a d -> Cumulative a /\ Cumulative d;
  completeness: forall a : R -> Rbar, Cumulative a -> exists d, S a d;
  causality: forall a d t, S a d -> t >= 0 -> Rbar_le (d(t)) (a(t))
}.

Generalizable Variables s t.

Theorem finite_server_t `(S: Server s): forall a d t, t >= 0 -> s a d -> is_finite (a t) -> is_finite (d t).
intros.
destruct S.
destruct (subset_c_c0 a d H0).
pose (causality0 a d t H0 H).
unfold is_finite in H1.
rewrite <- H1 in r.
case (Rbar_dec (d t)).
intros.
rewrite H4 in r.
case r.
intros.
destruct H3.
destruct non_decr_pos0.
destruct positive0.
pose (pos_to_pos0 t H).
case H4.
intros.
rewrite H3 in r0.
case r0.
tauto.
Qed.

(*If the input of a server is finite then its output too*)
Theorem finite_server `(S: Server s) : forall a d, s a d -> is_finite_f a -> is_finite_f d.
unfold is_finite_f.
intros.
destruct S.
pose (causality0 a d x H H1).
pose (H0 x H1).
destruct (subset_c_c0 a d H).
destruct H3.
destruct non_decr_pos0.
destruct positive0.
pose (pos_to_pos0 x H1).
unfold is_finite in i.
rewrite <- i in r.
case (Rbar_dec (d x)).
intros.
rewrite H3 in r.
case r.
intros.
case H3.
intros.
rewrite H4 in r0.
case r0.
tauto.
Qed.

(*Definition of a server/system with several inputs*)
Class MultiInput (S : list (R -> Rbar) -> list (R -> Rbar) -> Prop) (n: nat) := {
  same_length: forall (A D : list (R -> Rbar)), S A D -> length A = n \/ length D = n;
  cumul_lists: forall (A D : list (R -> Rbar)) (a d : R -> Rbar), S A D -> (List.In a A -> Cumulative a \/ List.In d D -> Cumulative d);
  completeness_sched: forall (A : list (R -> Rbar)), (forall a, List.In a A -> Cumulative a) -> exists D, S A D;
  causality_sched: forall (A D : list (R -> Rbar)) (i: nat) (t: R), S A D -> lt i n -> List.nth i A (delta 0) t >= List.nth i D (delta 0) t
}.

 
(** ** Server concatenation*)

(*Definition of the concatenation between two servers*)
Definition server_concat `(S: Server s) `(T: Server t) := fun a c => exists b, (s a b) /\ (t b c).

(*The concatenation between two servers is also a server*)
Global Instance ServerConcat `(S: Server s) `(T: Server t): Server (server_concat S T).
destruct S.
destruct T.
split.
intros.
destruct H.
destruct H.
pose (subset_c_c0 a x H).
pose (subset_c_c1 x d H0).
tauto.
intros.
pose (completeness0 a H).
destruct e.
pose (subset_c_c0 a x H0).
destruct a0.
pose (completeness1 x H2).
destruct e.
exists x0.
exists x.
tauto.
intros.
destruct H.
destruct H.
pose (causality0 a x t0 H H0).
pose (causality1 x d t0 H1 H0).
apply (Rbar_le_trans _ _ _ r0 r).
Qed.

End Server.