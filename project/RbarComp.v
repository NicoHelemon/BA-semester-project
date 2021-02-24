(* This section introduces complementary theorems about Rbar *)

From Coq Require Import Reals ssreflect FunctionalExtensionality Setoid Image.
From Coquelicot Require Import Rbar Rcomplements Compactness Lim_seq Rcomplements Hierarchy Lub.
From mathcomp Require Import ssrnat.

(* x <= y -> x + z <= y + z *)
Lemma Rbar_plus_le_r: forall x y z : Rbar, 
  Rbar_le x y -> Rbar_le (Rbar_plus x z) (Rbar_plus y z).

Proof.
  intros.
  pose (Rbar_le_refl z).
  apply (Rbar_plus_le_compat x y z z H r).
  Qed.

(* x <= y -> z + x <= z + y *)
Lemma Rbar_plus_le_l: forall x y z : Rbar,
  Rbar_le x y -> Rbar_le (Rbar_plus z x) (Rbar_plus z y).

Proof.
  intros.
  pose (Rbar_le_refl z).
  apply (Rbar_plus_le_compat z z x y r H).
  Qed.

(* x >= 0 and y >= 0 -> x + y >= 0 *)
Lemma Rbar_plus_le_pos: forall x y : Rbar,
  Rbar_le 0 x -> Rbar_le 0 y -> Rbar_le 0 (Rbar_plus x y).

Proof.
  intros.
  pose (Rbar_plus_le_compat 0 x 0 y H H0).
  setoid_rewrite Rbar_plus_0_l in r.
  tauto.
  Qed.

(* x is not minus infininity -> x + infinity = infinity *)
Lemma Rbar_plus_inf_not_minf: forall x : Rbar, 
  m_infty <> x -> Rbar_plus x p_infty = p_infty.

Proof.
  intro.
  case x.
  - intros.
    simpl.
    tauto.
  - simpl.
    tauto.
  - simpl.
    tauto.
  Qed.

(* Any element of Rbar is either infinity, minus infinity or finite *)
Theorem Rbar_dec: forall x, 
  x = p_infty \/ x = m_infty \/ is_finite x.

Proof.
  intros.
  case x.
  - intros.
    unfold is_finite.
    tauto.
  - tauto.
  - tauto.
  Qed. 

(* If an element of Rbar is not infinite then it is finite *)
Theorem Rbar_not_finite: forall x,
  ~is_finite x -> x = p_infty \/ x = m_infty.

Proof.
  intros.
  pose (Rbar_dec x).
  case o.
  - tauto.
  - intros.
    case H0.
    - tauto.
    - intros.
      tauto.
  Qed.

(* Currying: (p and q) -> r = p -> (q -> r) *)

(* If none of the arguments are minus infinity then the addition is associtative in Rbar *)
Theorem Rbar_assoc_m_inf: forall x y z, 
  x <> m_infty -> y <> m_infty -> z <> m_infty
  -> Rbar_plus (Rbar_plus x y) z = Rbar_plus x (Rbar_plus y z).

Proof.
  intros.
  pose (Rbar_dec x).
  case o.
  - intros. (* x = p_infty *)
    rewrite H2.
    pose (Rbar_dec y).
    case o0.
    - intros. (* y = p_infty *)
      rewrite H3.
      pose (Rbar_dec z).
      case o1. 
      - intros. (* z = p_infty *)
        rewrite H4.
        intuition.
      - intro. (* z = m_infty \/ is_finite z *)
        case H4.
        - intros.
          rewrite H5.
          intuition.
        - intros.
          rewrite <- H5.
          intuition.
    - intros. (* y = m_infty \/ is_finite y *)
      case H3.
      - intros.
        case (H0 H4).
      - intros.
        unfold is_finite in H4.
        rewrite <- H4.
        pose (Rbar_dec z).
        case o1.
        - intros. (* z = p_infty *)
          rewrite H5.
          intuition.
        - intros. (* z = m_infty \/ is_finite z *)
          case H5.
          - intros.
            rewrite H6.
            intuition.
          - intros.
            rewrite <- H6.
            intuition.
  - intros. (* x = m_infty \/ is_finite x *)
    case H2.
    - intros. (* x = m_infty *)
      case (H H3).
    - intros. (* is_finite x *)
      unfold is_finite in H3.
      rewrite <- H3.
      case (Rbar_dec y).
      - intros. (* y = p_infty *)
        rewrite H4.
        case (Rbar_dec z).
        - intros. (* z = p_infty *)
          rewrite H5.
          intuition.
        - intros. (* z = m_infty \/ is_finite z *)
          case H5.
          - intros.
            case (H1 H6).
          - intros.
            unfold is_finite in H6.
            rewrite <- H6.
            intuition.
      - intros. (* y = m_infty \/ is_finite y *)
        case H4.
        - intros.
          case (H0 H5).
        - intros.
          unfold is_finite in H5.
          rewrite <- H5.
          case (Rbar_dec z).
          - intros.
            rewrite H6.
            intuition.
          - intros.
            case H6.
            - intros.
              case (H1 H7).
            - intros.
              unfold is_finite in H7.
              rewrite <- H7.
              simpl.
              apply Rbar_finite_eq.
              apply Rplus_assoc.
  Qed.

(* If two arguments are finite then the addition is associtative in Rbar *)
Theorem Rbar_assoc_x_y_f: forall x y z,
  is_finite x -> is_finite y ->
  Rbar_plus (Rbar_plus x y) z = Rbar_plus x (Rbar_plus y z).

Proof.
  unfold is_finite.
  intros.
  rewrite <- H.
  rewrite <- H0.
  case (Rbar_dec z).
  - intros.
    rewrite H1.
    intuition.
  - intros.
    case H1.
    - intros.
      rewrite H2.
      intuition.
    - intros.
      rewrite <- H2.
      simpl.
      apply Rbar_finite_eq.
      apply Rplus_assoc.
  Qed.

(* If two arguments are finite then the addition is associtative in Rbar *)
Theorem Rbar_assoc_x_z_f: forall x y z,
  is_finite x -> is_finite z -> 
  Rbar_plus (Rbar_plus x y) z = Rbar_plus x (Rbar_plus y z).

Proof.
  unfold is_finite.
  intros.
  rewrite <- H.
  rewrite <- H0.
  simpl.
  case (Rbar_dec y).
  - intros.
    rewrite H1.
    intuition.
  - intros.
    case H1.
    - intros.
      rewrite H2.
      intuition.
    - intros.
      unfold is_finite in H2.
      rewrite <- H2.
      simpl.
      apply Rbar_finite_eq.
      apply Rplus_assoc.
  Qed.


(* If two arguments are finite then the addition is associtative in Rbar *)
Theorem Rbar_assoc_y_z_f: forall x y z,
  is_finite y -> is_finite z ->
  Rbar_plus (Rbar_plus x y) z = Rbar_plus x (Rbar_plus y z).

Proof.
  unfold is_finite.
  intros.
  rewrite <- H.
  rewrite <- H0.
  simpl.
  case (Rbar_dec x).
  - intros.
    rewrite H1.
    intuition.
  - intros.
    case H1.
    - intros.
      rewrite H2.
      intuition.
    - intros.
      unfold is_finite in H2.
      rewrite <- H2.
      simpl.
      apply Rbar_finite_eq.
      apply Rplus_assoc.
  Qed.

(* If x and y are equal then finite x and finite y are also equal *)
Theorem finite_eq: forall x y : R,
  x = y <-> Finite x = Finite y.

Proof.
  intros.
  split.
  - intros.
    rewrite H.
    tauto.
  - intros.
    assert (Rbar_le x y).
    rewrite H.
    apply Rbar_le_refl.
    assert (Rbar_le y x).
    rewrite H.
    apply Rbar_le_refl.
    simpl in H0.
    simpl in H1.
    apply (Rle_antisym _ _ H0 H1).
  Qed.
