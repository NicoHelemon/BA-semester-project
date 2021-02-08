(** In this module we define a non preemptive static priority scheduler. *)

Require Import Reals Image Decidable RbarComp ClassicalDescription.
From Coquelicot Require Import Rbar Lub.
Require Import Definitions SetTheory Packetizer Seq.

(*checks if for a given t and epsilon during the interval ]t, t+ eps[ a is always greater than d or is always equal to d*)
Definition monot_inter (a d: R -> Rbar) (t eps: R) := eps > 0 /\ ((forall delta, 0 < delta < eps -> a (t + delta) <= d(t + delta)) \/ (forall delta, 0 < delta < eps -> a (t + delta) > d (t + delta))).

(*checks if for a given t there exists an epsilon such that during the interval ]t, t+ eps[ a is always greater than d or is always equal to d*)
Definition ex_monot_inter (a d: R -> Rbar) (t: R) := exists eps, monot_inter a d t eps.

Generalizable Variables l.

(* if the input is packetized and th output cumulative there always exists an epsilon that fulfills the condition above*)
Theorem ex_monot_inter_packet `(ls: LengthSequence l) (a d: R -> Rbar) (t: R) : packetized ls a -> Cumulative d -> ex_monot_inter a d t.
Admitted.

(* if the input is packetized and th output cumulative there always exists an epsilon that fulfills the condition above*)
Theorem sig_monot_inter (a d: R -> Rbar) (t: R) (p : ex_monot_inter a d t) : {eps : R | monot_inter a d t eps}.
Admitted.

(* if the input is packetized and th output cumulative there always exists an epsilon that fulfills the condition above*)
Theorem dec_monot_inter (a d: R -> Rbar) (t: R) (p: ex_monot_inter a d t): {forall delta, 0 < delta < proj1_sig (sig_monot_inter a d t p) -> a (t + delta) <= d(t + delta)} + {forall delta, 0 < delta < proj1_sig (sig_monot_inter a d t p) -> a (t + delta) > d (t + delta)}.
Admitted.

(* a is equal to d during the interval [t, t + e]*)
Definition equal_up_to (a d: R -> Rbar) (t: R) (eps: Rbar) := 
match eps with
|Finite e => forall delta, t <= delta <= t + e -> d delta = a delta
|p_infty => forall delta, t <= delta -> d delta = a delta
|m_infty => False
end.

(* d is an affine function during the interval   [t, t + eps]*)
Definition incr_up_to (a d: R -> Rbar) (t c: R)  (eps: Rbar) := 
match eps with
|Finite e => forall delta, t <= delta <= t + e -> d delta = Rbar_plus (a t) (c * (delta - t))
|p_infty => forall delta, t <= delta -> d delta = Rbar_plus (a t) (c * (delta - t))
|m_infty => False
end.

(* set of the epsilons such that the condition above is *)
Definition set_monot_inter (a d : R -> Rbar) (t: R): Ensemble R := (fun eps => monot_inter a d t eps).

(*maximum of that set*)
Definition max_monot_inter (a d : R -> Rbar) (t: R): Rbar := Lub_Rbar (set_monot_inter a d t).

(*Find the minimum between the epsilon of (Ah Al) (Dh Dl)*)
Definition find_eps (ah al dh dl: R -> Rbar) (t: R) :=
Rbar_min (max_monot_inter ah dh t) (max_monot_inter al dl t).

(*Remaining length of the packet to process*)
Definition rem_length `(ls: LengthSequence l) (v: R):=
INR(nat_sum l (S (last_packet l im_0 v))) - v.

(* the scheduler is not serving any packet, i e it's value is in the image of the partial of l*)
Definition is_not_serving `(ls: LengthSequence l) (v: R) :=
INR(nat_sum l (last_packet l im_0 v)) = v.

(*Remaining processing time of a packet*)
Definition proc_time `(ls: LengthSequence l) (v: Rbar) (c: R): R := real ((rem_length ls v) / c).

(*Definition of the scheduler*)
Class Scheduler (S : (R -> Rbar) -> (R -> Rbar) -> (R -> Rbar) -> (R -> Rbar) -> Prop) `(ls: LengthSequence l) (c: R) := {
  packet_inputs: forall ah al dh dl, S ah al dh dl -> packetized ls ah /\ packetized ls al;
  cumul_outputs: forall ah al dh dl, S ah al dh dl -> Cumulative dh /\ Cumulative dl;
  output_def: forall ah al dh dl (p: S ah al dh dl), forall t, t >= 0 ->
  match dec_monot_inter ah dh t (ex_monot_inter_packet ls ah dh t (proj1 (packet_inputs ah al dh dl p)) (proj1 (cumul_outputs ah al dh dl p))) with
  | left _ =>
    match dec_monot_inter al dl t (ex_monot_inter_packet ls al dl t (proj2 (packet_inputs ah al dh dl p)) (proj2 (cumul_outputs ah al dh dl p))) with
    | left _ => equal_up_to ah dh t (t + find_eps ah al dh dl t) /\ equal_up_to al dl t (t + find_eps ah al dh dl t)
    | right _ => equal_up_to ah dh t (t + find_eps ah al dh dl t) /\ incr_up_to al dl t (t + find_eps ah al dh dl t) c
    end
  | right _ =>
    match dec_monot_inter al dl t (ex_monot_inter_packet ls al dl t (proj2 (packet_inputs ah al dh dl p)) (proj2 (cumul_outputs ah al dh dl p))) with
    | left _ => incr_up_to ah dh t (t + find_eps ah al dh dl t) c /\ equal_up_to al dl t (t + find_eps ah al dh dl t)
    | right _ => equal_up_to ah dh t (t + (proc_time ls (dh t) c))  /\ incr_up_to ah dh (t + (proc_time ls (dh t) c)) (t + find_eps ah al dh dl t) c
    /\ incr_up_to al dl t (t + (proc_time ls (dl t) c)) c /\ equal_up_to al dl (t + (proc_time ls (dl t) c)) (t + find_eps ah al dh dl t)
    end
  end
}.





