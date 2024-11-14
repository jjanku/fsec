pragma Goals:printall.
require import AllCore.

type query_t, resp_t.

module type Oracle = {
  proc get(q : query_t) : resp_t
}.

type in_t, out_t.

(* TODO: Consider changing the type so that
 * the module doesn't have to make any query. *)
module type Stoppable = {
  proc init(i : in_t) : query_t
  proc continue(r : resp_t) : query_t
  proc finish(r : resp_t) : out_t
}.

(* Number of queries. *)
const Q : {int | 1 <= Q} as Q_pos.

(* Assuming that a module S makes _exactly_ Q queries,
 * a run of S with an oracle O is defined as follows. *)
module Runner(S : Stoppable, O : Oracle) = {
  proc run(i : in_t) : out_t = {
    var o : out_t;
    var q : query_t;
    var r : resp_t;
    var c : int;

    q <@ S.init(i);
    c <- 1;

    while (c < Q) {
      r <@ O.get(q);
      q <@ S.continue(r);
      c <- c + 1;
    }

    r <@ O.get(q);
    o <@ S.finish(r);

    return o;
  }
}.

(* TODO: Add a Stoppable definition where the module
 * can finish early, i.e., after <= Q queries, and provide
 * a transformation to a module making = Q queries? *)

(* NOTE: It is possible to use Stoppable modules with standard
 * games using the Runner module and partial argument application:
 *
 *   declare module SAdv <: Stoppable.
 *   module Adv = Runner(SAdv).
 *)

theory Ind.

module IndRunner(S : Stoppable, O : Oracle) = {
  proc iter(q : query_t, n : int) : query_t = {
    var r : resp_t;

    while (0 < n) {
      r <@ O.get(q);
      q <@ S.continue(r);
      n <- n - 1;
    }

    return q;
  }

  proc init(i : in_t, n : int) : query_t = {
    var q : query_t;
    q <@ S.init(i);
    q <@ iter(q, n - 1);
    return q;
  }

  proc init_split(i : in_t, k : int, l : int) : query_t = {
    var q : query_t;
    q <@ init(i, k);
    q <@ iter(q, l);
    return q;
  }

  proc run(i : in_t, n : int) : out_t = {
    var o : out_t;
    var q : query_t;
    var r : resp_t;

    q <@ init(i, n);
    r <@ O.get(q);
    o <@ S.finish(r);

    return o;
  }
}.

section PROOF.

declare module O <: Oracle.
(* TODO: Can we avoid this restriction? *)
declare module S <: Stoppable {-O}.

equiv ind_run_equiv :
  Runner(S, O).run ~ IndRunner(S, O).run :
  (arg{1}, Q) = arg{2} /\ ={glob S, glob O} ==>
  ={res, glob S, glob O}.
proof.
proc; inline.
sim.
while (={glob S, glob O} /\ q{1} = q1{2} /\ c{1} + n1{2} = Q).
+ wp; do 2! call (_ : true); skip => /#.
wp; call (_ : true); wp; skip => /#.
qed.

equiv ind_split_equiv :
  IndRunner(S, O).init ~ IndRunner(S, O).init_split :
  ={glob S, glob O, i} /\ n{1} = k{2} + l{2} /\ 0 < k{2} /\ 0 <= l{2} ==>
  ={res, glob S, glob O}.
proof.
proc => /=; inline.
exlim k{2}, l{2} => k0 l0.
splitwhile {1} 4 : 0 < n0 - l0.
sim.
while (={glob S, glob O} /\ q0{1} = q2{2} /\ n0{1} - l0 = n1{2} /\ 0 <= n1{2} /\ 0 <= l0).
+ wp; do 2! call (_ : true); skip => /#.
wp; call (_ : true); wp; skip => /#.
qed.

end section PROOF.

end Ind.
