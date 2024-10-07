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
