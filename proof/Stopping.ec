require import AllCore.

type query_t, resp_t.

module type Oracle = {
  proc get(q : query_t) : resp_t
}.

type in_t, out_t.

module type Stoppable = {
  proc init(i : in_t) : query_t
  proc continue(r : resp_t) : query_t
  proc finish(r : resp_t) : out_t
}.

(* Max number of queries. *)
const Q : {int | 1 <= Q} as Q_pos.

(* WLOG, we assume that the module makes _exactly_ Q queries,
 * a run of the module is then defined as follows. *)
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
