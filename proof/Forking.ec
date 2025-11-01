(* Forking lemma.
 *
 * Largely based on the proof of the general forking lemma
 * by Bellare & Neven [0].
 *
 * [0] https://cseweb.ucsd.edu/~mihir/papers/multisignatures.pdf
 *)

pragma Goals:printall.

require import AllCore List Distr DInterval Finite StdOrder StdBigop RealFun.
import RField RealOrder Bigreal BRA.
require Stopping.
require import SquareConvex.

(* Input & auxiliary output type. *)
type in_t, aux_t.

type query_t, resp_t.
const Q : {int | 1 <= Q} as Q_pos.

(* TODO: Is this idiomatic in EC? *)
clone import Stopping as ForkStopping with
  type query_t <- query_t,
  type resp_t  <- resp_t,
  op   Q       <- Q,
  type in_t    <- in_t,
  type out_t   <= int * aux_t
proof *.
realize Q_pos by exact Q_pos.
(* TODO: Why is this not imported as well? *)
type out_t = int * aux_t.
export ForkStopping.

op [lossless uniform] dresp : resp_t distr.

(* Forgetful random oracle, may respond inconsistently to
 * repeated queries. This is intentional, otherwise we may not
 * be able to repogram the oracle at the forking point. *)
module FRO : Oracle = {
  proc get(q : query_t) : resp_t = {
    var r : resp_t;
    r <$ dresp;
    return r;
  }
}.

type log_t = query_t * resp_t.

(* NOTE: The standard library contains a similar
 * oracle transformer which logs just the queries.
 * We need to record responses as well. *)
module Log(O : Oracle) : Oracle = {
  var log : log_t list

  proc get(q : query_t) : resp_t = {
    var r;
    r <@ O.get(q);
    log <- log ++ [(q, r)];
    return r;
  }
}.

type state_t.
op pair_st : state_t * state_t -> state_t.
op unpair_st : state_t -> state_t * state_t.
axiom pair_st_inj : injective pair_st.
axiom pair_st_can : cancel pair_st unpair_st.

require RewWithInit.
clone RewWithInit.RWI as Rewinding with
  type sbits <- state_t,
  type iat   <- int,
  type irt   <- query_t * int * (log_t list),
  type rrt   <- out_t * (log_t list),
  op pair_sbits <- pair_st,
  op unpair     <- unpair_st
proof *.
realize ips by exact pair_st_inj.
(* FIXME: Why isn't this proved in the cloned theory? *)
realize RW.ips by exact pair_st_inj.
realize unpair_pair by exact pair_st_can.
(* Ditto. *)
realize RW.unpair_pair by exact pair_st_can.

(* FIXME: Import form Rewinding.RW? *)
module type Rewindable = {
  proc getState() : state_t
  proc setState(st : state_t) : unit
}.

op int2st : int -> state_t.
op st2int : state_t -> int.
axiom int2st_inj : injective int2st.
axiom int2st_can : cancel int2st st2int.

op q2st : query_t -> state_t.
op st2q : state_t -> query_t.
axiom q2st_inj : injective q2st.
axiom q2st_can : cancel q2st st2q.

op r2st : resp_t -> state_t.
op st2r : state_t -> resp_t.
axiom r2st_inj : injective r2st.
axiom r2st_can : cancel r2st st2r.

require State.
clone import State as St with
  type state_t <- state_t,
  op   pair_st <- pair_st,
  op   unpair_st <- unpair_st
proof *.
realize pair_st_inj by exact pair_st_inj.
realize pair_st_can by exact pair_st_can.

clone import ListState as LogState with
  type elem_t  <- log_t,
  op   elem2st <- fun (l : log_t) => pair_st (q2st l.`1, r2st l.`2),
  op   st2elem <- fun st => let (q_st, r_st) = unpair_st st in (st2q q_st, st2r r_st),
  op   int2st  <- int2st,
  op   st2int  <- st2int
  rename "list" as "log"
proof *.
realize elem2st_inj by smt(pair_st_inj q2st_inj r2st_inj).
realize elem2st_can by smt(pair_st_can q2st_can r2st_can).
realize int2st_inj by exact int2st_inj.
realize int2st_can by exact int2st_can.

(* TODO: Generalize to other oracles as well?
 * Most of the lemmas below need to assume very little about
 * the used oracle. It should be sufficient to require
 * rewindability plus some bound on the probability of
 * a collision, such as:
 * forall q r &m : Pr[O.get(q) @ &m : res = r] <= bound *)


(* TODO: Does it make sense to generalize somehow?
 * Could we, for example, prove the forking lemma
 * for any event E such that E => (0 <= j < Q)? *)
(* NOTE: We index queries from 0 (unlike pen&paper proofs). *)
op success (j : int) : bool = 0 <= j < Q.

module type Forkable = {
  include Rewindable
  include Stoppable
}.

module IForker(I : IGen, F : Forkable) = {
  (* TODO: Might be easier to prove invariants about these if we
   * keep them local? In such case, we would need to return
   * those in run to be able to refer to the results.
   * Check the proofs! *)
  var j1, j2 : int
  var log1, log2 : log_t list
  var r1, r2 : resp_t

  (* First run of F, with query and state logging. *)
  proc fst() : out_t * (log_t list) * (state_t list) = {
    var sts : state_t list;
    var st : state_t;
    var i : in_t;
    var o : out_t;
    var q : query_t;
    var r : resp_t;
    var c : int;

    sts <- [];
    Log.log <- [];

    i <@ I.gen();
    q <@ F.init(i);
    c <- 1;

    while (c < Q) {
      st <@ F.getState();
      sts <- sts ++ [st];
      r <@ Log(FRO).get(q);
      q <@ F.continue(r);
      c <- c + 1;
    }

    st <@ F.getState();
    sts <- sts ++ [st];
    r <@ Log(FRO).get(q);
    o <@ F.finish(r);

    return (o, Log.log, sts);
  }

  (* Second partial run of F, with query logging. *)
  proc snd(q : query_t, c : int) : out_t * (log_t list) = {
    var o : out_t;
    var r : resp_t;

    Log.log <- [];

    while (c < Q) {
      r <@ Log(FRO).get(q);
      q <@ F.continue(r);
      c <- c + 1;
    }

    r <@ Log(FRO).get(q);
    o <@ F.finish(r);

    return (o, Log.log);
  }

  proc run() : int * aux_t * aux_t = {
    var sts : state_t list;
    var st : state_t;
    var o1, o2 : out_t;
    var j : int;
    var a1, a2 : aux_t;
    var q : query_t;

    (o1, log1, sts) <@ fst();
    (j1, a1) <- o1;
    (q, r1) <- nth witness log1 j1;

    (* TODO: Check whether failing early (! success j1)
     * would simplify some proofs. *)

    (* Rewind. *)
    st <- nth witness sts j1;
    F.setState(st);

    (o2, log2) <@ snd(q, j1 + 1);
    (j2, a2) <- o2;
    log2 <- (take j1 log1) ++ log2;
    r2 <- (nth witness log2 j1).`2;

    j <- if success j1 /\ success j2 /\ j1 = j2 /\ r1 <> r2
      then j1 else -1;

    return (j, a1, a2);
  }
}.

(* NOTE: In the pen & paper proof, the authors first show that
 * the probability bound holds for a forker with a fixed input
 * and then prove using Jensen's inequality and linearity of
 * expectation that it also holds when we average over different
 * inputs.
 *
 * Here, we use a slightly different approach. We make the input
 * generation a part of the forking algorithm and prove the result
 * in this general setting. The bound for a fixed input is then
 * obtained for free by using a constant input generator. (This way,
 * we fully utilize the power of the rew_with_init lemma and do not
 * have to import other results from the easycrypt-rewinding library
 * such as reflection.) *)

module Forker(F : Forkable) = {
  proc run(i : in_t) : int * aux_t * aux_t = {
    var ret;
    ConstGen.i <- i;
    ret <@ IForker(ConstGen, F).run();
    return ret;
  }
}.

module GenThenFork(I : IGen, F : Forkable) = {
  proc run() : int * aux_t * aux_t = {
    var i, ret;
    i <@ I.gen();
    ret <@ Forker(F).run(i);
    return ret;
  }
}.

equiv gen_then_fork_equiv (I <: IGen {-IForker}) (F <: Forkable {-I, -IForker}) :
  GenThenFork(I, F).run ~ IForker(I, F).run :
  ={glob I, glob F} ==> ={glob I, glob F, glob IForker, res}.
proof.
proc.
inline * - Log.
wp -2 100.
swap {2} 3 -2.
sim.
qed.

section PROOF.

local equiv oracle_log_equiv (O <: Oracle) :
  O.get ~ Log(O).get : ={glob O, arg} ==> ={glob O, res}.
proof.
proc *.
inline.
sim.
qed.

(* TODO: Move this somewhere else? *)
equiv runner_log_equiv (S <: Stoppable {-Log}) :
  Runner(S, FRO).run ~ Runner(S, Log(FRO)).run :
  ={glob S, arg} ==> ={glob S, res}.
proof.
proc.
call (_ : true).
call (oracle_log_equiv FRO).
while (={glob S, c, q}).
+ rewrite equiv [{2} 1 - (oracle_log_equiv FRO)].
  sim.
conseq (_ : _ ==> ={glob S, c, q}) => //.
sim.
qed.

equiv irunner_log_equiv (I <: IGen {-Log}) (S <: Stoppable {-I, -Log}) :
  IRunner(I, S, FRO).run ~ IRunner(I, S, Log(FRO)).run :
  ={glob I, glob S} ==> ={glob I, glob S, res}.
proof.
proc.
rewrite equiv [{2} 2 -(runner_log_equiv S)].
+ sim.
call (_ : true).
auto.
qed.

(* TODO: Log should, at this point, probably be moved outside this file. *)
hoare run_log_size (S <: Stoppable {-Log}) (O <: Oracle {-Log}) :
  Runner(S, Log(O)).run : Log.log = [] ==> size Log.log = Q.
proof.
have get_inc : forall n, hoare[
  Log(O).get : size Log.log = n ==> size Log.log = n + 1].
+ move => n.
  proc.
  wp; call (_ : true).
  auto; smt(size_cat).
proc.
call (_ : true).
ecall (get_inc (Q - 1)).
while (c <= Q /\ size Log.log = c - 1).
+ wp; call (_ : true).
  ecall (get_inc (c - 1)).
  auto => /#.
wp; call (_ : true).
auto => />.
smt(Q_pos).
qed.

hoare irun_log_size (I <: IGen {-Log}) (S <: Stoppable {-Log}) (O <: Oracle {-Log}) :
  IRunner(I, S, Log(O)).run : Log.log = [] ==> size Log.log = Q.
proof.
proc.
call (run_log_size S O).
call (_ : true).
skip => //.
qed.

declare module I <: IGen {-Log, -IForker}.

declare module F <: Forkable {-I, -FRO, -Log, -Runner, -IForker}.

(* Coppied from easycrypt-rewinding. *)
declare axiom F_rewindable :
  exists (f : glob F -> state_t), injective f /\
  (forall &m, Pr[F.getState() @ &m : (glob F) = (glob F){m} /\ res = f (glob F){m}] = 1%r) /\
  (forall &m st (x: glob F), st = f x => Pr[F.setState(st) @ &m : glob F = x] = 1%r) /\
  islossless F.setState.

(* NOTE: These two could be avoided if we used the alternative version of the rewinding lemma. *)
declare axiom I_gen_ll : islossless I.gen.
declare axiom F_init_ll : islossless F.init.

declare axiom F_continue_ll : islossless F.continue.
declare axiom F_finish_ll : islossless F.finish.

local phoare get_st_preserves_glob (gF : glob F):
  [F.getState : (glob F) = gF ==> (glob F) = gF] = 1%r.
proof.
elim F_rewindable.
move => f [_ [get_st_prop [_ _]]].
proc *.
call (_ : glob F = gF ==> glob F = gF /\ res = f gF).
+ bypr => &m gF_mem.
  rewrite -gF_mem.
  apply (get_st_prop &m).
auto.
qed.

local lemma get_st_ll : islossless F.getState.
proof.
proc *.
exlim (glob F) => gF.
call (get_st_preserves_glob gF).
auto.
qed.

local lemma set_st_ll : islossless F.setState.
proof.
smt(F_rewindable).
qed.

(* STEP 1:
 * Various lemmas that allow expressing the probability of a
 * successful fork in terms of probabilities of simpler events.
 *)

local lemma fork_pr &m :
  Pr[IForker(I, F).run() @ &m : success res.`1] =
  Pr[IForker(I, F).run() @ &m : IForker.j1 = IForker.j2 /\ success IForker.j1 /\ IForker.r1 <> IForker.r2].
proof.
byequiv => //.
proc.
seq 9 9 : (={glob IForker}).
+ sim.
auto => /#.
qed.

local lemma pr_split &m :
  Pr[IForker(I, F).run() @ &m : IForker.j1 = IForker.j2 /\ success IForker.j1 /\ IForker.r1 <> IForker.r2] >=
  Pr[IForker(I, F).run() @ &m : IForker.j1 = IForker.j2 /\ success IForker.j1] -
  Pr[IForker(I, F).run() @ &m : success IForker.j1 /\ IForker.r1 = IForker.r2].
proof.
(* TODO: Cannot use occurence selector with rewrite Pr? *)
have -> :
  Pr[IForker(I, F).run() @ &m : IForker.j1 = IForker.j2 /\ success IForker.j1] =
  Pr[IForker(I, F).run() @ &m : IForker.j1 = IForker.j2 /\ success IForker.j1 /\ IForker.r1 = IForker.r2] +
  Pr[IForker(I, F).run() @ &m : IForker.j1 = IForker.j2 /\ success IForker.j1 /\ IForker.r1 <> IForker.r2].
+ by rewrite Pr[mu_split IForker.r1 = IForker.r2]; smt().
have ABC_le_BC :
  Pr[IForker(I, F).run() @ &m : IForker.j1 = IForker.j2 /\ success IForker.j1 /\ IForker.r1 = IForker.r2] <=
  Pr[IForker(I, F).run() @ &m : success IForker.j1 /\ IForker.r1 = IForker.r2].
+ by rewrite Pr[mu_sub].
smt().
qed.

local equiv fst_run_log_equiv log0 :
  IForker(I, F).fst ~ IRunner(I, F, Log(FRO)).run :
  ={glob I, glob F} /\ Log.log{2} = log0 ==>
  ={glob I, glob F} /\ res{1}.`1 = res{2} /\ log0 ++ res{1}.`2 = Log.log{2}.
proof.
proc => /=.
inline Runner.
wp.
call (_ : true).
have log_equiv : equiv[
  Log(FRO).get ~ Log(FRO).get :
  ={arg} /\ log0 ++ Log.log{1} = Log.log{2} ==>
  ={res} /\ log0 ++ Log.log{1} = Log.log{2}
].
+ proc; inline.
  wp; rnd; wp; skip.
  smt(catA).
call log_equiv.
wp.
ecall {1} (get_st_preserves_glob (glob F){1}).
while (={q, c, glob F} /\ log0 ++ Log.log{1} = Log.log{2}).
+ wp.
  call (_ : true).
  call log_equiv.
  wp.
  ecall {1} (get_st_preserves_glob (glob F){1}).
  auto => />.
do 2! (wp; call (_ : true)).
auto => />.
smt(cats0).
qed.

local equiv fst_run_equiv :
  IForker(I, F).fst ~ IRunner(I, F, FRO).run :
  ={glob I, glob F} ==> ={glob I, glob F} /\ res{1}.`1 = res{2}.
proof.
proc *.
rewrite equiv [{2} 1 (irunner_log_equiv I F)].
exlim (Log.log{2}) => log0.
call (fst_run_log_equiv log0).
auto.
qed.

local hoare fst_log_size :
  IForker(I, F).fst : true ==> size res.`2 = Q.
proof.
conseq (fst_run_log_equiv []) (irun_log_size I F FRO) => /#.
qed.

const pr_collision = 1%r / (size (to_seq (support dresp)))%r.

(* TODO: Decompose? *)
local lemma pr_succ_resp_eq &m :
  Pr[IForker(I, F).run() @ &m : success IForker.j1 /\ IForker.r1 = IForker.r2] <=
  Pr[IRunner(I, F, FRO).run() @ &m : success res.`1] * pr_collision.
proof.
byphoare (: glob I = (glob I){m} /\ glob F = (glob F){m} ==> _) => //.
proc.
seq 3 : (success IForker.j1)
  Pr[IRunner(I, F, FRO).run() @ &m : success res.`1] pr_collision
  _ 0%r
  (size IForker.log1 = Q);
last by trivial.

(* #pre ==> size IForker.log1 = Q *)
+ wp.
  call fst_log_size.
  auto.

(* #pre ==> success IForker.j1 *)
+ wp.
  call (_ : glob I = (glob I){m} /\ glob F = (glob F){m} ==> success res.`1.`1).
  + bypr => &m0 glob_eq.
    byequiv => //.
    conseq fst_run_equiv; smt().
  auto.

(* success IForker.j1 ==> #post *)
+ inline.
  wp.
  conseq (_ : _ ==> success IForker.j1 /\ IForker.r1 = (head witness Log.log).`2).
  + smt(nth_cat size_takel nth0_head).
  (* FIXME: This is rather painful. Call doesn't work in pHL? *)
  seq 12 : (success IForker.j1 /\ IForker.r1 = (head witness Log.log).`2)
    pr_collision 1%r
    _ 0%r;
  1,3,5: trivial; first last.
  + hoare; call (_ : true); auto.
  wp.
  have mu_dresp_eq :
    forall r0, mu dresp (fun r => r0 = r) <= pr_collision.
  + move => r0.
    have -> : (fun r => r0 = r) = pred1 r0 by smt().
    rewrite (mu1_uni_ll _ _ dresp_uni dresp_ll).
    smt(invr_ge0 size_ge0).
  case (IForker.j1 = Q - 1).
  (* case: IForker.j1 = Q*)
  + rcondf 6.
    + wp; call (_ : true); auto.
    rnd; wp => /=.
    call (_ : true); auto.
    move => &hr [[_ succ] _].
    rewrite succ /=.
    apply mu_dresp_eq.
  (* case: IForker.j1 <> Q *)
  unroll 6; rcondt 6.
  + wp; call (_ : true); wp; skip => /#.
  seq 11 : (success IForker.j1 /\ IForker.r1 = (head witness Log.log).`2)
    pr_collision 1%r
    _ 0%r
    (Log.log <> []);
  3,5: trivial.
  + wp; rnd; wp; call (_ : true); wp; skip => /#.
  + wp; rnd; wp; call (_ : true); wp; skip => /=.
    move => &hr [[_ succ] _].
    rewrite succ /=.
    apply mu_dresp_eq.
  hoare.
  rnd; wp.
  while (Log.log <> [] /\ ! (success IForker.j1 /\ IForker.r1 = (head witness Log.log).`2)).
  + wp; call (_ : true); wp; rnd; wp; skip => /#.
  wp; call (_ : true); skip => /#.

(* ! success IForker.j1 ==> #post *)
hoare.
conseq (_ : _ ==> ! success IForker.j1); 1: smt().
wp.
call (_ : true) => //.
call (_ : true).
auto.
qed.

(* FIXME: The following two lemmas are almost identical.
 * Try to extract the common bits into a separate lemma or
 * reuse the existing PrIntervalToSum (easycrypt-zk) theory. *)
local lemma pr_split_sum &m :
  Pr[IForker(I, F).run() @ &m : IForker.j1 = IForker.j2 /\ success IForker.j1] =
  bigi predT (fun j => Pr[IForker(I, F).run() @ &m : IForker.j1 = j /\ IForker.j2 = j]) 0 Q.
proof.
rewrite /success.
have -> :
  forall n, 0 <= n =>
  Pr[IForker(I, F).run() @ &m : IForker.j1 = IForker.j2 /\ 0 <= IForker.j1 && IForker.j1 < n] =
  bigi predT (fun j => Pr[IForker(I, F).run() @ &m : IForker.j1 = j /\ IForker.j2 = j]) 0 n;
[idtac | smt(Q_pos) | trivial].
apply ge0ind => /=.
+ smt().
+ rewrite big_geq => //.
  have -> /= : forall x, (0 <= x < 0) = false by smt().
  by rewrite Pr[mu_false].
move => n n_ge0 ind _.
rewrite big_int_recr //=.
rewrite Pr[mu_split IForker.j1 < n].
have -> : forall b x, ((b /\ 0 <= x < n + 1) /\ x < n) <=> (b /\ 0 <= x < n) by smt().
rewrite ind //.
have -> // : forall j1 j2, ((j1 = j2 /\ 0 <= j1 < n + 1) /\ ! j1 < n) <=> (j1 = n /\ j2 = n) by smt().
qed.

local lemma pr_succ_sum &m :
  Pr[IRunner(I, F, FRO).run() @ &m : success res.`1] =
  bigi predT (fun j => Pr[IRunner(I, F, FRO).run() @ &m : res.`1 = j]) 0 Q.
proof.
rewrite /success.
have -> :
  forall n, 0 <= n =>
  Pr[IRunner(I, F, FRO).run() @ &m : 0 <= res.`1 < n] =
  bigi predT (fun j => Pr[IRunner(I, F, FRO).run() @ &m : res.`1 = j]) 0 n;
[idtac | smt(Q_pos) | trivial].
apply ge0ind => /=.
+ smt().
+ rewrite big_geq => //.
  have -> /= : forall x, (0 <= x < 0) = false by smt().
  by rewrite Pr[mu_false].
move => n n_ge0 ind _.
rewrite big_int_recr //=.
rewrite Pr[mu_split res.`1 < n].
have -> : forall x, ((0 <= x < n + 1) /\ x < n) <=> (0 <= x < n) by smt().
rewrite ind //.
have -> // : forall j, ((0 <= j < n + 1) /\ ! j < n) <=> (j = n) by smt().
qed.

(* STEP 2:
 * At this point, we can focus on the following probability:
 * Pr[IForker(F).run(i) @ &m : IForker.j1 = j /\ IForker.j2 = j].
 *
 * The key observation is that we can replace IForker by a module,
 * that always forks after the j-th query and the probability
 * does not change.
 *
 * Then, after fixing the forking point, it is easy to transform
 * the module into the shape required by the rew_with_init lemma.
 *)

local module SplitForker(I : IGen, F : Forkable) = {
  var bad : bool

  (* IForker.fst that runs F only until the first C queries. *)
  proc fst_partial(C : int) : query_t * (log_t list) * (state_t list) = {
    var sts : state_t list;
    var st : state_t;
    var i : in_t;
    var o : out_t;
    var q : query_t;
    var r : resp_t;
    var c : int;

    sts <- [];
    Log.log <- [];

    i <@ I.gen();
    q <@ F.init(i);
    c <- 1;

    (* CHANGE: < C instead of < Q. *)
    while (c < C) {
      st <@ F.getState();
      sts <- sts ++ [st];
      r <@ Log(FRO).get(q);
      q <@ F.continue(r);
      c <- c + 1;
    }

    (* CHANGE: Finish removed. *)

    return (q, Log.log, sts);
  }

  (* Same as IForker.snd, but with state recording. *)
  (* TODO: Consider adding state recording to IForker.snd. *)
  proc snd(q : query_t, c : int) : out_t * (log_t list) * (state_t list) = {
    var sts : state_t list;
    var st : state_t;
    var o : out_t;
    var r : resp_t;

    sts <- [];
    Log.log <- [];

    while (c < Q) {
      st <@ F.getState();
      sts <- sts ++ [st];
      r <@ Log(FRO).get(q);
      q <@ F.continue(r);
      c <- c + 1;
    }

    st <@ F.getState();
    sts <- sts ++ [st];
    r <@ Log(FRO).get(q);
    o <@ F.finish(r);

    return (o, Log.log, sts);
  }

  proc fst(C : int) : out_t * (log_t list) * (state_t list) = {
    var sts, sts1, sts2 : state_t list;
    var log, log1, log2 : log_t list;
    var q : query_t;
    var o : out_t;

    (q, log1, sts1) <@ fst_partial(C);
    (o, log2, sts2) <@ snd(q, C);
    sts <- sts1 ++ sts2;
    log <- log1 ++ log2;

    return (o, log, sts);
  }

  (* IForker.run with bad event logging, with some unnecessary bits removed
   * (e.g., we don't care about aux output nor the two responses to q) *)
  proc run1(j : int) : int * int * aux_t * aux_t * (log_t list) * (log_t list) = {
    var sts1, _sts2 : state_t list;
    var st : state_t;
    var log1, log2 : log_t list;
    var o1, o2 : out_t;
    var j1, j1', j2 : int;
    var a1, a2 : aux_t;
    var q : query_t;

    (o1, log1, sts1) <@ fst(j + 1);
    (j1, a1) <- o1;

    bad <- false;
    j1' <- j1;
    if (j1 <> j) {
      bad <- true;
    }

    q <- (nth witness log1 j1').`1;
    st <- nth witness sts1 j1';
    F.setState(st);

    (o2, log2, _sts2) <@ snd(q, j1' + 1);
    (j2, a2) <- o2;
    log2 <- (take j1' log1) ++ log2;

    return (j1, j2, a1, a2, log1, log2);
  }

  (* Same as run1, except we always rewind to the j-th query. *)
  proc run2(j : int) : int * int * aux_t * aux_t * (log_t list) * (log_t list) = {
    var sts1, _sts2 : state_t list;
    var st : state_t;
    var log1, log2 : log_t list;
    var o1, o2 : out_t;
    var j1, j1', j2 : int;
    var a1, a2 : aux_t;
    var q : query_t;

    (o1, log1, sts1) <@ fst(j + 1);
    (j1, a1) <- o1;

    bad <- false;
    j1' <- j1;
    if (j1 <> j) {
      bad <- true;
      (* CHANGE: *)
      j1' <- j;
    }

    q <- (nth witness log1 j1').`1;
    st <- nth witness sts1 j1';
    F.setState(st);

    (o2, log2, _sts2) <@ snd(q, j1' + 1);
    (j2, a2) <- o2;
    log2 <- (take j1' log1) ++ log2;

    return (j1, j2, a1, a2, log1, log2);
  }
}.

local lemma fst_split_equiv C :
  1 <= C <= Q =>
  equiv[
    IForker(I, F).fst ~ SplitForker(I, F).fst :
    ={glob I, glob F} /\ arg{2} = C ==> ={glob I, glob F, res}
  ].
proof.
move => C_range.
proc.
inline SplitForker(I, F).fst_partial SplitForker(I, F).snd Log.
wp.
call (_ : true).
wp.
call (_ : true); 1: auto.
wp.
call (_ : true).
splitwhile{1} 6 : c < C.
conseq (_ : _ ==> ={glob I, glob F} /\ q{1} = q1{2} /\ Log.log{1} = log1{2} ++ Log.log{2} /\ sts{1} = sts1{2} ++ sts3{2}) => />.
+ smt(catA).
while (={glob I, glob F} /\ q{1} = q1{2} /\ Log.log{1} = log1{2} ++ Log.log{2} /\ sts{1} = sts1{2} ++ sts3{2} /\ c{1} = c0{2}).
+ wp. call (_ : true). wp. call (_ : true). auto. wp. call (_ : true). skip => />. smt(catA).
wp.
conseq (_ : _ ==> ={glob I, glob F} /\ q{1} = q0{2} /\ Log.log{1} = Log.log{2} /\ sts{1} = sts0{2} /\ c{1} = C) => />.
+ smt(cats0).
while (={glob I, glob F} /\ q{1} = q0{2} /\ Log.log{1} = Log.log{2} /\ sts{1} = sts0{2} /\ c{1} = c{2} /\ c{1} <= C /\ C0{2} = C).
+ wp. call (_ : true). wp. call (_ : true). auto. wp. call (_ : true). skip => />. smt().
wp.
call (_ : true).
call (_ : true).
auto => /#.
qed.

local equiv snd_equiv :
  IForker(I, F).snd ~ SplitForker(I, F).snd :
  ={glob F, arg} ==> ={glob F} /\ res{1}.`1 = res{2}.`1 /\ res{1}.`2 = res{2}.`2.
proof.
proc => /=.
sim.
ecall {2} (get_st_preserves_glob (glob F){2}).
while (={q, Log.log, glob F, c}).
+ sim.
  ecall {2} (get_st_preserves_glob (glob F){2}).
  auto.
auto.
qed.

local lemma run_run1_equiv j :
  0 <= j < Q =>
  equiv[
    IForker(I, F).run ~ SplitForker(I, F).run1 :
    ={glob I, glob F} /\ arg{2} = j ==>
    ={glob I, glob F} /\ IForker.j1{1} = res{2}.`1 /\ IForker.j2{1} = res{2}.`2 /\
      res{1}.`2 = res{2}.`3 /\ res{1}.`3 = res{2}.`4 /\
      IForker.log1{1} = res{2}.`5 /\ IForker.log2{1} = res{2}.`6
  ].
proof.
move => j_range.
proc.
wp => /=.
call snd_equiv.
call (_ : true).
wp => /=.
call (fst_split_equiv (j + 1)); 1: smt().
auto => /#.
qed.

local lemma pr_run1_eq &m j :
  0 <= j < Q =>
  Pr[IForker(I, F).run() @ &m : IForker.j1 = j /\ IForker.j2 = j] =
  Pr[SplitForker(I, F).run1(j) @ &m : res.`1 = j /\ res.`2 = j].
proof.
move => j_range.
byequiv => //.
conseq (run_run1_equiv j j_range); smt().
qed.

(* TODO: Try to prove this using pRHL, i.e., without using
 * the syntactic byupto tactic. *)
local lemma pr_run2_ineq &m j :
  Pr[SplitForker(I, F).run1(j) @ &m : res.`1 = j /\ res.`2 = j] >=
  Pr[SplitForker(I, F).run2(j) @ &m : res.`1 = j /\ res.`2 = j].
proof.
have :
  Pr[SplitForker(I, F).run2(j) @ &m : res.`1 = j /\ res.`2 = j] <=
    Pr[SplitForker(I, F).run1(j) @ &m : res.`1 = j /\ res.`2 = j] +
  Pr[SplitForker(I, F).run2(j) @ &m : (res.`1 = j /\ res.`2 = j) /\ SplitForker.bad].
+ byupto.
have -> :
  Pr[SplitForker(I, F).run2(j) @ &m : (res.`1 = j /\ res.`2 = j) /\ SplitForker.bad] = 0%r.
+ byphoare (_ : arg = j ==> _) => //.
  hoare.
  proc => /=.
  conseq (_ : _ ==> !(j1 = j /\ SplitForker.bad)); 1: smt().
  do 3! (wp; call (_ : true) => //).
trivial.
qed.

(* Need to transform SplitForker.run2 into a form
 * that is suitable for application of the rew_with_init lemma. *)

local module InitWrapper(I : IGen, F : Forkable) = {
  proc init(j : int) : query_t * int * (log_t list) = {
    var q, log, sts;
    (q, log, sts) <@ SplitForker(I, F).fst_partial(j + 1);
    return (q, j, log);
  }
}.

local module RewindWrapper(I : IGen, F : Forkable) = {
  (* TODO: Rewrite SplitForker.snd in such a way that it doesn't use the
   * Log module so that we don't have to store the log here? We would get
   * rid of the serialization axioms here, but not in ForkingRO. *)
  proc getState() : state_t = {
    var gF_st;
    gF_st <@ F.getState();
    return pair_st (gF_st, log2st Log.log);
  }

  proc setState(st : state_t) = {
    var gF_st, log_st;
    (gF_st, log_st) <- unpair_st st;
    F.setState(gF_st);
    Log.log <- st2log log_st;
  }

  proc run(q_j_log : query_t * int * (log_t list)) : out_t * (log_t list) = {
    var q, o, log, log', sts, j;
    (q, j, log) <- q_j_log;
    (o, log', sts) <@ SplitForker(I, F).snd(q, j + 1);
    log <- log ++ log';
    return (o, log);
  }
}.

local lemma wrapper_rewindable :
  exists (f : glob RewindWrapper(I, F) -> state_t), injective f /\
  (forall &m, Pr[RewindWrapper(I, F).getState() @ &m : (glob RewindWrapper(I, F)) = (glob RewindWrapper(I, F)){m} /\ res = f (glob RewindWrapper(I, F)){m}] = 1%r) /\
  (forall &m st (x: glob RewindWrapper(I, F)), st = f x => Pr[RewindWrapper(I, F).setState(st) @ &m : glob RewindWrapper(I, F) = x] = 1%r) /\
  islossless RewindWrapper(I, F).setState.
proof.
elim (Rewinding.RW.rewindable_A F F_rewindable).
move => gF2st [gF2st_inj [F_get_st_prop [F_set_st_prop F_set_st_ll]]].
exists (fun (gWrap : glob RewindWrapper(I, F)) => pair_st (gF2st gWrap.`1, log2st gWrap.`2)) => /=.
do split.
+ smt(pair_st_inj log2st_inj).
+ move => &m.
  byphoare (_ : (glob RewindWrapper(I, F)) = (glob RewindWrapper(I, F)){m} ==> _) => //.
  proc.
  call (F_get_st_prop (glob F){m}) => //.
+ move => &m st gWrap st_pair_eq.
  byphoare (_ : arg = st ==> _) => //.
  proc.
  wp.
  call (F_set_st_prop gWrap.`1).
  auto => />.
  smt(pair_st_can log2st_can).
islossless.
qed.

local module InitRewinder(I : IGen, F : Forkable) =
  Rewinding.QQ(RewindWrapper(I, F), InitWrapper(I, F)).

local equiv rewinder_run_equiv :
  InitRewinder(I, F).main_run ~ SplitForker(I, F).fst :
  ={glob I, glob F} /\ arg{1} + 1 = arg{2}  ==>
  ={glob I, glob F} /\ res{1}.`2 = (res{2}.`1, res{2}.`2).
proof.
proc => /=.
inline InitWrapper RewindWrapper.
wp.
call (_ : ={glob F}); 1: sim.
wp.
call (_ : ={glob I, glob F}); 1: sim.
auto => />.
qed.

local lemma main_run_equiv j log0 :
  0 <= j < Q =>
  equiv[
    IRunner(I, F, Log(FRO)).run ~ InitRewinder(I, F).main_run :
    ={glob I, glob F} /\ arg{2} = j /\ Log.log{1} = log0 ==>
    ={glob I} /\ res{1} = res{2}.`2.`1 /\ Log.log{1} = log0 ++ res{2}.`2.`2
  ].
proof.
move => j_range.
transitivity
  IForker(I, F).fst
  (={glob I, glob F} /\ Log.log{1} = log0 ==> ={glob I} /\ res{1} = res{2}.`1 /\ Log.log{1} = log0 ++ res{2}.`2)
  (={glob I, glob F} /\ arg{2} = j ==> ={glob I} /\ res{1}.`1 = res{2}.`2.`1 /\ res{1}.`2 = res{2}.`2.`2);
1,2: smt().
+ by symmetry; conseq (fst_run_log_equiv log0).
transitivity
  SplitForker(I, F).fst
  (={glob I, glob F} /\ arg{2} = j + 1 ==> ={glob I, res})
  (={glob I, glob F} /\ arg{1} = arg{2} + 1 ==> ={glob I} /\ res{1}.`1 = res{2}.`2.`1 /\ res{1}.`2 = res{2}.`2.`2).
+ move => &1 &2 rel.
  exists (glob F){1} (glob I){1} (j + 1) => /#.
+ smt().
+ conseq (fst_split_equiv (j + 1) _) => /#.
symmetry; conseq rewinder_run_equiv => /#.
qed.

local lemma pr_wrapper_run &m j :
  0 <= j < Q =>
  Pr[IRunner(I, F, FRO).run() @ &m : res.`1 = j] =
  Pr[InitRewinder(I, F).main_run(j) @ &m : res.`2.`1.`1 = j].
proof.
move => j_range.
byequiv => //.
proc *.
rewrite equiv [{1} 1 (irunner_log_equiv I F)].
exlim (Log.log{1}) => log0.
call (main_run_equiv j log0).
auto.
qed.

(* TODO: This proof really needs some refactoring... *)
local lemma init_rew_split_equiv j :
  0 <= j < Q =>
  equiv[
    SplitForker(I, F).run2 ~ InitRewinder(I, F).main :
    ={glob I, glob F, arg} /\ arg{1} = j ==>
    (* FIXME: Consider changing the return type of SplitForker.run2 *)
    let (j1, j2, a1, a2, log1, log2) = res{1} in
    ={glob I} /\ ((j1, a1), log1) = res{2}.`1.`2 /\ ((j2, a2), log2) = res{2}.`2.`2
  ].
proof.
move => j_range.
proc => /=.
inline InitWrapper RewindWrapper SplitForker(I, F).fst.
wp.
call (_ : ={glob F}); 1: sim.
wp.
call (_ : true).
wp => /=.
conseq (_ : _ ==>
  ={glob I, glob F, o} /\
  nth witness (sts10{1} ++ sts2{1}) j = (unpair_st s{2}).`1 /\
  ((nth witness (log10{1} ++ log20{1}) j).`1, j, take j (log10{1} ++ log20{1})) = r0{2} /\
  log10{1} = log0{2} /\ log20{1} = log'{2}
); 1: smt().
seq 2 3 : (={glob I, glob F} /\ C{1} = j + 1 /\ (q0{1}, j, log10{1}) = r0{2} /\
  size log10{1} = j /\ size sts10{1} = j).
+ wp.
  call (_ : ={glob I, glob F, arg} /\ arg{1} = j + 1 ==> ={glob I, glob F, res} /\ size res{1}.`2 = j /\ size res{1}.`3 = j).
  + proc.
    while (={glob I, glob F, q, Log.log, sts, c, C} /\ c{1} <= C{1} /\ size Log.log{1} + 1 = c{1} /\ size sts{1} + 1 = c{1}).
    + wp. call (_ : true). inline. wp. rnd. wp. call (_ : true). skip => />. smt(size_cat).
    wp. call (_ : true). wp. call (_ : true). wp. skip => /#.
  wp. skip => />.

(* TODO: Try to redefine the Forkers/Runner so that there is no oracle
 * call after the while loop. This way we could perhaps avoid some of
 * the case analysis? *)
inline SplitForker(I, F).snd Log.
conseq (_ : _ ==> ={glob I, glob F, o} /\
  head witness sts2{1} = (unpair_st s{2}).`1 /\
  ((head witness log20{1}).`1, j, log10{1}) = r0{2} /\
  log10{1} = log0{2} /\ log20{1} = log'{2}
).
+ move => />.
  smt(nth0_head nth_cat take_size_cat).
swap {2} [1..2] 5.
sp.
wp.
call (_ : true).
wp.
call (_ : true); 1: sim.
wp.
case (j = Q - 1).
+ rcondf {1} 1.
  + move => &n. skip. smt().
  rcondf {2} 4.
  + move => &n. wp. call (_ : true). skip. smt().
  wp.
  ecall {2} (get_st_preserves_glob (glob F){1}).
  wp.
  call (_ : true).
  skip => />.
  smt(pair_st_can).

unroll {1} 1. unroll {2} 4.
rcondt {1} 1.
+ move => &n. skip. smt().
rcondt {2} 4.
+ move => &n. wp. call (_ : true). skip. smt().
call (_ : true).
while (
  ={glob I, glob F, c, Log.log} /\ q1{1} = q2{2} /\
  head witness sts0{1} = (unpair_st s{2}).`1 /\ sts0{1} <> [] /\
  ((head witness Log.log{1}).`1, j, log0{2}) = r0{2} /\ Log.log{1} <> []
).
+ wp. call (_ : true). wp. call (_ : true). sim. wp. call (_ : true). skip => /#.
wp. call (_ : true). wp. call (_ : true). sim. wp.
ecall {2} (get_st_preserves_glob (glob F){1}).
wp.
call (_ : true).
skip => />.
smt(head_cons pair_st_can).
qed.

local lemma pr_wrapper_main &m j :
  0 <= j < Q =>
  Pr[SplitForker(I, F).run2(j) @ &m : res.`1 = j /\ res.`2 = j] =
  Pr[InitRewinder(I, F).main(j) @ &m : res.`1.`2.`1.`1 = j /\ res.`2.`2.`1.`1 = j].
proof.
move => j_range.
byequiv (init_rew_split_equiv j j_range) => /#.
qed.

local lemma split_fst_partial_ll : islossless SplitForker(I, F).fst_partial.
proof.
islossless; first last.
+ exact F_init_ll.
+ exact I_gen_ll.
while (true) (C - c); 2: auto => /#.
move => v.
wp.
call F_continue_ll.
call (_ : true); 1: islossless.
wp.
call get_st_ll.
skip => /#.
qed.

local lemma split_snd_ll : islossless SplitForker(I, F).snd.
proof.
islossless.
+ apply F_finish_ll.
+ apply get_st_ll.
while (true) (Q - c); 2: auto => /#.
move => v.
wp.
call F_continue_ll.
wp.
call (_ : true); 1: islossless.
wp.
call get_st_ll.
skip => /#.
qed.

local lemma pr_fork_specific &m j :
  0 <= j < Q =>
  Pr[IForker(I, F).run() @ &m : IForker.j1 = j /\ IForker.j2 = j] >=
  Pr[IRunner(I, F, FRO).run() @ &m : res.`1 = j] ^ 2.
proof.
move => j_range.
rewrite pr_run1_eq //.
move : (pr_run2_ineq &m j).
apply ler_trans.
rewrite pr_wrapper_run //.
rewrite pr_wrapper_main //.
apply (Rewinding.rew_with_init
  (RewindWrapper(I, F)) (InitWrapper(I, F))
  _ _ wrapper_rewindable _ _
  &m (fun (r : (query_t * int * log_t list) * (out_t * log_t list)) => r.`2.`1.`1 = j)
).
(* FIXME: Why does the rewinding theory include these assumptions? *)
+ sim.
+ sim.
+ proc.
  wp; call split_snd_ll; auto.
proc.
call split_fst_partial_ll => //.
qed.

(* STEP 3:
 * In the previous steps, we disassembled the probability of a fork
 * into a sum and replaced each summand by a square.
 *
 * Now we need to assemble the sum of squares back into a single
 * event.
 *)

local lemma square_sum (n : int) (f : int -> real) :
  (1 <= n) =>
  (forall j, 0 <= j < n => 0%r <= f j) =>
  bigi predT (fun j => square (f j)) 0 n >= square (bigi predT f 0 n) / n%r.
proof.
move => n_ge0 elem_ge0.
move : (Jensen_fin [0..n - 1] f square (finite_dinter 0 (n - 1)) (dinter_ll 0 (n - 1) _) square_convex); 1: smt().
rewrite ! fin_expE; 1,2: by apply finite_dinter.
rewrite /(\o).
rewrite ! (eq_big_perm _ _ (to_seq (support [0..n - 1])) (range 0 n)); 1,2: apply perm_eq_dinter.
rewrite (eq_big_seq _ (fun (j : int) => f j / n%r)).
+ smt(mem_range dinter1E).
rewrite (eq_big_seq (fun (x : int) => square (f x) * mu1 [0..n - 1] x) (fun (j : int) => square (f j) / n%r)).
+ smt(mem_range dinter1E).
rewrite - !  mulr_suml.
pose s := bigi predT f 0 n.
pose s2 :=  bigi predT (fun (i : int) => square (f i)) 0 n.
have -> : forall (x y : real), square (x * y) = y * square x * y.
+ move => x y.
  smt(mulrC expr2).
rewrite ler_pmul2r => /#.
qed.

(* STEP 4:
 * Put all the pieces together.
 *)

lemma pr_fork_success &m :
  let pr_runner_succ = Pr[IRunner(I, F, FRO).run() @ &m : success res.`1] in
  let pr_fork_succ   = Pr[IForker(I, F).run() @ &m : success res.`1] in
  pr_fork_succ >= pr_runner_succ ^ 2 / Q%r - pr_runner_succ * pr_collision.
proof.
simplify.
rewrite fork_pr.
move : (pr_split &m).
apply ler_trans.
apply ler_sub; first last.
+ apply pr_succ_resp_eq.
rewrite pr_split_sum.
rewrite pr_succ_sum.
have : bigi predT (fun (j : int) => Pr[IRunner(I, F, FRO).run() @ &m : res.`1 = j] ^ 2) 0 Q <=
  bigi predT (fun (j : int) => Pr[IForker(I, F).run() @ &m : IForker.j1 = j /\ IForker.j2 = j]) 0 Q.
+ apply ler_sum_seq.
  move => j j_range _ /=.
  apply pr_fork_specific.
  smt(mem_range).
apply ler_trans.
apply square_sum.
+ smt(Q_pos).
smt(ge0_mu).
qed.

section PROPERTY_TRANSFER.

(* In this section, we show that if the result of running F with FRO
 * satisfies some property P_out, then this property also holds for
 * the two results produced by IForker (provided that it succeeds). *)

declare pred P_in : glob I * glob F.
declare pred P_out : glob I * out_t * (log_t list).

declare axiom run_prop :
  hoare[
    IRunner(I, F, Log(FRO)).run :
    P_in (glob I, glob F) /\ Log.log = [] ==>
    P_out (glob I, res, Log.log)
  ].

local hoare fst_run_prop :
  IForker(I, F).fst : P_in (glob I, glob F) ==> P_out (glob I, res.`1, res.`2).
proof.
conseq (fst_run_log_equiv []) run_prop => /#.
qed.

local lemma snd_run_prop_split :
  (forall j, 0 <= j < Q => hoare[IForker(I, F).run : P_in (glob I, glob F) ==> res.`1 = j => P_out (glob I, (res.`1, res.`3), IForker.log2)]) =>
  hoare[IForker(I, F).run : P_in (glob I, glob F) ==> success res.`1 => P_out (glob I, (res.`1, res.`3), IForker.log2)].
proof.
have snd_forall :
  forall n, 0 <= n =>
  (forall j, 0 <= j < n => hoare[IForker(I, F).run : P_in (glob I, glob F) ==> res.`1 = j => P_out (glob I, (res.`1, res.`3), IForker.log2)]) =>
  hoare[IForker(I, F).run : P_in (glob I, glob F) ==> 0 <= res.`1 < n => P_out (glob I, (res.`1, res.`3), IForker.log2)].
+ apply ge0ind => /=.
  + smt().
  + move => _.
    by conseq (_ : _ ==> true); 1: smt().
  move => n n_ge0 ind _ ass.
  conseq
    (_ : _ ==> 0 <= res.`1 < n => P_out (glob I, (res.`1, res.`3), IForker.log2))
    (_ : _ ==>      res.`1 = n => P_out (glob I, (res.`1, res.`3), IForker.log2)) => //.
  + smt().
  + apply (ass n).
    smt().
  apply ind => //.
  smt().
rewrite /success.
apply snd_forall.
smt(Q_pos).
qed.

(* NOTE: This lemma could have been used above to show this inequality:
 *   Pr[SplitForker(F).run1(i, j) @ &m : res.`1 = j /\ res.`2 = j] >=
 *   Pr[SplitForker(F).run2(i, j) @ &m : res.`1 = j /\ res.`2 = j].
 * However, here we need to assume losslessness of F.continue & F.finish. (TODO: Or do we?)
 * For this reason, we prefer the approach using the byupto tactic. *)
local lemma run1_run2_equiv j0 :
  0 <= j0 < Q =>
  equiv[
    SplitForker(I, F).run1 ~ SplitForker(I, F).run2 :
    ={glob I, glob F, arg} /\ arg{1} = j0 ==>
    res{1}.`1 = res{2}.`1 /\ (res{1}.`1 = j0 => ={glob I, glob F, res})
  ].
proof.
move => j0_range.
proc => /=.
seq 3 3 : (={glob I, glob F, j, j1, a1, o1, log1, sts1} /\ j{1} = j0).
+ wp.
  call (_ : ={glob I, glob F}).
  + sim; auto.
  auto.
case (j1{1} = j{1}).
+ sim.
  auto.
wp.
call {1} split_snd_ll; call {2} split_snd_ll.
call {1} set_st_ll; call {2} set_st_ll.
auto => />.
qed.

local equiv init_rew_snd_equiv :
  InitRewinder(I, F).main ~ InitRewinder(I, F).main_run :
  ={glob I, glob F, arg} ==> ={glob I} /\ res{1}.`2 = res{2}.
proof.
proc => /=.
call (_ : ={glob F}); 1: sim.
inline RewindWrapper(I, F).getState RewindWrapper(I, F).setState.
elim F_rewindable => enc_glob [_ [get_st_pr [set_st_pr set_st_ll]]].
have set_st_ph : forall gF,
  phoare[F.setState : arg = enc_glob gF ==> (glob F) = gF] = 1%r.
+ move => gF.
  bypr => &m.
  by apply set_st_pr.
wp.
ecall {1} (set_st_ph (glob F){2}).
inline RewindWrapper(I, F).run.
wp.
call {1} split_snd_ll.
wp.
have get_st_ph : forall gF,
  phoare[F.getState : (glob F) = gF ==> (glob F) = gF /\ res = enc_glob gF] = 1%r.
+ move => gF.
  bypr => &m.
  move => <-.
  by apply get_st_pr.
ecall {1} (get_st_ph (glob F){2}).
conseq (_ : _ ==> ={glob I, glob F, r0}) => //.
+ smt(pair_st_can).
sim.
qed.

local lemma snd_run_prop_single j0 :
  0 <= j0 < Q =>
  hoare[IForker(I, F).run : P_in (glob I, glob F) ==> res.`1 = j0 => P_out (glob I, (res.`1, res.`3), IForker.log2)].
proof.
move => j0_range.
conseq
  (_ : P_in (glob I, glob F) ==> IForker.j1 = j0 => P_out (glob I, (IForker.j2, res.`3), IForker.log2))
  (_ : _ ==> res.`1 = j0 => IForker.j1 = j0 /\ IForker.j2 = j0) => //.
+ smt().
+ proc.
  seq 9 : true => //.
  auto => /#.
conseq (run_run1_equiv j0 j0_range)
  (_ : P_in (glob I, glob F) /\ arg = j0 ==> res.`1 = j0 => P_out (glob I, (res.`2, res.`4), res.`6)).
+ smt().
+ smt().
conseq (run1_run2_equiv j0 j0_range)
  (_ : P_in (glob I, glob F) /\ arg = j0 ==> P_out (glob I, (res.`2, res.`4), res.`6)).
+ smt().
+ smt().
conseq (init_rew_split_equiv j0 j0_range)
  (_ : P_in (glob I, glob F) /\ arg = j0 ==> P_out (glob I, res.`2.`2.`1, res.`2.`2.`2)).
+ smt().
+ smt().
conseq init_rew_snd_equiv (_ : P_in (glob I, glob F) /\ arg = j0 ==> P_out (glob I, res.`2.`1, res.`2.`2)).
+ smt().
+ smt().
have main_run_equiv_rev :
  forall log0,
  equiv[
    InitRewinder(I, F).main_run ~ IRunner(I, F, Log(FRO)).run :
    ={glob I, glob F} /\ arg{1} = j0 /\ Log.log{2} = log0 ==>
    ={glob I} /\ res{1}.`2.`1 = res{2} /\ log0 ++ res{1}.`2.`2 = Log.log{2}
  ].
+ by move => log0; symmetry; conseq (main_run_equiv j0 log0 j0_range).
conseq (main_run_equiv_rev []) run_prop.
+ smt().
+ smt().
qed.

hoare property_transfer :
  IForker(I, F).run :
  P_in (glob I, glob F) ==>
  let (j, a1, a2) = res in success j =>
    P_out (glob I, (j, a1), IForker.log1) /\ P_out (glob I, (j, a2), IForker.log2).
proof.
conseq
  (_ : _ ==> success res.`1 => P_out (glob I, (res.`1, res.`3), IForker.log2))
  (_ : _ ==> success res.`1 => P_out (glob I, (res.`1, res.`2), IForker.log1)) => //.
+ smt().
+ proc => /=.
  seq 9 : (P_out (glob I, (IForker.j1, a1), IForker.log1)); first last.
  + auto => /#.
  wp; call (_ : true) => //; call (_ : true); wp.
  call fst_run_prop.
  skip => /#.
apply snd_run_prop_split.
apply snd_run_prop_single.
qed.

end section PROPERTY_TRANSFER.

hoare success_log_props :
  IForker(I, F).run : true ==>
  let j = res.`1 in
  let (q1, r1) = nth witness IForker.log1 j in
  let (q2, r2) = nth witness IForker.log2 j in
    success j =>
      size IForker.log1 = Q /\ size IForker.log2 = Q /\
      take j IForker.log1 = take j IForker.log2 /\
      q1 = q2 /\ r1 <> r2.
proof.
conseq
  (_ : _ ==>
    let j = res.`1 in success j => size IForker.log1 = Q /\ size IForker.log2 = Q)
  (_ : _ ==>
    let j = res.`1 in
    let (q1, r1) = nth witness IForker.log1 j in
    let (q2, r2) = nth witness IForker.log2 j in
      success j => take j IForker.log1 = take j IForker.log2 /\ q1 = q2 /\ r1 <> r2);
1: smt(); first last.
+ conseq (property_transfer predT (fun (r : glob I * out_t * log_t list) => size r.`3 = Q) _); 1: smt().
  conseq (irun_log_size I F FRO).
proc.
wp.
have snd_head : forall q0, hoare[
  IForker(I, F).snd : q = q0 ==> (head witness res.`2).`1 = q0
].
+ move => q0.
  proc; inline Log.
  (* TODO: Again, reordering the instructions might help? *)
  case (Q <= c).
  + rcondf 2; auto; 1: smt().
    call (_ : true).
    wp.
    call (_ : true) => //.
    auto.
  unroll 2; rcondt 2; 1: auto => /#.
  call (_ : true) => /=.
  wp.
  call (_ : true) => //.
  wp.
  while ((head witness Log.log).`1 = q0 /\ Log.log <> []).
  + wp; call (_ : true); wp; call (_ : true) => //; wp.
    skip.
    smt(head_cons).
  wp; call (_ : true); wp; call (_ : true) => //.
  auto.
  smt(head_cons).
ecall (snd_head q).
call (_ : true).
wp.
call fst_log_size.
skip.
smt(take_catl take_take size_take nth_cat nth0_head).
qed.

section CONVENIENCE.

(* Here we just combine all results we have into a (hopefully)
 * more usable package. *)

declare pred P_in : glob I * glob F.
declare pred P_out : glob I * out_t * (log_t list).

declare axiom success_impl :
  hoare[
    IRunner(I, F, Log(FRO)).run :
    P_in (glob I, glob F) /\ Log.log = [] ==>
    success res.`1 => P_out (glob I, res, Log.log)
  ].

declare op pr_success : real.

declare axiom success_eq :
  phoare[IRunner(I, F, FRO).run : P_in (glob I, glob F) ==> success res.`1] = pr_success.

lemma forking_lemma :
  phoare[
    IForker(I, F).run :
    P_in (glob I, glob F) ==>
    let (j, a1, a2) = res in
    let log1 = IForker.log1 in
    let log2 = IForker.log2 in
    let (q1, r1) = nth witness log1 j in
    let (q2, r2) = nth witness log2 j in
    success j /\
    size log1 = Q /\ size log2 = Q /\
    take j log1 = take j log2 /\ q1 = q2 /\ r1 <> r2 /\
    P_out (glob I, (j, a1), log1) /\ P_out (glob I, (j, a2), log2)
  ] >= (pr_success ^ 2 / Q%r - pr_success * pr_collision).
proof.
conseq (_ : _ ==> success res.`1) (_ : _ ==>
  success res.`1 =>
    let (j, a1, a2) = res in
    let log1 = IForker.log1 in
    let log2 = IForker.log2 in
    let (q1, r1) = nth witness log1 j in
    let (q2, r2) = nth witness log2 j in
    size log1 = Q /\ size log2 = Q /\
    take j log1 = take j log2 /\ q1 = q2 /\ r1 <> r2 /\
    P_out (glob I, (j, a1), log1) /\ P_out (glob I, (j, a2), log2)).
+ trivial.
+ smt().
+ pose P_out' := fun (ol : glob I * out_t * (log_t list)) => success ol.`2.`1 => P_out ol.
  conseq success_log_props (property_transfer P_in P_out' success_impl) => /#.
bypr => &m P_in_arg /=.
have -> : pr_success = Pr[IRunner(I, F, FRO).run() @ &m : success res.`1].
+ by byphoare (_ : (glob I, glob F) = (glob I, glob F){m} /\ arg = arg{m} ==> _) => //; conseq success_eq.
apply (pr_fork_success &m).
qed.

end section CONVENIENCE.

end section PROOF.
