(* Forking lemma - proof sketch
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

(* FIXME: Properly import Rewindable form easycrypt-rewinding. *)
type state_t.

module type Rewindable = {
  proc getState() : state_t
  proc setState(st : state_t) : unit
}.

(* Auxiliary output type. *)
type aux_t.

clone import Stopping as ForkStopping with
  type out_t <= int * aux_t.
(* TODO: Why is this not imported as well? *)
type out_t = int * aux_t.

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

module Forker(F : Forkable) = {
  (* TODO: Might be easier to prove invariants about these if we
   * keep them local? In such case, we would need to return
   * those in run to be able to refer to the results.
   * Check the proofs! *)
  var j1, j2 : int
  var log1, log2 : log_t list
  var r1, r2 : resp_t

  (* First run of F, with query and state logging. *)
  proc fst(i : in_t) : out_t * (log_t list) * (state_t list) = {
    var sts : state_t list;
    var st : state_t;
    var o : out_t;
    var q : query_t;
    var r : resp_t;
    var c : int;

    sts <- [];
    Log.log <- [];

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
    var log : log_t list;
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

  proc run(i : in_t) : int * aux_t * aux_t = {
    var sts : state_t list;
    var st : state_t;
    var o1, o2 : out_t;
    var j : int;
    var a1, a2 : aux_t;
    var q : query_t;

    (o1, log1, sts) <@ fst(i);
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

declare module F <: Forkable {-FRO, -Log, -Runner, -Forker}.

(* Coppied from easycrypt-rewinding. *)
declare axiom F_rewindable :
  exists (f : glob F -> state_t), injective f /\
  (forall &m, Pr[F.getState() @ &m : (glob F) = (glob F){m} /\ res = f (glob F){m}] = 1%r) /\
  (forall &m st (x: glob F), st = f x => Pr[F.setState(st) @ &m : glob F = x] = 1%r) /\
  islossless F.setState.

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

local lemma fork_pr i &m :
  Pr[Forker(F).run(i) @ &m : success res.`1] =
  Pr[Forker(F).run(i) @ &m : Forker.j1 = Forker.j2 /\ success Forker.j1 /\ Forker.r1 <> Forker.r2].
proof.
byequiv => //.
proc.
seq 9 9 : (={glob Forker}).
+ sim.
auto => /#.
qed.

local lemma pr_split i &m :
  Pr[Forker(F).run(i) @ &m : Forker.j1 = Forker.j2 /\ success Forker.j1 /\ Forker.r1 <> Forker.r2] >=
  Pr[Forker(F).run(i) @ &m : Forker.j1 = Forker.j2 /\ success Forker.j1] -
  Pr[Forker(F).run(i) @ &m : success Forker.j1 /\ Forker.r1 = Forker.r2].
proof.
(* TODO: Cannot use occurence selector with rewrite Pr? *)
have -> :
  Pr[Forker(F).run(i) @ &m : Forker.j1 = Forker.j2 /\ success Forker.j1] =
  Pr[Forker(F).run(i) @ &m : Forker.j1 = Forker.j2 /\ success Forker.j1 /\ Forker.r1 = Forker.r2] +
  Pr[Forker(F).run(i) @ &m : Forker.j1 = Forker.j2 /\ success Forker.j1 /\ Forker.r1 <> Forker.r2].
+ by rewrite Pr[mu_split Forker.r1 = Forker.r2]; smt().
have ABC_le_BC :
  Pr[Forker(F).run(i) @ &m : Forker.j1 = Forker.j2 /\ success Forker.j1 /\ Forker.r1 = Forker.r2] <=
  Pr[Forker(F).run(i) @ &m : success Forker.j1 /\ Forker.r1 = Forker.r2].
+ by rewrite Pr[mu_sub].
smt().
qed.

local equiv fst_run_log_equiv log0 :
  Forker(F).fst ~ Runner(F, Log(FRO)).run :
  ={arg, glob F} /\ Log.log{2} = log0 ==>
  ={glob F} /\ res{1}.`1 = res{2} /\ log0 ++ res{1}.`2 = Log.log{2}.
proof.
proc => /=.
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
wp.
call (_ : true).
auto => />.
smt(cats0).
qed.

local equiv fst_run_equiv :
  Forker(F).fst ~ Runner(F, FRO).run :
  ={arg, glob F} ==> ={glob F} /\ res{1}.`1 = res{2}.
proof.
proc *.
rewrite equiv [{2} 1 (runner_log_equiv F)].
exlim (Log.log{2}) => log0.
call (fst_run_log_equiv log0).
auto.
qed.

local hoare fst_log_size :
  Forker(F).fst : true ==> size res.`2 = Q.
proof.
conseq (fst_run_log_equiv []) (run_log_size F FRO) => /#.
qed.

(* TODO: Decompose? *)
local lemma pr_succ_resp_eq &m i :
  Pr[Forker(F).run(i) @ &m : success Forker.j1 /\ Forker.r1 = Forker.r2] <=
  Pr[Runner(F, FRO).run(i) @ &m : success res.`1] * (1%r / (size (to_seq (support dresp)))%r).
proof.
pose inv_supp_size := 1%r / (size (to_seq (support dresp)))%r.
byphoare (: arg = i /\ glob F = (glob F){m} ==> _) => //.
proc.
seq 3 : (success Forker.j1)
  Pr[Runner(F, FRO).run(i) @ &m : success res.`1] inv_supp_size
  _ 0%r
  (size Forker.log1 = Q);
last by trivial.

(* #pre ==> size Forker.log1 = Q *)
+ wp.
  call fst_log_size.
  auto.

(* #pre ==> success Forker.j1 *)
+ wp.
  call (_ : glob F = (glob F){m} /\ arg = i ==> success res.`1.`1).
  + bypr => &m0 glob_eq.
    byequiv => //.
    conseq fst_run_equiv; smt().
  auto.

(* success Forker.j1 ==> #post *)
+ inline.
  wp.
  conseq (_ : _ ==> success Forker.j1 /\ Forker.r1 = (head witness Log.log).`2).
  + smt(nth_cat size_takel nth0_head).
  (* FIXME: This is rather painful. Call doesn't work in pHL? *)
  seq 12 : (success Forker.j1 /\ Forker.r1 = (head witness Log.log).`2)
    inv_supp_size 1%r
    _ 0%r;
  1,3,5: trivial; first last.
  + hoare; call (_ : true); auto.
  wp.
  have mu_dresp_eq :
    forall r0, mu dresp (fun r => r0 = r) <= inv_supp_size.
  + move => r0.
    have -> : (fun r => r0 = r) = pred1 r0 by smt().
    rewrite (mu1_uni_ll _ _ dresp_uni dresp_ll).
    smt(invr_ge0 size_ge0).
  case (Forker.j1 = Q - 1).
  (* case: Forker.j1 = Q*)
  + rcondf 6.
    + wp; call (_ : true); auto.
    rnd; wp => /=.
    call (_ : true); auto.
    move => &hr [[_ succ] _].
    rewrite succ /=.
    apply mu_dresp_eq.
  (* case: Forker.j1 <> Q *)
  unroll 6; rcondt 6.
  + wp; call (_ : true); wp; skip => /#.
  seq 11 : (success Forker.j1 /\ Forker.r1 = (head witness Log.log).`2)
    inv_supp_size 1%r
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
  while (Log.log <> [] /\ ! (success Forker.j1 /\ Forker.r1 = (head witness Log.log).`2)).
  + wp; call (_ : true); wp; rnd; wp; skip => /#.
  wp; call (_ : true); skip => /#.

(* ! success Forker.j1 ==> #post *)
hoare.
conseq (_ : _ ==> ! success Forker.j1); 1: smt().
wp.
call (_ : true) => //.
call (_ : true).
auto.
qed.

(* FIXME: The following two lemmas are almost identical.
 * Try to extract the common bits into a separate lemma or
 * reuse the existing PrIntervalToSum (easycrypt-zk) theory. *)
local lemma pr_split_sum &m i :
  Pr[Forker(F).run(i) @ &m : Forker.j1 = Forker.j2 /\ success Forker.j1] =
  bigi predT (fun j => Pr[Forker(F).run(i) @ &m : Forker.j1 = j /\ Forker.j2 = j]) 0 Q.
proof.
rewrite /success.
have -> :
  forall n, 0 <= n =>
  Pr[Forker(F).run(i) @ &m : Forker.j1 = Forker.j2 /\ 0 <= Forker.j1 && Forker.j1 < n] =
  bigi predT (fun j => Pr[Forker(F).run(i) @ &m : Forker.j1 = j /\ Forker.j2 = j]) 0 n;
[idtac | smt(Q_pos) | trivial].
apply ge0ind => /=.
+ smt().
+ rewrite big_geq => //.
  have -> /= : forall x, (0 <= x < 0) = false by smt().
  by rewrite Pr[mu_false].
move => n n_ge0 ind _.
rewrite big_int_recr //=.
rewrite Pr[mu_split Forker.j1 < n].
have -> : forall b x, ((b /\ 0 <= x < n + 1) /\ x < n) <=> (b /\ 0 <= x < n) by smt().
rewrite ind //.
have -> // : forall j1 j2, ((j1 = j2 /\ 0 <= j1 < n + 1) /\ ! j1 < n) <=> (j1 = n /\ j2 = n) by smt().
qed.

local lemma pr_succ_sum &m i:
  Pr[Runner(F, FRO).run(i) @ &m : success res.`1] =
  bigi predT (fun j => Pr[Runner(F, FRO).run(i) @ &m : res.`1 = j]) 0 Q.
proof.
rewrite /success.
have -> :
  forall n, 0 <= n =>
  Pr[Runner(F, FRO).run(i) @ &m : 0 <= res.`1 < n] =
  bigi predT (fun j => Pr[Runner(F, FRO).run(i) @ &m : res.`1 = j]) 0 n;
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
 * Pr[Forker(F).run(i) @ &m : Forker.j1 = j /\ Forker.j2 = j].
 *
 * The key observation is that we can replace Forker by a module,
 * that always forks after the j-th query and the probability
 * does not change.
 *
 * Then, after fixing the forking point, it is easy to transform
 * the module into the shape required by the rew_with_init lemma.
 *)

local module SplitForker(F : Forkable) = {
  var bad : bool

  (* Forker.fst that runs F only until the first C queries. *)
  proc fst_partial(i : in_t, C : int) : query_t * (log_t list) * (state_t list) = {
    var sts : state_t list;
    var st : state_t;
    var o : out_t;
    var q : query_t;
    var r : resp_t;
    var c : int;

    sts <- [];
    Log.log <- [];

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

  (* Same as Forker.snd, but with state recording. *)
  (* TODO: Consider adding state recording to Forker.snd. *)
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

  proc fst(i : in_t, C : int) : out_t * (log_t list) * (state_t list) = {
    var sts, sts1, sts2 : state_t list;
    var log, log1, log2 : log_t list;
    var q : query_t;
    var o : out_t;

    (q, log1, sts1) <@ fst_partial(i, C);
    (o, log2, sts2) <@ snd(q, C);
    sts <- sts1 ++ sts2;
    log <- log1 ++ log2;

    return (o, log, sts);
  }

  (* Forker.run with bad event logging, with some unnecessary bits removed
   * (e.g., we don't care about aux output nor the two responses to q) *)
  proc run1(i : in_t, j : int) : int * int * aux_t * aux_t * (log_t list) * (log_t list) = {
    var sts1, _sts2 : state_t list;
    var st : state_t;
    var log1, log2 : log_t list;
    var o1, o2 : out_t;
    var j1, j1', j2 : int;
    var a1, a2 : aux_t;
    var q : query_t;

    (o1, log1, sts1) <@ fst(i, j + 1);
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
  proc run2(i : in_t, j : int) : int * int * aux_t * aux_t * (log_t list) * (log_t list) = {
    var sts1, _sts2 : state_t list;
    var st : state_t;
    var log1, log2 : log_t list;
    var o1, o2 : out_t;
    var j1, j1', j2 : int;
    var a1, a2 : aux_t;
    var q : query_t;

    (o1, log1, sts1) <@ fst(i, j + 1);
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
    Forker(F).fst ~ SplitForker(F).fst :
    ={glob F} /\ arg{1} = arg{2}.`1 /\ arg{2}.`2 = C ==> ={glob F, res}
  ].
proof.
move => C_range.
proc.
inline SplitForker(F).fst_partial SplitForker(F).snd Log.
wp.
call (_ : true).
wp.
call (_ : true); 1: auto.
wp.
call (_ : true).
splitwhile{1} 5 : c < C.
conseq (_ : _ ==> ={glob F} /\ q{1} = q1{2} /\ Log.log{1} = log1{2} ++ Log.log{2} /\ sts{1} = sts1{2} ++ sts3{2}) => />.
+ smt(catA).
while (={glob F} /\ q{1} = q1{2} /\ Log.log{1} = log1{2} ++ Log.log{2} /\ sts{1} = sts1{2} ++ sts3{2} /\ c{1} = c0{2}).
+ wp. call (_ : true). wp. call (_ : true). auto. wp. call (_ : true). skip => />. smt(catA).
wp.
conseq (_ : _ ==> ={glob F} /\ q{1} = q0{2} /\ Log.log{1} = Log.log{2} /\ sts{1} = sts0{2} /\ c{1} = C) => />.
+ smt(cats0).
while (={glob F} /\ q{1} = q0{2} /\ Log.log{1} = Log.log{2} /\ sts{1} = sts0{2} /\ c{1} = c{2} /\ c{1} <= C /\ C0{2} = C).
+ wp. call (_ : true). wp. call (_ : true). auto. wp. call (_ : true). skip => />. smt().
wp.
call (_ : true).
auto => /#.
qed.

local equiv snd_equiv :
  Forker(F).snd ~ SplitForker(F).snd :
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
    Forker(F).run ~ SplitForker(F).run1 :
    ={glob F} /\ (arg{1}, j) = arg{2} ==>
    ={glob F} /\ Forker.j1{1} = res{2}.`1 /\ Forker.j2{1} = res{2}.`2 /\
      res{1}.`2 = res{2}.`3 /\ res{1}.`3 = res{2}.`4 /\
      Forker.log1{1} = res{2}.`5 /\ Forker.log2{1} = res{2}.`6
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

local lemma pr_run1_eq &m i j :
  0 <= j < Q =>
  Pr[Forker(F).run(i) @ &m : Forker.j1 = j /\ Forker.j2 = j] =
  Pr[SplitForker(F).run1(i, j) @ &m : res.`1 = j /\ res.`2 = j].
proof.
move => j_range.
byequiv => //.
conseq (run_run1_equiv j j_range); smt().
qed.

(* TODO: Try to prove this using pRHL, i.e., without using
 * the syntactic byupto tactic. *)
local lemma pr_run2_ineq &m i j :
  Pr[SplitForker(F).run1(i, j) @ &m : res.`1 = j /\ res.`2 = j] >=
  Pr[SplitForker(F).run2(i, j) @ &m : res.`1 = j /\ res.`2 = j].
proof.
have :
  Pr[SplitForker(F).run2(i, j) @ &m : res.`1 = j /\ res.`2 = j] <=
    Pr[SplitForker(F).run1(i, j) @ &m : res.`1 = j /\ res.`2 = j] +
  Pr[SplitForker(F).run2(i, j) @ &m : (res.`1 = j /\ res.`2 = j) /\ SplitForker.bad].
+ byupto.
have -> :
  Pr[SplitForker(F).run2(i, j) @ &m : (res.`1 = j /\ res.`2 = j) /\ SplitForker.bad] = 0%r.
+ byphoare (_ : arg.`2 = j ==> _) => //.
  hoare.
  proc => /=.
  conseq (_ : _ ==> !(j1 = j /\ SplitForker.bad)); 1: smt().
  wp; do 3! (call (_ : true) => //; wp).
trivial.
qed.

(* Need to transform SplitForker.run2 into a form
 * that is suitable for application of the rew_with_init lemma. *)

local module RewindWrapper(F : Forkable) = {

  (* FIXME: Need to handle bad var in SplitForker and
   * show that this module is rewindable. *)
  proc getState() : state_t = {
    var st;
    st <@ F.getState();
    return st;
  }

  proc setState(st : state_t) = {
    F.setState(st);
  }

  proc init(ij : in_t * int) : query_t * int * (log_t list) = {
    var i, j, q, log, sts;
    (i, j) <- ij;
    (q, log, sts) <@ SplitForker(F).fst_partial(i, j + 1);
    return (q, j, log);
  }

  proc run(q_j_log : query_t * int * (log_t list)) : out_t * (log_t list) = {
    var q, o, log, log', sts, j;
    (q, j, log) <- q_j_log;
    (o, log', sts) <@ SplitForker(F).snd(q, j + 1);
    log <- log ++ log';
    return (o, log);
  }
}.

(* This matches the QQ module in easycrypt-rewinding. *)
(* FIXME: Clone and instantiate RewWithInit.. *)
local type iat = in_t * int.
local module InitRewinder(F : Forkable) = {
  module A = RewindWrapper(F)
  module B = RewindWrapper(F)

  proc main(i:iat) = {
    var s, r0, r1, r2;
    r0 <@ B.init(i);
    s <@ A.getState();
    r1 <@ A.run(r0);
    A.setState(s);
    r2 <@ A.run(r0);
    return ((r0,r1), (r0, r2));
  }

  proc main_run(i:iat) = {
    var r, r0;
    r0 <@ B.init(i);
    r <@ A.run(r0);
    return (r0, r);
  }
}.

local equiv rewinder_run_equiv :
  InitRewinder(F).main_run ~ SplitForker(F).fst :
  ={glob F} /\ arg{1}.`1 = arg{2}.`1 /\ arg{1}.`2 + 1 = arg{2}.`2  ==>
  ={glob F} /\ res{1}.`2 = (res{2}.`1, res{2}.`2).
proof.
proc => /=.
inline InitRewinder.
wp.
call (_ : ={glob F}); 1: sim.
wp.
call (_ : ={glob F}); 1: sim.
auto => />.
qed.

local lemma main_run_equiv j log0 :
  0 <= j < Q =>
  equiv[
    Runner(F, Log(FRO)).run ~ InitRewinder(F).main_run :
    ={glob F} /\ (arg{1}, j) = arg{2} /\ Log.log{1} = log0 ==>
    res{1} = res{2}.`2.`1 /\ Log.log{1} = log0 ++ res{2}.`2.`2
  ].
proof.
move => j_range.
transitivity
  Forker(F).fst
  (={glob F, arg} /\ Log.log{1} = log0 ==> res{1} = res{2}.`1 /\ Log.log{1} = log0 ++ res{2}.`2)
  (={glob F} /\ (arg{1}, j) = arg{2} ==> res{1}.`1 = res{2}.`2.`1 /\ res{1}.`2 = res{2}.`2.`2);
1,2: smt().
+ by symmetry; conseq (fst_run_log_equiv log0).
transitivity
  SplitForker(F).fst
  (={glob F} /\ (arg{1}, j + 1) = arg{2} ==> ={res})
  (={glob F} /\ arg{1}.`1 = arg{2}.`1 /\ arg{1}.`2 = arg{2}.`2 + 1 ==> res{1}.`1 = res{2}.`2.`1 /\ res{1}.`2 = res{2}.`2.`2).
+ move => &1 &2 rel.
  exists (glob F){1} (arg{1}, j + 1) => /#.
+ smt().
+ conseq (fst_split_equiv (j + 1) _) => /#.
symmetry; conseq rewinder_run_equiv => /#.
qed.

local lemma pr_wrapper_run &m i j :
  0 <= j < Q =>
  Pr[Runner(F, FRO).run(i) @ &m : res.`1 = j] =
  Pr[InitRewinder(F).main_run((i, j)) @ &m : res.`2.`1.`1 = j].
proof.
move => j_range.
byequiv => //.
proc *.
rewrite equiv [{1} 1 (runner_log_equiv F)].
exlim (Log.log{1}) => log0.
call (main_run_equiv j log0).
auto.
qed.

local lemma init_rew_split_equiv j :
  0 <= j < Q =>
  equiv[
    SplitForker(F).run2 ~ InitRewinder(F).main :
    ={glob F, arg} /\ arg{1}.`2 = j ==>
    (* FIXME: Consider changing the return type of SplitForker.run2 *)
    let (j1, j2, a1, a2, log1, log2) = res{1} in
    ((j1, a1), log1) = res{2}.`1.`2 /\ ((j2, a2), log2) = res{2}.`2.`2
  ].
proof.
move => j_range.
proc => /=.
inline InitRewinder SplitForker(F).fst.
wp.
call (_ : ={glob F}); 1: sim.
wp.
call (_ : true).
wp => /=.
conseq (_ : _ ==>
  ={glob F, o} /\
  nth witness (sts10{1} ++ sts2{1}) j = s{2} /\
  ((nth witness (log10{1} ++ log20{1}) j).`1, j, take j (log10{1} ++ log20{1})) = r0{2} /\
  log10{1} = log0{2} /\ log20{1} = log'{2}
); 1: smt().
seq 3 4 : (={glob F} /\ C{1} = j + 1 /\ (q0{1}, j, log10{1}) = r0{2} /\
  size log10{1} = j /\ size sts10{1} = j).
+ wp.
  call (_ : ={glob F, arg} /\ arg{1}.`2 = j + 1 ==> ={glob F, res} /\ size res{1}.`2 = j /\ size res{1}.`3 = j).
  + proc.
    while (={glob F, q, Log.log, sts, c, C} /\ c{1} <= C{1} /\ size Log.log{1} + 1 = c{1} /\ size sts{1} + 1 = c{1}).
    + wp. call (_ : true). inline. wp. rnd. wp. call (_ : true). skip => />. smt(size_cat).
    wp. call (_ : true). wp. skip => /#.
  wp. skip => />.

(* TODO: Try to redefine the Forkers/Runner so that there is no oracle
 * call after the while loop. This way we could perhaps avoid some of
 * the case analysis? *)
inline SplitForker(F).snd Log.
conseq (_ : _ ==> ={glob F, o} /\
  head witness sts2{1} = s{2} /\
  ((head witness log20{1}).`1, j, log10{1}) = r0{2} /\
  log10{1} = log0{2} /\ log20{1} = log'{2}
).
+ move => />.
  smt(nth0_head nth_cat take_size_cat).
swap {2} [1..2] 6.
sp.
wp.
call (_ : true).
wp.
call (_ : true); 1: sim.
wp.
case (j = Q - 1).
+ rcondf {1} 1.
  + move => &n. skip. smt().
  rcondf {2} 3.
  + move => &n. wp. call (_ : true). skip. smt().
  wp.
  ecall {2} (get_st_preserves_glob (glob F){1}).
  wp.
  call (_ : true).
  skip => />.

unroll {1} 1. unroll {2} 3.
rcondt {1} 1.
+ move => &n. skip. smt().
rcondt {2} 3.
+ move => &n. wp. call (_ : true). skip. smt().
call (_ : true).
while (
  ={glob F, c, Log.log} /\ q1{1} = q2{2} /\
  head witness sts0{1} = s{2} /\ sts0{1} <> [] /\
  ((head witness Log.log{1}).`1, j, log0{2}) = r0{2} /\ Log.log{1} <> []
).
+ wp. call (_ : true). wp. call (_ : true). sim. wp. call (_ : true). skip => /#.
wp. call (_ : true). wp. call (_ : true). sim. wp.
ecall {2} (get_st_preserves_glob (glob F){1}).
wp.
call (_ : true).
skip => />.
smt(head_cons).
qed.

local lemma pr_wrapper_main &m i j :
  0 <= j < Q =>
  Pr[SplitForker(F).run2(i, j) @ &m : res.`1 = j /\ res.`2 = j] =
  Pr[InitRewinder(F).main((i, j)) @ &m : res.`1.`2.`1.`1 = j /\ res.`2.`2.`1.`1 = j].
proof.
move => j_range.
byequiv (init_rew_split_equiv j j_range) => /#.
qed.

local lemma pr_fork_specific &m i j :
  0 <= j < Q =>
  Pr[Forker(F).run(i) @ &m : Forker.j1 = j /\ Forker.j2 = j] >=
  Pr[Runner(F, FRO).run(i) @ &m : res.`1 = j] ^ 2.
proof.
move => j_range.
rewrite pr_run1_eq //.
move : (pr_run2_ineq &m i j).
apply ler_trans.
rewrite pr_wrapper_run //.
rewrite pr_wrapper_main //.
(* FIXME: Apply rew_with_init. *)
admit.
qed.

(* STEP 3:
 * In the previous steps, we disassembled the probability of a fork
 * into a sum and replaced each summand by a square.
 *
 * Now we need to assemble the sum of squares back into a single
 * event.
 *)

local op square (x : real) = x ^ 2.

local lemma square_convex : forall (a b : real), convex square a b.
proof.
(* FIXME: Import the lemma from easycrypt-rewinding. *)
admit.
qed.

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

lemma pr_fork_success &m i :
  let pr_runner_succ = Pr[Runner(F, FRO).run(i) @ &m : success res.`1] in
  let pr_fork_succ   = Pr[Forker(F).run(i) @ &m : success res.`1] in
  pr_fork_succ >= pr_runner_succ ^ 2 / Q%r - pr_runner_succ * (1%r / (size (to_seq (support dresp)))%r).
proof.
simplify.
rewrite fork_pr.
move : (pr_split i &m).
apply ler_trans.
apply ler_sub; first last.
+ apply pr_succ_resp_eq.
rewrite pr_split_sum.
rewrite pr_succ_sum.
have : bigi predT (fun (j : int) => Pr[Runner(F, FRO).run(i) @ &m : res.`1 = j] ^ 2) 0 Q <=
  bigi predT (fun (j : int) => Pr[Forker(F).run(i) @ &m : Forker.j1 = j /\ Forker.j2 = j]) 0 Q.
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
 * the two results produced by Forker (provided that it succeeds). *)

declare pred P_in : in_t.
declare pred P_out : out_t * (log_t list).

declare axiom run_prop :
  hoare[Runner(F, Log(FRO)).run : P_in i /\ Log.log = [] ==> P_out (res, Log.log)].

local hoare fst_run_prop :
  Forker(F).fst : P_in i ==> P_out (res.`1, res.`2).
proof.
conseq (fst_run_log_equiv []) (_ : P_in i /\ Log.log = [] ==> P_out (res, Log.log)) => //.
+ smt().
apply run_prop.
qed.

local lemma snd_run_prop_split :
  (forall j, 0 <= j < Q => hoare[Forker(F).run : P_in i ==> res.`1 = j => P_out ((res.`1, res.`3), Forker.log2)]) =>
  hoare[Forker(F).run : P_in i ==> success res.`1 => P_out ((res.`1, res.`3), Forker.log2)].
proof.
have snd_forall :
  forall n, 0 <= n =>
  (forall j, 0 <= j < n => hoare[Forker(F).run : P_in i ==> res.`1 = j => P_out ((res.`1, res.`3), Forker.log2)]) =>
  hoare[Forker(F).run : P_in i ==> 0 <= res.`1 < n => P_out ((res.`1, res.`3), Forker.log2)].
+ apply ge0ind => /=.
  + smt().
  + move => _.
    by conseq (_ : _ ==> true); 1: smt().
  move => n n_ge0 ind _ ass.
  conseq
    (_ : _ ==> 0 <= res.`1 < n => P_out ((res.`1, res.`3), Forker.log2))
    (_ : _ ==>      res.`1 = n => P_out ((res.`1, res.`3), Forker.log2)) => //.
  + smt().
  + apply (ass n).
    smt().
  apply ind => //.
  smt().
rewrite /success.
apply snd_forall.
smt(Q_pos).
qed.

local lemma split_snd_ll : islossless SplitForker(F).snd.
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

(* NOTE: This lemma could have been used above to show this inequality:
 *   Pr[SplitForker(F).run1(i, j) @ &m : res.`1 = j /\ res.`2 = j] >=
 *   Pr[SplitForker(F).run2(i, j) @ &m : res.`1 = j /\ res.`2 = j].
 * However, here we need to assume losslessness of F.continue & F.finish. (TODO: Or do we?)
 * For this reason, we prefer the approach using the byupto tactic. *)
local lemma run1_run2_equiv j0 :
  0 <= j0 < Q =>
  equiv[
    SplitForker(F).run1 ~ SplitForker(F).run2 :
    ={glob F, arg} /\ arg{1}.`2 = j0 ==>
    res{1}.`1 = res{2}.`1 /\ (res{1}.`1 = j0 => ={glob F, res})
  ].
proof.
move => j0_range.
proc => /=.
seq 3 3 : (={glob F, j, j1, a1, o1, log1, sts1} /\ j{1} = j0).
+ wp.
  call (_ : ={glob F}).
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
  InitRewinder(F).main ~ InitRewinder(F).main_run :
  ={glob F, arg} ==> res{1}.`2 = res{2}.
proof.
proc => /=.
call (_ : ={glob F}); 1: sim.
inline InitRewinder(F).A.getState InitRewinder(F).A.setState.
elim F_rewindable => enc_glob [_ [get_st_pr [set_st_pr set_st_ll]]].
have set_st_ph : forall gF,
  phoare[F.setState : arg = enc_glob gF ==> (glob F) = gF] = 1%r.
+ move => gF.
  bypr => &m.
  by apply set_st_pr.
ecall {1} (set_st_ph (glob F){2}).
inline InitRewinder(F).A.run.
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
conseq (_ : _ ==> ={glob F, r0}) => //.
sim.
qed.

local lemma snd_run_prop_single j0 :
  0 <= j0 < Q =>
  hoare[Forker(F).run : P_in arg ==> res.`1 = j0 => P_out ((res.`1, res.`3), Forker.log2)].
proof.
move => j0_range.
conseq
  (_ : P_in arg ==> Forker.j1 = j0 => P_out ((Forker.j2, res.`3), Forker.log2))
  (_ : _ ==> res.`1 = j0 => Forker.j1 = j0 /\ Forker.j2 = j0) => //.
+ smt().
+ proc.
  seq 9 : true => //.
  auto => /#.
conseq (run_run1_equiv j0 j0_range)
  (_ : P_in arg.`1 /\ arg.`2 = j0 ==> res.`1 = j0 => P_out ((res.`2, res.`4), res.`6)).
+ smt().
+ smt().
conseq (run1_run2_equiv j0 j0_range)
  (_ : P_in arg.`1 /\ arg.`2 = j0 ==> P_out ((res.`2, res.`4), res.`6)).
+ smt().
+ smt().
conseq (init_rew_split_equiv j0 j0_range)
  (_ : P_in arg.`1 /\ arg.`2 = j0 ==> P_out res.`2.`2).
+ smt().
+ smt().
conseq init_rew_snd_equiv (_ : P_in arg.`1 /\ arg.`2 = j0 ==> P_out res.`2).
+ smt().
+ smt().
have main_run_equiv_rev :
  forall log0,
  equiv[
    InitRewinder(F).main_run ~ Runner(F, Log(FRO)).run :
    ={glob F} /\ arg{1} = (arg{2}, j0) /\ Log.log{2} = log0 ==>
    res{1}.`2.`1 = res{2} /\ log0 ++ res{1}.`2.`2 = Log.log{2}
  ].
+ by move => log0; symmetry; conseq (main_run_equiv j0 log0 j0_range).
conseq (main_run_equiv_rev []) run_prop.
+ smt().
+ smt().
qed.

hoare property_transfer :
  Forker(F).run :
  P_in i ==>
  let (j, a1, a2) = res in success j =>
    P_out ((j, a1), Forker.log1) /\ P_out ((j, a2), Forker.log2).
proof.
conseq
  (_ : _ ==> success res.`1 => P_out ((res.`1, res.`3), Forker.log2))
  (_ : _ ==> success res.`1 => P_out ((res.`1, res.`2), Forker.log1)) => //.
+ smt().
+ proc => /=.
  seq 9 : (P_out ((Forker.j1, a1), Forker.log1)); first last.
  + auto => /#.
  wp; call (_ : true) => //; call (_ : true); wp.
  call fst_run_prop.
  skip => /#.
apply snd_run_prop_split.
apply snd_run_prop_single.
qed.

end section PROPERTY_TRANSFER.

hoare success_log_props :
  Forker(F).run : true ==>
  let j = res.`1 in
  let (q1, r1) = nth witness Forker.log1 j in
  let (q2, r2) = nth witness Forker.log2 j in
    success j =>
      size Forker.log1 = Q /\ size Forker.log2 = Q /\
      take j Forker.log1 = take j Forker.log2 /\
      q1 = q2 /\ r1 <> r2.
proof.
conseq
  (_ : _ ==>
    let j = res.`1 in success j => size Forker.log1 = Q /\ size Forker.log2 = Q)
  (_ : _ ==>
    let j = res.`1 in
    let (q1, r1) = nth witness Forker.log1 j in
    let (q2, r2) = nth witness Forker.log2 j in
      success j => take j Forker.log1 = take j Forker.log2 /\ q1 = q2 /\ r1 <> r2);
1: smt(); first last.
+ conseq (property_transfer predT (fun (r : out_t * log_t list) => size r.`2 = Q) _); 1: smt().
  conseq (run_log_size F FRO).
proc.
wp.
have snd_head : forall q0, hoare[
  Forker(F).snd : q = q0 ==> (head witness res.`2).`1 = q0
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

declare pred P_in : in_t.
declare pred P_out : out_t * (log_t list).

declare axiom success_impl :
  hoare[Runner(F, Log(FRO)).run : P_in i /\ Log.log = [] ==> success res.`1 => P_out (res, Log.log)].

declare op pr_success : real.

declare axiom success_eq :
  phoare[Runner(F, FRO).run : P_in i ==> success res.`1] = pr_success.

op pr_collision = 1%r / (size (to_seq (support dresp)))%r.

lemma forking_lemma :
  phoare[
    Forker(F).run :
    P_in arg ==>
    let (j, a1, a2) = res in
    let log1 = Forker.log1 in
    let log2 = Forker.log2 in
    let (q1, r1) = nth witness log1 j in
    let (q2, r2) = nth witness log2 j in
    success j /\
    size log1 = Q /\ size log2 = Q /\
    take j log1 = take j log2 /\ q1 = q2 /\ r1 <> r2 /\
    P_out ((j, a1), log1) /\ P_out ((j, a2), log2)
  ] >= (pr_success ^ 2 / Q%r - pr_success * pr_collision).
proof.
conseq (_ : _ ==> success res.`1) (_ : _ ==>
  success res.`1 =>
    let (j, a1, a2) = res in
    let log1 = Forker.log1 in
    let log2 = Forker.log2 in
    let (q1, r1) = nth witness log1 j in
    let (q2, r2) = nth witness log2 j in
    size log1 = Q /\ size log2 = Q /\
    take j log1 = take j log2 /\ q1 = q2 /\ r1 <> r2 /\
    P_out ((j, a1), log1) /\ P_out ((j, a2), log2)).
+ trivial.
+ smt().
+ pose P_out' := fun (ol : out_t * (log_t list)) => success ol.`1.`1 => P_out ol.
  conseq success_log_props (property_transfer P_in P_out' success_impl) => /#.
bypr => &m P_in_arg /=.
have -> : pr_success = Pr[Runner(F, FRO).run(arg{m}) @ &m : success res.`1].
+ by byphoare (_ : arg = arg{m} ==> _) => //; conseq success_eq.
apply (pr_fork_success &m arg{m}).
qed.

end section CONVENIENCE.

end section PROOF.

