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

(* TODO: Properly import Rewindable form easycrypt-rewinding. *)
type state_t.

module type Rewindable = {
  proc getState() : state_t
  proc setState(st : state_t) : unit
}.

type aux_t.

clone import Stopping as ForkStopping with
  type out_t <= int * aux_t.
(* FIXME: Why is this not imported as well? *)
type out_t = int * aux_t.

(* TODO: Generalize, e.g., to (query_t -> resp_t distr)? *)
(* TODO: Remove uniformity assumption? *)
op [lossless uniform] dresp : resp_t distr.

(* Forgetful random oracle. *)
(* NOTE: The oracle is allowed to behave inconsistently.
 * This is intentional, otherwise we may not be able to
 * repogram the oracle at the forking point. *)
module FRO : Oracle = {
  proc get(q : query_t) : resp_t = {
    var r : resp_t;
    r <$ dresp;
    return r;
  }
}.

(* TODO: Does it make sense to generalize somehow? *)
(* NOTE: We index queries from 0 (unlike pen&paper proofs). *)
op success (j : int) : bool = 0 <= j < Q.

module type Forkable = {
  include Rewindable
  include Stoppable
}.

type log_t = query_t * resp_t.

(* TODO: Think about how to define the module so that it is
 * more amenable to proving the forking lemma. *)
module Forker(F : Forkable) = {
  (* FIXME: Might be easier to prove invariants about these if we
   * keep them local. In such case, we would need to return
   * those in run to be able to refer to the results. *)
  var j1, j2 : int
  var log1, log2 : (query_t * resp_t) list
  var r1, r2 : resp_t

  (* FIXME: log directly to log1 and log2? *)

  (* First run of F, with query and state logging. *)
  proc fst(i : in_t) : out_t * (log_t list) * (state_t list) = {
    var sts : state_t list;
    var st : state_t;
    var log : log_t list;
    var o : out_t;
    var q : query_t;
    var r : resp_t;
    var c : int;

    sts <- [];
    log <- [];

    q <@ F.init(i);
    c <- 1;

    while (c < Q) {
      st <@ F.getState();
      sts <- sts ++ [st];
      r <@ FRO.get(q);
      log <- log ++ [(q, r)];
      q <@ F.continue(r);
      c <- c + 1;
    }

    st <@ F.getState();
    sts <- sts ++ [st];
    r <@ FRO.get(q);
    log <- log ++ [(q, r)];
    o <@ F.finish(r);

    return (o, log, sts);
  }

  (* Second partial run of F, with query logging. *)
  proc snd(q : query_t, c : int) : out_t * (log_t list) = {
    var log : log_t list;
    var o : out_t;
    var r : resp_t;

    log <- [];

    while (c < Q) {
      r <@ FRO.get(q);
      log <- log ++ [(q, r)];
      q <@ F.continue(r);
      c <- c + 1;
    }

    r <@ FRO.get(q);
    log <- log ++ [(q, r)];
    o <@ F.finish(r);

    return (o, log);
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

    (* FIXME: might be easier to prove things if we fail early. *)

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

section.

declare module F <: Forkable {-FRO, -Runner, -Forker}.

(* Coppied from easycrypt-rewinding. *)
declare axiom F_rewindable :
  exists (f : glob F -> state_t), injective f /\
  (forall &m, Pr[F.getState() @ &m : (glob F) = (glob F){m} /\ res = f (glob F){m}] = 1%r) /\
  (forall &m st (x: glob F), st = f x => Pr[F.setState(st) @ &m : glob F = x] = 1%r) /\
  islossless F.setState.


local lemma get_st_preserves_glob (gF : glob F):
  phoare[F.getState : (glob F) = gF ==> (glob F) = gF] = 1%r.
proof.
elim F_rewindable.
move => f [_ [H [_ _]]].
proc*.
call (_ : glob F = gF ==> glob F = gF /\ res = f gF).
bypr => &m gF_mem.
rewrite -gF_mem.
apply (H &m).
auto.
qed.

local lemma fork_pr i &m :
  Pr[Forker(F).run(i) @ &m : success res.`1] =
  Pr[Forker(F).run(i) @ &m : Forker.j1 = Forker.j2 /\ success Forker.j1 /\ Forker.r1 <> Forker.r2].
proof.
byequiv => //.
proc.
seq 9 9 : (={glob Forker}).
sim.
auto.
smt().
qed.

local lemma pr_split i &m :
  Pr[Forker(F).run(i) @ &m : Forker.j1 = Forker.j2 /\ success Forker.j1 /\ Forker.r1 <> Forker.r2] >=
  Pr[Forker(F).run(i) @ &m : Forker.j1 = Forker.j2 /\ success Forker.j1] -
  Pr[Forker(F).run(i) @ &m : success Forker.j1 /\ Forker.r1 = Forker.r2].
proof.
(* FIXME: Cannot use occurence selector with rewrite Pr? *)
have -> :
  Pr[Forker(F).run(i) @ &m : Forker.j1 = Forker.j2 /\ success Forker.j1] =
  Pr[Forker(F).run(i) @ &m : Forker.j1 = Forker.j2 /\ success Forker.j1 /\ Forker.r1 = Forker.r2] +
  Pr[Forker(F).run(i) @ &m : Forker.j1 = Forker.j2 /\ success Forker.j1 /\ Forker.r1 <> Forker.r2].
by rewrite Pr[mu_split Forker.r1 = Forker.r2]; smt().
have ABC_le_BC :
  Pr[Forker(F).run(i) @ &m : Forker.j1 = Forker.j2 /\ success Forker.j1 /\ Forker.r1 = Forker.r2] <=
  Pr[Forker(F).run(i) @ &m : success Forker.j1 /\ Forker.r1 = Forker.r2].
rewrite Pr[mu_sub] //.
smt().
qed.

local lemma fst_run_equiv :
  equiv[
    Forker(F).fst ~ Runner(F, FRO).run :
    ={arg, glob F} ==> ={glob F} /\ res{1}.`1 = res{2}
  ].
proof.
proc.
call (_ : true).
wp.
call (_ : true). sim.
wp.
conseq (_ : _ ==> ={q, glob F}). trivial.
ecall {1} (get_st_preserves_glob (glob F){1}).
while (={q, c, glob F}).
wp.
call (_ : true).
wp.
call (_ : true). sim.
wp.
ecall {1} (get_st_preserves_glob (glob F){1}).
auto.
wp.
call (_ : true).
auto.
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
have fst_log_size : hoare[Forker(F).fst : true ==> size res.`2 = Q].
proc. inline.
call (_ : true).
wp.
rnd.
wp.
call (_ : true).
while (c = size log + 1 /\ c <= Q).
wp. call (_ : true). wp. rnd. wp. call (_ : true). skip. smt(size_cat).
wp.
call (_ : true).
wp.
skip => />.
smt(Q_pos size_cat).
wp.
call fst_log_size.
auto.

(* #pre ==> success Forker.j1 *)
wp.
call (_ : glob F = (glob F){m} /\ arg = i ==> success res.`1.`1).
bypr.
move => &m0 glob_eq.
byequiv => //.
conseq (_ : ={arg, glob F} ==> ={glob F} /\ res{1}.`1 = res{2}). smt(). trivial.
apply fst_run_equiv.
auto.

(* success Forker.j1 ==> #post *)
inline.
wp.
conseq (_ : _ ==> success Forker.j1 /\ Forker.r1 = (head witness log).`2). smt(nth_cat size_takel nth0_head).
(* FIXME: This is rather painful. Call doesn't work in pHL? *)
seq 10 : (success Forker.j1 /\ Forker.r1 = (head witness log).`2)
  inv_supp_size 1%r
  _ 0%r;
1,3,5: trivial.
wp.
have mu_dresp_eq :
  forall r0, mu dresp (fun r => r0 = r) <= inv_supp_size.
move => r0.
have -> : (fun r => r0 = r) = pred1 r0 by smt().
rewrite (mu1_uni_ll _ _ dresp_uni dresp_ll).
smt(invr_ge0 size_ge0).
case (Forker.j1 = Q - 1).

(* case: Forker.j1 = Q*)
rcondf 6. wp. call (_ : true). auto.
rnd. wp. simplify.
call (_ : true). auto.
move => &hr [[_ succ] _].
rewrite succ /=.
apply mu_dresp_eq.

(* case: Forker.j1 <> Q *)
unroll 6. rcondt 6. wp. call (_ : true). wp. skip. smt().
seq 9 : (success Forker.j1 /\ Forker.r1 = (head witness log).`2)
  inv_supp_size 1%r
  _ 0%r
  (log <> []);
3,5: trivial.
wp. rnd. wp. call (_ : true). wp. skip => /#.
wp. rnd. wp. call (_ : true). wp. skip => /=.
move => &hr [[_ succ] _].
rewrite succ /=.
apply mu_dresp_eq.

hoare. rnd. wp.
while (log <> [] /\ ! (success Forker.j1 /\ Forker.r1 = (head witness log).`2)).
wp. call (_ : true). wp. rnd. wp. skip => /#.
wp. call (_ : true). skip => /#.

hoare. call (_ : true). auto.

(* ! success Forker.j1 ==> #post *)
hoare.
conseq (_ : _ ==> ! success Forker.j1); first by smt().
wp.
call (_ : true) => //.
call (_ : true).
auto.
qed.

print glob Forker.

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
apply ge0ind.
smt().
simplify.
rewrite big_geq; 1: trivial.
have -> : forall x, (0 <= x < 0) = false by smt().
simplify.
rewrite Pr[mu_false] //.
simplify.
move => n n_ge0 ind _.
rewrite big_int_recr //=.
rewrite Pr[mu_split Forker.j1 < n].
have -> : forall b x, ((b /\ 0 <= x < n + 1) /\ x < n) <=> (b /\ 0 <= x < n) by smt().
rewrite ind //.
have -> : forall j1 j2, ((j1 = j2 /\ 0 <= j1 < n + 1) /\ ! j1 < n) <=> (j1 = n /\ j2 = n) by smt().
trivial.
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
apply ge0ind.
smt().
simplify.
rewrite big_geq; 1: trivial.
have -> : forall x, (0 <= x < 0) = false by smt().
simplify.
rewrite Pr[mu_false] //.
simplify.
move => n n_ge0 ind _.
rewrite big_int_recr //=.
rewrite Pr[mu_split res.`1 < n].
have -> : forall x, ((0 <= x < n + 1) /\ x < n) <=> (0 <= x < n) by smt().
rewrite ind //.
have -> : forall j, ((0 <= j < n + 1) /\ ! j < n) <=> (j = n) by smt().
trivial.
qed.

local module SplitForker(F : Forkable) = {
  var bad : bool

  (* Forker.fst that runs F only until the first C queries. *)
  proc fst_partial(i : in_t, C : int) : query_t * (log_t list) * (state_t list) = {
    var sts : state_t list;
    var st : state_t;
    var log : log_t list;
    var o : out_t;
    var q : query_t;
    var r : resp_t;
    var c : int;

    sts <- [];
    log <- [];

    q <@ F.init(i);
    c <- 1;

    (* CHANGE: < C instead of < Q. *)
    while (c < C) {
      st <@ F.getState();
      sts <- sts ++ [st];
      r <@ FRO.get(q);
      log <- log ++ [(q, r)];
      q <@ F.continue(r);
      c <- c + 1;
    }

    (* CHANGE: Finish removed. *)

    return (q, log, sts);
  }

  (* Same as Forker.snd, but with state recording. *)
  (* TODO: Consider adding state recording to Forker.snd instead. *)
  proc snd(q : query_t, c : int) : out_t * (log_t list) * (state_t list) = {
    var sts : state_t list;
    var st : state_t;
    var log : log_t list;
    var o : out_t;
    var r : resp_t;

    sts <- [];
    log <- [];

    while (c < Q) {
      st <@ F.getState();
      sts <- sts ++ [st];
      r <@ FRO.get(q);
      log <- log ++ [(q, r)];
      q <@ F.continue(r);
      c <- c + 1;
    }

    st <@ F.getState();
    sts <- sts ++ [st];
    r <@ FRO.get(q);
    log <- log ++ [(q, r)];
    o <@ F.finish(r);

    return (o, log, sts);
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
  proc run1(i : in_t, j : int) : int * int = {
    var sts1, _sts2 : state_t list;
    var st : state_t;
    var log1, _log2 : log_t list;
    var o1, o2 : out_t;
    var j1, j1', j2 : int;
    var q : query_t;

    (o1, log1, sts1) <@ fst(i, j + 1);
    j1 <- o1.`1;

    bad <- false;
    j1' <- j1;
    if (j1 <> j) {
      bad <- true;
    }

    q <- (nth witness log1 j1').`1;
    st <- nth witness sts1 j1';
    F.setState(st);

    (o2, _log2, _sts2) <@ snd(q, j1' + 1);
    j2 <- o2.`1;

    return (j1, j2);
  }

  (* Same as run1, except we always rewind to the j-th query. *)
  proc run2(i : in_t, j : int) : int * int = {
    var sts1, _sts2 : state_t list;
    var st : state_t;
    var log1, _log2 : log_t list;
    var o1, o2 : out_t;
    var j1, j1', j2 : int;
    var q : query_t;

    (o1, log1, sts1) <@ fst(i, j + 1);
    j1 <- o1.`1;

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

    (o2, _log2, _sts2) <@ snd(q, j1' + 1);
    j2 <- o2.`1;

    return (j1, j2);
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
inline SplitForker(F).fst_partial SplitForker(F).snd.
wp.
call (_ : true).
wp.
call (_ : true). auto.
wp.
call (_ : true).
splitwhile{1} 5 : c < C.
conseq (_ : _ ==> ={glob F} /\ q{1} = q1{2} /\ log{1} = log1{2} ++ log3{2} /\ sts{1} = sts1{2} ++ sts3{2}) => />. smt(catA).
while (={glob F} /\ q{1} = q1{2} /\ log{1} = log1{2} ++ log3{2} /\ sts{1} = sts1{2} ++ sts3{2} /\ c{1} = c0{2}).
  wp. call (_ : true). wp. call (_ : true). auto. wp. call (_ : true). skip => />. smt(catA).
wp.
conseq (_ : _ ==> ={glob F} /\ q{1} = q0{2} /\ log{1} = log0{2} /\ sts{1} = sts0{2} /\ c{1} = C) => />. smt(cats0).
while ( ={glob F} /\ q{1} = q0{2} /\ log{1} = log0{2} /\ sts{1} = sts0{2} /\ c{1} = c{2} /\ c{1} <= C /\ C0{2} = C).
  wp. call (_ : true). wp. call (_ : true). auto. wp. call (_ : true). skip => />. smt().
wp.
call (_ : true).
auto => />.
smt().
qed.

local lemma snd_equiv :
  equiv[
    Forker(F).snd ~ SplitForker(F).snd :
    ={glob F, arg} ==> ={glob F} /\ res{1}.`1 = res{2}.`1 /\ res{1}.`2 = res{2}.`2
  ].
proof.
proc => /=.
sim.
ecall {2} (get_st_preserves_glob (glob F){2}).
while (={q, log, glob F, c}).
sim.
ecall {2} (get_st_preserves_glob (glob F){2}).
auto.
auto.
qed.

local lemma pr_run1_eq &m i j :
  0 <= j < Q =>
  Pr[Forker(F).run(i) @ &m : Forker.j1 = j /\ Forker.j2 = j] =
  Pr[SplitForker(F).run1(i, j) @ &m : res.`1 = j /\ res.`2 = j].
proof.
move => j_range.
byequiv => //.
proc.
wp => /=.
call snd_equiv.
call (_ : true).
wp => /=.
call (fst_split_equiv (j + 1)). smt().
auto => />.
smt().
qed.

local lemma pr_run2_ineq &m i j :
  Pr[SplitForker(F).run1(i, j) @ &m : res.`1 = j /\ res.`2 = j] >=
  Pr[SplitForker(F).run2(i, j) @ &m : res.`1 = j /\ res.`2 = j].
proof.
have :
  Pr[SplitForker(F).run2(i, j) @ &m : res.`1 = j /\ res.`2 = j] <=
    Pr[SplitForker(F).run1(i, j) @ &m : res.`1 = j /\ res.`2 = j] +
  Pr[SplitForker(F).run2(i, j) @ &m : (res.`1 = j /\ res.`2 = j) /\ SplitForker.bad].
byupto.
have -> :
  Pr[SplitForker(F).run2(i, j) @ &m : (res.`1 = j /\ res.`2 = j) /\ SplitForker.bad] = 0%r.
byphoare (_ : arg.`2 = j ==> _) => //. hoare.
proc => /=.
conseq (_ : _ ==> !(j1 = j /\ SplitForker.bad)). smt().
wp. do 3! (call (_ : true) => //; wp).
trivial.
qed.

(* Need to transform SplitForker.run2 into a form
 * that is suitable for application of the rew_with_init lemma. *)

local module RewindWrapper(F : Forkable) = {

  (* FIXME: Need to handle bad var in SplitForker. *)
  proc getState() : state_t = {
    var st;
    st <@ F.getState();
    return st;
  }

  proc setState(st : state_t) = {
    F.setState(st);
  }

  proc init(ij : in_t * int) : query_t * int = {
    var i, j, q, log, sts;
    (i, j) <- ij;
    (q, log, sts) <@ SplitForker(F).fst_partial(i, j + 1);
    return (q, j);
  }

  proc run(qj : query_t * int) : int = {
    var q, o, log, sts, j;
    (q, j) <- qj;
    (o, log, sts) <@ SplitForker(F).snd(q, j + 1);
    return o.`1;
  }
}.

(* This matches the QQ module in easycrypt-rewinding. *)
(* FIXME: Clone and instantiate RewWithInit.. *)
type iat = in_t * int.
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

(* FIXME: Import it properly. *)
(* lemma rew_with_init &m M i :
 *   Pr[ QQ(A,B).main(i) @ &m : M res.`1 /\ M res.`2 ]
 *     >= Pr[ QQ(A,B).main_run(i) @ &m : M res ] ^ 2. *)

local lemma rewinder_run_equiv :
  equiv[
    InitRewinder(F).main_run ~ SplitForker(F).fst :
    ={glob F} /\ arg{1}.`1 = arg{2}.`1 /\ arg{1}.`2 + 1 = arg{2}.`2  ==> ={glob F} /\ res{1}.`2 = res{2}.`1.`1
  ].
proof.
proc => /=.
inline InitRewinder.
wp.
call (_ : ={glob F}). sim.
wp.
call (_ : ={glob F}). sim.
auto => />.
qed.

local lemma pr_wrapper_run &m i j :
  0 <= j < Q =>
  Pr[Runner(F, FRO).run(i) @ &m : res.`1 = j] =
  Pr[InitRewinder(F).main_run((i, j)) @ &m : res.`2 = j].
proof.
move => j_range.
byequiv => //.
(* TODO: Try whether "rewrite equiv" would be easier to use. *)
transitivity
  Forker(F).fst
  (={glob F, arg} ==> res{1} = res{2}.`1)
  (={glob F} /\ arg{1} = arg{2}.`1 /\ arg{2} = (i, j) ==> res{1}.`1.`1 = res{2}.`2);
1,2: smt().
symmetry.
(* FIXME: conseq really needed? *)
conseq (_ : ={arg, glob F} ==> ={glob F} /\ res{1}.`1 = res{2}); 1,2: smt().
apply fst_run_equiv.
transitivity
  SplitForker(F).fst
  (={glob F} /\ arg{1} = arg{2}.`1 /\ arg{2}.`2 = j + 1 ==> ={glob F, res})
  (={glob F} /\ arg{1}.`1 = arg{2}.`1 /\ arg{1}.`2 = arg{2}.`2 + 1 ==> ={glob F} /\ res{1}.`1.`1 = res{2}.`2).
move => &1 &2 rel.  exists (glob F){1} (i, j + 1). smt().
smt().
apply fst_split_equiv => //. smt().
symmetry.
conseq (_ : ={glob F} /\ arg{1}.`1 = arg{2}.`1 /\ arg{1}.`2 + 1 = C{2} ==> ={glob F} /\ res{1}.`2 = res{2}.`1.`1); 1,2: smt().
apply rewinder_run_equiv.
qed.

local lemma pr_wrapper_main &m i j :
  0 <= j < Q =>
  Pr[SplitForker(F).run2(i, j) @ &m : res.`1 = j /\ res.`2 = j] =
  Pr[InitRewinder(F).main((i, j)) @ &m : res.`1.`2 = j /\ res.`2.`2 = j].
proof.
move => j_range.
byequiv => //.
proc => /=.
inline InitRewinder SplitForker(F).fst.
wp.
call (_ : ={glob F}). sim.
wp.
call (_ : true).
wp.
simplify.
conseq (_ : _ ==>
  ={glob F, o} /\
  nth witness (sts10{1} ++ sts2{1}) j = s{2} /\
  ((nth witness (log10{1} ++ log2{1}) j).`1, j) = r0{2}
). smt().
seq 3 4 : (={glob F} /\ C{1} = j + 1 /\ (q0{1}, j) = r0{2} /\
  size log10{1} = j /\ size sts10{1} = j).
wp.
call (_ : ={glob F, arg} /\ arg{1}.`2 = j + 1 ==> ={glob F, res} /\ size res{1}.`2 = j /\ size res{1}.`3 = j).
proc.
while (={glob F, q, log, sts, c, C} /\ c{1} <= C{1} /\ size log{1} + 1 = c{1} /\ size sts{1} + 1 = c{1}).
  wp. call (_ : true). wp. call (_ : true). sim. wp. call (_ : true). skip => />. smt(size_cat).
wp. call (_ : true). wp. skip => />. smt().
wp. skip => />.

(* TODO: Life could probably be much easier if we reordered
 * Forker.fst so that the first getState is outside of the while loop. *)
inline SplitForker(F).snd.
conseq (_ : _ ==> ={glob F, o} /\
  head witness sts2{1} = s{2} /\
  ((head witness log2{1}).`1, j) = r0{2}
).
move => />.
smt(nth0_head nth_cat).
swap {2} [1..2] 6.
sp.
wp.
call (_ : true).
wp.
call (_ : true). sim.
wp.
case (j = Q - 1).
rcondf {1} 1. move => &n. skip. smt().
rcondf {2} 3. move => &n. wp. call (_ : true). skip. smt().
wp.
ecall {2} (get_st_preserves_glob (glob F){1}).
wp.
call (_ : true).
skip => />.

unroll {1} 1. unroll {2} 3.
rcondt {1} 1. move => &n. skip. smt().
rcondt {2} 3. move => &n. wp. call (_ : true). skip. smt().
call (_ : true).
while (
  ={glob F, c} /\ q1{1} = q2{2} /\
  head witness sts0{1} = s{2} /\ sts0{1} <> [] /\
  ((head witness log0{1}).`1, j) = r0{2} /\ log0{1} <> []
).
wp. call (_ : true). wp. call (_ : true). sim. wp. call (_ : true). skip => />. smt().
wp. call (_ : true). wp. call (_ : true). sim. wp.
ecall {2} (get_st_preserves_glob (glob F){1}).
wp.
call (_ : true).
skip => />.
smt(head_cons).
qed.

(* IMPORTANT: It doesn't seem to be possible to prove this via pRHL.
 * While Forker.fst ~ DetForker.fst; DetForker.snd is true,
 * the probability that the remaining programs terminate differ. *)

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
admit. (* Direct application of rew_with_init. *)
qed.

op square (x : real) = x ^ 2.

lemma square_convex : forall (a b : real), convex square a b.
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
move : (Jensen_fin [0..n - 1] f square (finite_dinter 0 (n - 1)) (dinter_ll 0 (n - 1) _) square_convex). smt().
rewrite ! fin_expE; 1,2: by apply finite_dinter.
rewrite /(\o).
rewrite ! (eq_big_perm _ _ (to_seq (support [0..n - 1])) (range 0 n)); 1,2: apply perm_eq_dinter.
rewrite (eq_big_seq _ (fun (j : int) => f j / n%r)). smt(mem_range dinter1E).
rewrite (eq_big_seq (fun (x : int) => square (f x) * mu1 [0..n - 1] x) (fun (j : int) => square (f j) / n%r)). smt(mem_range dinter1E).
rewrite - !  mulr_suml.
pose s := bigi predT f 0 n.
pose s2 :=  bigi predT (fun (i : int) => square (f i)) 0 n.
have -> : forall (x y : real), square (x * y) = y * square x * y. move => x y. smt(mulrC expr2).
rewrite ler_pmul2r => /#.
qed.

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
apply pr_succ_resp_eq.
rewrite pr_split_sum.
rewrite pr_succ_sum.
have : bigi predT (fun (j : int) => Pr[Runner(F, FRO).run(i) @ &m : res.`1 = j] ^ 2) 0 Q <=
  bigi predT (fun (j : int) => Pr[Forker(F).run(i) @ &m : Forker.j1 = j /\ Forker.j2 = j]) 0 Q.
  apply ler_sum_seq.
  move => j j_range _.
  simplify.
  apply pr_fork_specific. smt(mem_range).
apply ler_trans.
apply square_sum.
  smt(Q_pos).
  smt(ge0_mu).
qed.

end section.

(* CRITICAL: How can we show that parts of the output
 * are identical in both executions?
 *
 * Will need to somehow show that if the j-th query
 * is critical, then the final output (the relevant part)
 * does not change afterwards?
 *
 * Use some invariant over states to show that
 * both end states satisfy some property?
 *
 * Could be also helpful to show that the logs from both
 * executions share a prefix? *)

