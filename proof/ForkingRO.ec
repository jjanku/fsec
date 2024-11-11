(* This theory provides a variant of the forking lemma for
 * modules F that expect a standard lazy RO (LRO) rather than
 * a forgetful RO (FRO) as in Forking.ec.
 *
 * The result is derived from the forking lemma in Forking.ec
 * by creating a wrapper, called Red, that runs F, forwards
 * F's queries to FRO, and changes inconsistent responses
 * before replying to F.
 *)

pragma Goals:printall.

require import AllCore List FMap.

type state_t.

type in_t, aux_t.

type query_t, resp_t.
op [lossless uniform] dresp : resp_t distr.
const Q : {int | 1 <= Q} as Q_pos.

(* TODO: Same patter as in Forking.ro. Is it idiomatic? *)
require Forking.
clone import Forking as ForkingLRO with
  type state_t <- state_t,
  type query_t <- query_t,
  type resp_t  <- resp_t,
  op   dresp   <- dresp,
  op   Q       <- Q,
  type in_t    <- in_t,
  type aux_t   <- aux_t
proof *.
realize Q_pos     by exact Q_pos.
realize dresp_ll  by exact dresp_ll.
realize dresp_uni by exact dresp_uni.

(* NOTE: We don't use the programming capabilities.
 * PROM was chosen instead of ROM because in conforms
 * to our Oracle module type. *)
require PROM.
clone PROM.FullRO as RO with
  type in_t    <- query_t,
  type out_t   <- resp_t,
  op   dout _  <- dresp.
module LRO = RO.RO.

(* FIXME: This shadows ForkStopping *)
require Stopping.
clone import Stopping as ForkStoppingRO with
  type query_t <- query_t,
  type resp_t  <- resp_t,
  type in_t    <- in_t,
  (* The module must return the critical query instead of
   * its index since queries can be repeated.
   * A successful run is one that returns Some query. *)
  type out_t   <- query_t option * aux_t,
  op   Q       <- Q
  rename "Stoppable" as "StoppableRO"
  rename "Runner" as "RunnerRO"
proof *.
realize Q_pos by exact Q_pos.
export ForkStoppingRO.

module type ForkableRO = {
  include Rewindable
  include StoppableRO
}.

theory Assoc.

op assoc_index ['a 'b] (xs : ('a * 'b) list) a = index a (unzip1 xs).

lemma ofassoc_empty :
  ofassoc [<:'a * 'b>] = empty.
proof.
apply fmap_eqP => x.
rewrite ofassoc_get assoc_nil.
by rewrite emptyE.
qed.

lemma ofassoc_rep ['a 'b] (xs : ('a * 'b) list) (a : 'a) (b : 'b) :
  a \in ofassoc xs => ofassoc (xs ++ [(a, b)]) = ofassoc xs.
proof.
rewrite mem_ofassoc.
move => a_in_xs.
apply fmap_eqP => x.
rewrite 2! ofassoc_get.
rewrite assoc_cat.
case (x \in unzip1 xs) => //.
move => x_notin_xs.
have x_neq_a : x <> a by smt().
rewrite assoc_cons assoc_nil.
rewrite x_neq_a /=.
apply contraT.
by rewrite eq_sym assocTP.
qed.

lemma ofassoc_cat1 ['a 'b] (xs : ('a * 'b) list) a b :
  a \notin ofassoc xs => ofassoc (xs ++ [(a, b)]) = (ofassoc xs).[a <- b].
proof.
rewrite mem_ofassoc.
move => a_notin_xs.
apply fmap_eqP => x.
rewrite ofassoc_get.
rewrite assoc_cat.
case (x = a).
+ move => ->.
  rewrite get_set_sameE.
  rewrite assoc_head.
  smt().
move => x_neq_a.
rewrite get_set_neqE //.
rewrite assoc_cons x_neq_a assoc_nil /=.
rewrite ofassoc_get.
rewrite -assocTP.
smt().
qed.

lemma assoc_index_mem ['a 'b] (xs : ('a * 'b) list) a :
  assoc_index xs a < size xs = a \in (ofassoc xs).
proof.
rewrite /assoc_index.
rewrite - (size_map fst).
rewrite index_mem.
by rewrite mem_ofassoc.
qed.

lemma nth_assoc_index ['a 'b] (xs : ('a * 'b) list) a :
  a \in ofassoc xs =>
  let e = nth witness xs (assoc_index xs a) in
  e.`1 = a /\ e.`2 = oget (ofassoc xs).[a].
proof.
move => a_in_xs e.
rewrite /e /assoc_index.
have index_bound : 0 <= index a (unzip1 xs) < size xs.
+ smt(index_ge0 assoc_index_mem).
split.
+ rewrite - (nth_map witness witness fst) //.
  rewrite nth_index //.
  by rewrite - mem_ofassoc.
rewrite ofassoc_get /assoc.
rewrite (onth_nth witness) //.
qed.

end Assoc.

import Assoc.

module Red(F : ForkableRO) : Forkable = {
  var q : query_t
  (* We use an association list instead of a map so that
   * we can find the index of the critical query easily. *)
  var m : log_t list

  (* FIXME: Need to handle the global vars above. *)
  proc getState() : state_t = {
    var st;
    st <@ F.getState();
    return st;
  }

  proc setState(st : state_t) = {
    F.setState(st);
  }

  proc init(i : in_t) : query_t = {
    m <- [];
    q <@ F.init(i);
    return q;
  }

  proc fix_resp(r : resp_t) : resp_t = {
    (* We always record the response we obtained from the Runner,
     * but to F, we respond consistently, i.e., we use the first
     * response to q in m. *)
    m <- m ++ [(q, r)];
    r <- oget (assoc m q);
    return r;
  }

  proc continue(r : resp_t) : query_t = {
    r <@ fix_resp(r);
    q <@ F.continue(r);

    return q;
  }

  proc finish(r : resp_t) : int * aux_t = {
    var j, cq, o;

    r <@ fix_resp(r);
    (cq, o) <@ F.finish(r);
    j <- odflt Q (omap (assoc_index m) cq);
    return (j, o);
  }
}.

(* TODO: Consider always asking for the returned query
 * once F finishes so that oget cq \in m holds. *)
op success_ro (m : (query_t, resp_t) fmap) (cq : query_t option) =
  is_some cq /\ oget cq \in m.

module ForkerRO(F : ForkableRO) = {
  var m1, m2 : (query_t, resp_t) fmap

  proc run(i : in_t) : query_t option * aux_t * aux_t = {
    var j, a1, a2, cq;

    (j, a1, a2) <@ Forker(Red(F)).run(i);

    m1 <- ofassoc Forker.log1;
    m2 <- ofassoc Forker.log2;
    cq <- if success j
      then Some (nth witness Forker.log1 j).`1
      else None;

    return (cq, a1, a2);
  }
}.

section PROOF.

declare module F <: ForkableRO {-Red, -FRO, -LRO, -Log, -Runner, -Forker}.

(* Coppied from easycrypt-rewinding. *)
declare axiom F_rewindable :
  exists (f : glob F -> state_t), injective f /\
  (forall &m, Pr[F.getState() @ &m : (glob F) = (glob F){m} /\ res = f (glob F){m}] = 1%r) /\
  (forall &m st (x: glob F), st = f x => Pr[F.setState(st) @ &m : glob F = x] = 1%r) /\
  islossless F.setState.

declare axiom F_continue_ll : islossless F.continue.
declare axiom F_finish_ll : islossless F.finish.

local lemma Red_F_rewindable :
  exists (f : glob Red(F) -> state_t), injective f /\
  (forall &m, Pr[Red(F).getState() @ &m : (glob Red(F)) = (glob Red(F)){m} /\ res = f (glob Red(F)){m}] = 1%r) /\
  (forall &m st (x: glob Red(F)), st = f x => Pr[Red(F).setState(st) @ &m : glob Red(F) = x] = 1%r) /\
  islossless Red(F).setState.
proof.
admit.
qed.

local lemma Red_F_continue_ll : islossless Red(F).continue.
proof.
islossless; exact F_continue_ll.
qed.

local lemma Red_F_finish_ll : islossless Red(F).finish.
proof.
islossless; exact F_finish_ll.
qed.

(* This is for outline purposes only. *)
local module RedO = {
  proc get(q : query_t) : resp_t = {
    var r, r1 : resp_t;
    r <@ Log(FRO).get(q);
    r1 <- r;
    r1 <@ Red(F).fix_resp(r1);
    return r1;
  }
}.

local equiv redo_lro_equiv :
  RedO.get ~ LRO.get :
  ={arg} /\ Log.log{1} = Red.m{1} /\ ofassoc Red.m{1} = LRO.m{2} /\ q{1} = Red.q{1} ==>
  ={res} /\ Log.log{1} = Red.m{1} /\ ofassoc Red.m{1} = LRO.m{2}.
proof.
proc; inline.
wp 9 3.
conseq (_ : _ ==> Log.log{1} = Red.m{1} /\ ofassoc Red.m{1} = LRO.m{2} /\ Red.q{1} = x{2}).
+ smt(ofassoc_get).
auto => />.
smt(ofassoc_cat1 ofassoc_rep).
qed.

local equiv red_log_fro_lro_equiv :
  Runner(Red(F), Log(FRO)).run ~ RunnerRO(F, LRO).run :
  (* TODO: Consider initializing the oracle in Runner. *)
  ={arg, glob F} /\ Log.log{1} = [] /\ LRO.m{2} = empty ==>
  ={glob F} /\ ofassoc Log.log{1} = LRO.m{2} /\
  res{1}.`1 = odflt Q (omap (assoc_index Log.log{1}) res{2}.`1) /\ res{1}.`2 = res{2}.`2 /\
  (success res{1}.`1 <=> success_ro LRO.m{2} res{2}.`1).
proof.
conseq
  (_ : _ ==> ={glob F} /\ ofassoc Log.log{1} = LRO.m{2} /\
             res{1}.`1 = odflt Q (omap (assoc_index Log.log{1}) res{2}.`1) /\ res{1}.`2 = res{2}.`2)
  (run_log_size (Red(F)) FRO) => //.
+ move => />.
  move => resL resR m.
  pose j := resL.`1; pose cq := resR.`1.
  case cq => /=.
  + smt().
  smt(index_ge0 assoc_index_mem).
proc.
inline Red -Red(F).fix_resp.
wp => /=.
call (_ : true).
outline {1} [7-9] r1 <@ RedO.get.
call redo_lro_equiv.
while (={c, q, glob F} /\ Log.log{1} = Red.m{1} /\ ofassoc Red.m{1} = LRO.m{2} /\ q{1} = Red.q{1}).
+ outline {1} [1-3] r0 <@ RedO.get.
  wp.
  call (_ : true).
  call redo_lro_equiv.
  auto => />.
wp; call (_ : true).
auto => />.
exact ofassoc_empty.
qed.

section CONVENIENCE.

declare pred P_in : glob F * in_t.
(* FIXME: How to declare the predicate so that it takes two values instead of a pair? *)
declare pred P_out : (query_t option * aux_t) * ((query_t, resp_t) fmap).

declare axiom success_impl :
  hoare[
    RunnerRO(F, LRO).run :
    P_in (glob F, i) /\ LRO.m = empty ==>
    success_ro LRO.m res.`1 => P_out (res, LRO.m)
  ].

declare op pr_success : real.

declare axiom success_eq :
  phoare[
    RunnerRO(F, LRO).run :
    P_in (glob F, i) /\ LRO.m = empty
    ==> success_ro LRO.m res.`1
  ] = pr_success.

lemma forking_lemma_ro :
  phoare[
    ForkerRO(F).run :
    P_in (glob F, arg) ==>
    let (cq, a1, a2) = res in
    let m1 = ForkerRO.m1 in
    let m2 = ForkerRO.m2 in
    (* TODO: Rename cq? *)
    let q  = oget cq in
    is_some cq /\
    q \in m1 /\ q \in m2 /\ m1.[q] <> m2.[q] /\
    P_out ((cq, a1), m1) /\ P_out ((cq, a2), m2)
  ] >= (pr_success ^ 2 / Q%r - pr_success * pr_collision).
proof.
proc.
wp.
pose Red_P_in := (fun (arg : glob Red(F) * in_t) =>
  let (gRed, i) = arg in
  let (_, __, gF) = gRed in
  P_in (gF, i)
).
pose Red_P_out := (fun (ret : (int * aux_t) * log_t list) =>
  let (o, log) = ret in
  let (j, aux) = o in
  let m = ofassoc log in
  let (q, r) = nth witness log j in
  q \in m /\ m.[q] = Some r /\ P_out ((Some q, aux), m)
).
call (
  forking_lemma (Red(F))
  Red_F_rewindable Red_F_continue_ll Red_F_finish_ll
  Red_P_in Red_P_out _ pr_success _
).
+ conseq red_log_fro_lro_equiv success_impl; 1: smt().
  smt(nth_assoc_index).
+ have success_eq_log : phoare[
    Runner(Red(F), Log(FRO)).run : P_in (glob F, i) /\ Log.log = [] ==> success res.`1
  ] = pr_success.
  + conseq red_log_fro_lro_equiv success_eq => /#.
  conseq (runner_log_equiv (Red(F))) success_eq_log => /#.
skip.
rewrite /Red_P_out.
smt().
qed.

end section CONVENIENCE.

end section PROOF.
