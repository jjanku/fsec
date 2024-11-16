pragma Goals:printall.

require import AllCore FMap List Distr Finite.

require DLog.
clone import DLog as DL
  rename "Adversary" as "Adv_DL"
  rename "DLogExperiment" as "Exp_DL".
import G GP FD GP.ZModE GP.ZModE.ZModpField.
import DLog.

type com_t  = group. (* Commitment *)
type chal_t = exp.   (* Challenge  *)
type resp_t = exp.   (* Response   *)
type trans_t = com_t * chal_t * resp_t. (* Transcript *)

type pk_t = group.
type sk_t = exp.

type msg_t.
type sig_t = com_t * resp_t.

type query_t = pk_t * com_t * msg_t.

require DigitalSignaturesROM.
clone import DigitalSignaturesROM as DS_ROM with
  type pk_t  <- pk_t,
  type sk_t  <- sk_t,
  type msg_t <- msg_t,
  type sig_t <- sig_t,
  type in_t  <- query_t,
  type out_t <- chal_t.
import StatelessROM.

op dnonce : exp distr.
(* The distribution of private keys must match the one used in Exp_DL. *)
op dsk : sk_t distr = dt.
op [lossless uniform] dchal : chal_t distr.

(* TODO: Really need to ask on Zulip how to work with tuples. *)
op verify (pk : pk_t) (t : trans_t) =
  (* let (com, chal, resp) = t in g ^ resp = com * (pk ^ chal). *)
  g ^ t.`3 = t.`1 * (pk ^ t.`2).

(* FIXME: The variable names are probably a bit too verbose. *)
module (Schnorr : Scheme_ROM) (RO : Oracle) = {
  proc keygen() : pk_t * sk_t = {
    var sk, pk;
    sk <$ dsk;
    pk <- g ^ sk;
    return (pk, sk);
  }

  proc sign(sk : sk_t, m : msg_t) : sig_t = {
    var pk, nonce, com, chal, resp;

    pk <- g ^ sk;
    nonce <$ dnonce;
    com <- g ^ nonce;
    chal <@ RO.get(pk, com, m);
    resp <- nonce + sk * chal;

    return (com, resp);
  }

  proc verify(pk : pk_t, m : msg_t, s : sig_t) : bool = {
    var com, resp, chal;

    (com, resp) <- s;
    chal <@ RO.get(pk, com, m);

    return verify pk (com, chal, resp);
  }
}.

op extractor (pk : pk_t) (t1 t2 : trans_t) =
(*  let (_, chal1, resp1) = t1 in
  let (_, chal2, resp2) = t2 in
  (resp1 - resp2) / (chal1 - chal2). *)
  (t1.`3 - t2.`3) / (t1.`2 - t2.`2).

(* The main part of the proof is taken from the following EC example:
 * https://github.com/EasyCrypt/easycrypt/blob/r2024.09/examples/SchnorrPK.ec#L146-L148 *)
lemma extractor_corr (pk : pk_t) (t1 t2 : trans_t) :
  t1.`1 = t2.`1 => t1.`2 <> t2.`2 =>
  verify pk t1 => verify pk t2 =>
  pk = g ^ (extractor pk t1 t2).
proof.
rewrite /verify /extractor.
pose r := t1.`1.
pose z1 := t1.`3; pose z2 := t2.`3.
pose e1 := t1.`2; pose e2 := t2.`2.
move => <- e12_neq t1_verif t2_verif.
rewrite expM expB.
rewrite t1_verif t2_verif.
rewrite invM (mulcC r) mulcA -(mulcA (pk ^ e1)).
rewrite mulcV mulc1.
rewrite -expB -expM.
rewrite divrr.
+ by rewrite subr_eq0.
by rewrite exp1.
qed.

require Stopping.
clone import Stopping as AdvStopping with
  type in_t    <- pk_t,
  type out_t   <- msg_t * sig_t,
  type query_t <- query_t,
  type resp_t  <- chal_t.

require ForkingRO.
clone import ForkingRO as AdvForkingRO with
  type in_t    <- pk_t,
  (* All other important parts of the forgery
   * are included in the critical query.*)
  type aux_t   <- resp_t,
  type query_t <- query_t,
  type resp_t  <- chal_t,
  op   dresp   <- dchal,
  op   Q       <- Q + 1
proof *.
realize Q_pos     by smt(Q_pos).
realize dresp_ll  by exact dchal_ll.
realize dresp_uni by exact dchal_uni.

section SECURITY_EUF_KOA.

module (AdvRunner (A : Stoppable) : Adv_EUFKOA_ROM) (O : Oracle) = {
  proc forge = Runner(A, O).run
}.

module type ForkableAdv = {
  include Stoppable
  include ForkingLRO.Rewindable
}.

(* A simple wrapper that runs A and makes one extra query
 * at the end to verify A's forgery. *)
(* TODO: Consider creating a generic module for this type
 * of transformation, it is probably a common pattern. *)
module AdvWrapper (A : ForkableAdv) : ForkableRO = {
  var c : int
  var pk : pk_t
  var q : query_t
  var com : com_t
  var resp : resp_t

  (* FIXME: Need to handle global vars. *)
  proc getState() : state_t = {
    var st;
    st <@ A.getState();
    return st;
  }

  proc setState(st : state_t) = {
    A.setState(st);
  }

  proc init(i : pk_t) : query_t = {
    pk <- i;
    (* NOTE: This is just to make sim tactic happy
     * since these are assigned in an else branch only. *)
    (com, resp) <- witness;
    q <@ A.init(pk);
    c <- 1;
    return q;
  }

  proc continue(r : chal_t) : query_t = {
    var m, s;

    if (c < Q) {
      q <@ A.continue(r);
    } else {
      (m, s) <@ A.finish(r);
      (com, resp) <- s;
      q <- (pk, com, m);
    }
    c <- c + 1;

    return q;
  }

  proc finish(r : chal_t) : query_t option * resp_t = {
    var cq;

    cq <- if verify pk (q.`2, r, resp)
      then Some q
      else None;

    return (cq, resp);
  }
}.

(* An input generator to be used with IRunnerRO.
 * Cannot be local because A must not access its glob. *)
module KeyGen = {
  var sk : sk_t

  proc gen() : pk_t = {
    var pk;
    sk <$ dsk;
    pk <- g ^ sk;
    return pk;
  }
}.

declare module A <: ForkableAdv {-LRO, -AdvWrapper, -IForkerRO, -KeyGen, -ConstGen}.

(* Coppied from easycrypt-rewinding. *)
declare axiom A_rewindable :
  exists (f : glob A -> state_t), injective f /\
  (forall &m, Pr[A.getState() @ &m : (glob A) = (glob A){m} /\ res = f (glob A){m}] = 1%r) /\
  (forall &m st (x: glob A), st = f x => Pr[A.setState(st) @ &m : glob A = x] = 1%r) /\
  islossless A.setState.

declare axiom A_continue_ll : islossless A.continue.
declare axiom A_finish_ll : islossless A.finish.

(* The boring stuff... *)
local lemma Wrap_A_rewindable :
  exists (f : glob AdvWrapper(A) -> state_t), injective f /\
  (forall &m, Pr[AdvWrapper(A).getState() @ &m : (glob AdvWrapper(A)) = (glob AdvWrapper(A)){m} /\ res = f (glob AdvWrapper(A)){m}] = 1%r) /\
  (forall &m st (x: glob AdvWrapper(A)), st = f x => Pr[AdvWrapper(A).setState(st) @ &m : glob AdvWrapper(A) = x] = 1%r) /\
  islossless AdvWrapper(A).setState.
proof.
(* FIXME *)
admit.
qed.

local lemma Wrap_A_continue_ll : islossless AdvWrapper(A).continue.
proof.
islossless; [exact A_continue_ll | exact A_finish_ll].
qed.

local lemma Wrap_A_finish_ll : islossless AdvWrapper(A).finish.
proof.
islossless.
qed.

local equiv wrap_koa_success_equiv :
  IRunnerRO(KeyGen, AdvWrapper(A), LRO).run ~ EUF_KOA_ROM(LRO, Schnorr, AdvRunner(A)).main :
  LRO.m{1} = empty /\ ={glob A} ==> success_ro LRO.m{1} res{1}.`1 = res{2}.
proof.
proc.
inline RunnerRO EUF_KOA.
inline AdvWrapper(A).finish Schnorr(LRO).verify.
inline AdvRunner.
splitwhile {1} 5 : (c < Q).
inline {1} (2) AdvWrapper(A).continue.
have lro_equiv : equiv[LRO.get ~ LRO.get : ={arg, glob LRO} ==> ={res, glob LRO}].
+ sim.
seq 5 6 : (
  ={q, glob A, glob LRO} /\
  c{1} = Q /\ c{1} = AdvWrapper.c{1} /\
  AdvWrapper.pk{1} = pk{2}
).
+ while (={q, c, glob A, glob LRO} /\ c{1} = AdvWrapper.c{1} /\ c{1} <= Q).
  + inline AdvWrapper.
    rcondt {1} 3.
    + auto.
      call (_ : true) => //.
    wp; call (_ : true).
    wp; call lro_equiv.
    skip => /#.
  inline.
  wp; call (_ : true).
  auto => />.
  (* FIXME: Clear the wrong Q_pos. *)
  smt(AdvStopping.Q_pos).
rcondt {1} 1.
+ auto => /#.
rcondf {1} 3.
+ auto.
  call (_ : true) => //.
rcondf {1} 9.
+ auto.
  call (_ : true); wp.
  call (_ : true) => //.
conseq
  (_ : _ ==> is_some o{1}.`1 = r{2})
  (_ : _ ==> is_some o.`1 => oget o.`1 \in LRO.m).
+ smt().
+ inline (2) LRO.get.
  auto.
  call (_ : true); wp; call (_ : true) => //.
  skip; smt(mem_set).
wp; call lro_equiv.
wp; call (_ : true).
wp; call lro_equiv.
skip => /#.
qed.

local hoare success_impl_verify :
  IRunnerRO(KeyGen, AdvWrapper(A), LRO).run :
  true ==>
  let (qo, resp) = res in
  let q = oget qo in
    success_ro LRO.m qo => verify (g ^ KeyGen.sk) (q.`2, oget LRO.m.[q], resp).
proof.
proc; inline * -LRO.get -AdvWrapper(A).continue.
seq 12 : (AdvWrapper.pk = g ^ KeyGen.sk /\ q = AdvWrapper.q).
+ while (q = AdvWrapper.q).
  + inline AdvWrapper(A).continue.
    by wp.
  wp; call (_ : true).
  auto.
inline.
auto => /#.
qed.

module RedAdv (A : ForkableAdv) : Adv_DL = {
  proc guess(h : group) : exp option = {
    var qo, resp1, resp2, ret;

    (qo, resp1, resp2) <@ ForkerRO(AdvWrapper(A)).run(h);
    ret <- omap (fun q =>
      let (_, com, __) = q in extractor h
        (com, oget IForkerRO.m1.[q], resp1)
        (com, oget IForkerRO.m2.[q], resp2)
    ) qo;

    return ret;
  }
}.

(* This is (more or less) just Exp_DL(RedAdv(A)) with the adversary
 * inlined and the challenge generation moved to IForkerRO. *)
local module Exp_DL0 (A : ForkableAdv) = {
  proc main() : bool = {
    var qo, resp1, resp2, ret;

    (qo, resp1, resp2) <@ IForkerRO(KeyGen, AdvWrapper(A)).run();
    ret <- omap (fun q =>
      let (_, com, __) = q in extractor (g ^ KeyGen.sk)
        (com, oget IForkerRO.m1.[q], resp1)
        (com, oget IForkerRO.m2.[q], resp2)
    ) qo;

    return ret = Some KeyGen.sk;
  }
}.

local equiv dl_exp_exp0_equiv :
  Exp_DL(RedAdv(A)).main ~ Exp_DL0(A).main : ={glob A} ==> ={res}.
proof.
proc.
rewrite equiv [{2} 1 -(gen_then_fork_ro_equiv KeyGen (AdvWrapper(A)))].
inline RedAdv GenThenForkRO KeyGen.
wp.
call (_ : ={arg, glob A} ==> ={res, IForkerRO.m1, IForkerRO.m2}); 1: sim.
auto.
qed.

(* NOTE: For KOA security, we don't have to assume anything about dnonce. *)

lemma schnorr_koa_secure &m :
  Pr[Exp_DL(RedAdv(A)).main() @ &m : res] >=
    Pr[EUF_KOA_ROM(LRO, Schnorr, AdvRunner(A)).main() @ &m : res] ^ 2 / (Q + 1)%r -
    Pr[EUF_KOA_ROM(LRO, Schnorr, AdvRunner(A)).main() @ &m : res]  / (size (to_seq (support dchal)))%r.
proof.
have -> : Pr[Exp_DL(RedAdv(A)).main() @ &m : res] = Pr[Exp_DL0(A).main() @ &m : res].
+ byequiv dl_exp_exp0_equiv => //.
byphoare (_ : glob A = (glob A){m} ==> _) => //.
proc.
wp.
pose P_in  := (
  fun (arg : glob KeyGen * glob AdvWrapper(A)) =>
    arg.`2.`6 = (glob A){m}
).
pose P_out := (
  fun (arg : glob KeyGen * (query_t option * resp_t) * (query_t, chal_t) fmap) =>
    let (sk, o, m) = arg in
    let (qo, resp) = o in
    let q = oget qo in
    verify (g ^ sk) (q.`2, oget m.[q], resp)
).
call (
  forking_lemma_ro
  KeyGen (AdvWrapper(A))
  Wrap_A_rewindable Wrap_A_continue_ll Wrap_A_finish_ll
  P_in P_out
  _ Pr[EUF_KOA_ROM(LRO, Schnorr, AdvRunner(A)).main() @ &m : res]  _
); rewrite /P_in /P_out /=.
+ conseq success_impl_verify => /#.
+ bypr => &m0 mem_eqs.
  byequiv wrap_koa_success_equiv => /#.
skip => />.
smt(extractor_corr pow_bij).
qed.

end section SECURITY_EUF_KOA.
