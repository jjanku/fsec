pragma Goals:printall.

require import AllCore FMap List Distr Finite FelTactic StdBigop StdOrder Mu_mem.
import RealOrder.

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
import DSS.Stateless.

(* In the simulator, we sample response from dt. *)
op dnonce : exp distr = dt.
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

(* Number of random oracle queries. *)
const QR : {int | 1 <= QR} as QR_pos.

(* Number of signing queries. *)
const QS : {int | 0 <= QS} as QS_ge0.

require Stopping.
clone import Stopping as AdvStopping with
  type in_t    <- pk_t,
  type out_t   <- msg_t * sig_t,
  type query_t <- query_t,
  type resp_t  <- chal_t,
  op   Q       <- QR
proof *.
realize Q_pos by exact QR_pos.

require ForkingRO.
clone import ForkingRO as AdvForkingRO with
  type in_t    <- pk_t,
  (* All other important parts of the forgery
   * are included in the critical query.*)
  type aux_t   <- resp_t,
  type query_t <- query_t,
  type resp_t  <- chal_t,
  op   dresp   <- dchal,
  op   Q       <- QR + 1
proof *.
realize Q_pos     by smt(QR_pos).
realize dresp_ll  by exact dchal_ll.
realize dresp_uni by exact dchal_uni.

section SECURITY_EUF_KOA.

module (FAdv_KOA_Runner (A : Stoppable) : Adv_EUFKOA_ROM) (O : Oracle) = {
  proc forge = Runner(A, O).run
}.

module type FAdv_KOA = {
  include Stoppable
  include ForkingLRO.Rewindable
}.

(* A simple wrapper that runs A and makes one extra query
 * at the end to verify A's forgery. *)
(* TODO: Consider creating a generic module for this type
 * of transformation, it is probably a common pattern. *)
module AdvWrapper (A : FAdv_KOA) : ForkableRO = {
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

    if (c < QR) {
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

declare module A <: FAdv_KOA {-LRO, -AdvWrapper, -IForkerRO, -KeyGen, -ConstGen}.

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
  IRunnerRO(KeyGen, AdvWrapper(A), LRO).run ~ EUF_KOA_ROM(LRO, Schnorr, FAdv_KOA_Runner(A)).main :
  LRO.m{1} = empty /\ ={glob A} ==> success_ro LRO.m{1} res{1}.`1 = res{2}.
proof.
proc.
inline RunnerRO EUF_KOA.
inline AdvWrapper(A).finish Schnorr(LRO).verify.
inline FAdv_KOA_Runner.
splitwhile {1} 5 : (c < QR).
inline {1} (2) AdvWrapper(A).continue.
have lro_equiv : equiv[LRO.get ~ LRO.get : ={arg, glob LRO} ==> ={res, glob LRO}].
+ sim.
seq 5 6 : (
  ={q, glob A, glob LRO} /\
  c{1} = QR /\ c{1} = AdvWrapper.c{1} /\
  AdvWrapper.pk{1} = pk{2}
).
+ while (={q, c, glob A, glob LRO} /\ c{1} = AdvWrapper.c{1} /\ c{1} <= QR).
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
  smt(QR_pos).
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

module RedAdv (A : FAdv_KOA) : Adv_DL = {
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
local module Exp_DL0 (A : FAdv_KOA) = {
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
    Pr[EUF_KOA_ROM(LRO, Schnorr, FAdv_KOA_Runner(A)).main() @ &m : res] ^ 2 / (QR + 1)%r -
    Pr[EUF_KOA_ROM(LRO, Schnorr, FAdv_KOA_Runner(A)).main() @ &m : res]  / (size (to_seq (support dchal)))%r.
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
  _ Pr[EUF_KOA_ROM(LRO, Schnorr, FAdv_KOA_Runner(A)).main() @ &m : res]  _
); rewrite /P_in /P_out /=.
+ conseq success_impl_verify => /#.
+ bypr => &m0 mem_eqs.
  byequiv wrap_koa_success_equiv => /#.
skip => />.
smt(extractor_corr pow_bij).
qed.

end section SECURITY_EUF_KOA.

section SECURITY_EUF_CMA.

module type FAdv_CMA (SO : SOracle_CMA_ROM) = {
  include Stoppable
  include ForkingLRO.Rewindable
}.

module (FAdv_CMA_Runner (A : FAdv_CMA) : Adv_EUFCMA_ROM) (RO : Oracle) (SO : SOracle_CMA_ROM) = {
  proc forge = Runner(A(SO), RO).run
}.

module (BoundedSO : Oracle_CMA_ROM) (RO : Oracle) (S : Scheme) = {
  proc init       = O_CMA_ROM_Default(RO, S).init
  proc nr_queries = O_CMA_ROM_Default(RO, S).nr_queries
  proc fresh      = O_CMA_ROM_Default(RO, S).fresh

  proc sign(m : msg_t) : sig_t = {
    var n, s;

    n <@ nr_queries();
    if (n < QS) {
      s <@ O_CMA_ROM_Default(RO, S).sign(m);
    } else {
      s <- witness;
    }

    return s;
  }
}.

module Red_CMA_KOA (A : FAdv_CMA) : FAdv_KOA = {
  var q : query_t
  var m : (query_t, chal_t) fmap

  proc program(q : query_t, r : chal_t) : chal_t = {
    if (q \notin m) {
      m.[q] <- r;
    }
    return oget m.[q];
  }

  module Simulator : SOracle_CMA_ROM = {
    var pk : pk_t
    var signed : msg_t list
    var bad : bool

    proc init(pk0 : pk_t) = {
      pk <- pk0;
      bad <- false;
      signed <- [];
    }

    proc sign(msg : msg_t) : sig_t = {
      var com, chal, resp, q, s;

      if (size signed < QS) {
        chal <$ dchal;
        resp <$ dt;
        com <- (g ^ resp) * (pk ^ -chal);

        q <- (pk, com, msg);
        if (q \in m) {
          bad <- true;
        }
        m.[q] <- chal;

        s <- (com, resp);
        signed <- signed ++ [msg];
      } else {
        s <- witness;
      }

      return s;
    }
  }

  (* FIXME: Need to handle global vars. *)
  proc getState() : state_t = {
    return witness;
  }

  proc setState(st : state_t) = {
  }

  proc init_loc(i : pk_t) = {
    q <- witness;
    m <- empty;
    Simulator.init(i);
  }

  proc init_adv(i : pk_t) : query_t = {
    q <@ A(Simulator).init(i);
    return q;
  }

  proc init(i : pk_t) : query_t = {
    var q;
    init_loc(i);
    q <@ init_adv(i);
    return q;
  }

  proc continue(r : chal_t) : query_t = {
    r <@ program(q, r);
    q <@ A(Simulator).continue(r);
    return q;
  }

  proc finish(r : chal_t) : msg_t * sig_t = {
    var ms;
    r <@ program(q, r);
    ms <@ A(Simulator).finish(r);
    return ms;
  }
}.

declare module A <: FAdv_CMA {-Red_CMA_KOA, -LRO, -O_CMA_Default}.

declare axiom A_init_ll : forall (SO <: SOracle_CMA_ROM),
  islossless SO.sign => islossless A(SO).init.
declare axiom A_continue_ll : forall (SO <: SOracle_CMA_ROM),
  islossless SO.sign => islossless A(SO).continue.
declare axiom A_finish_ll : forall (SO <: SOracle_CMA_ROM),
  islossless SO.sign => islossless A(SO).finish.

(* This module corresponds to FAdv_KOA_Runner(Red_CMA_KOA).
 * Its function is to enable the application of the fel tactic. *)
local module Red_Runner (A : FAdv_CMA) (O : Oracle) = {
  module Red = Red_CMA_KOA(A)

  var d : int

  proc program(q : query_t, r : chal_t) : chal_t = {
    (* This condition always evaluates to true when the procedure is called
     * inside forge(). It allows us to easily establish the invariant
     * fsize Red.m <= QR + QS needed for the analysis of the bad event. *)
    if (d < QR) {
      if (q \notin Red.m) {
        Red.m.[q] <- r;
      }
      r <- oget Red.m.[q];
      d <- d + 1;
    }
    return r;
  }

  proc forge(i : pk_t) : msg_t * sig_t = {
    var o, q, r, c;

    Red.init_loc(i);
    d <- 0;
    Red.q <@ A(Red.Simulator).init(i);
    q <- Red.q;
    c <- 1;
    while (c < QR){
      r <@ O.get(q);
      r <@ program(Red.q, r);
      Red.q <@ A(Red.Simulator).continue(r);
      q <- Red.q;
      c <- c + 1;
    }
    r <@ O.get(q);
    r <@ program(Red.q, r);
    o <@ A(Red.Simulator).finish(r);

    return o;
  }
}.

local lemma pr_bad_runner_eq &m pk :
  Pr[FAdv_KOA_Runner(Red_CMA_KOA(A), LRO).forge(pk) @ &m : Red_CMA_KOA.Simulator.bad] =
  Pr[Red_Runner(A, LRO).forge(pk) @ &m : Red_CMA_KOA.Simulator.bad].
proof.
byequiv => //.
proc.
inline Red_CMA_KOA(A).init Red_CMA_KOA(A).continue Red_CMA_KOA(A).finish.
wp.
call (_ : ={glob Red_CMA_KOA}); 1: sim.
have program_equiv : forall d_val, equiv[
  Red_CMA_KOA(A).program ~ Red_Runner(A, LRO).program :
  ={arg, Red_CMA_KOA.m} /\ Red_Runner.d{2} = d_val /\ d_val < QR ==>
  ={res, Red_CMA_KOA.m} /\ Red_Runner.d{2} = d_val + 1
].
+ move => d_val.
  proc.
  rcondt {2} 1 => //.
  auto.
call (program_equiv (QR - 1)).
wp.
call (_ : ={glob LRO}); 1: sim.
while (
  ={glob A, glob Red_CMA_KOA, glob LRO, q, c} /\ c{2} <= QR /\ Red_Runner.d{2} = c{2} - 1
).
+ wp => /=.
  call (_ : ={glob Red_CMA_KOA}); 1: sim.
  exlim Red_Runner.d{2} => d_val.
  call (program_equiv d_val).
  wp.
  call (_ : ={glob LRO}); 1: sim.
  auto => /#.
inline Red_CMA_KOA(A).init_adv.
wp.
call (_ : ={glob Red_CMA_KOA}); 1: sim.
wp.
inline.
auto => />.
smt(QR_pos).
qed.

local lemma pr_bad_runner &m pk :
  Pr[FAdv_KOA_Runner(Red_CMA_KOA(A), LRO).forge(pk) @ &m : Red_CMA_KOA.Simulator.bad] <=
  QS%r * (QS + QR)%r / order%r.
proof.
rewrite pr_bad_runner_eq.
fel
  2
  (size Red_CMA_KOA.Simulator.signed)
  (fun ctr => (QS + QR)%r / order%r)
  QS
  Red_CMA_KOA.Simulator.bad
  [
    Red_Runner(A, RO.RO).Red.Simulator.sign : (size Red_CMA_KOA.Simulator.signed < QS);
    Red_Runner(A, RO.RO).program : false
  ]
  (
    fsize Red_CMA_KOA.m <= Red_Runner.d + size Red_CMA_KOA.Simulator.signed /\
    Red_Runner.d <= QR /\ size Red_CMA_KOA.Simulator.signed <= QS) => //.
+ rewrite Bigreal.sumri_const //.
  exact QS_ge0.
+ inline.
  auto => />.
  smt(QS_ge0 QR_pos fsize_empty).
+ move => b c.
  proc.
  auto => />.
  smt(fsize_set).
+ proc.
  rcondt 1; 1: auto.
  seq 1 : true
    1%r ((QS + QR)%r / order%r)
    0%r _
    (! Red_CMA_KOA.Simulator.bad /\ fsize Red_CMA_KOA.m <= QS + QR) => //.
  + auto => /#.
  inline.
  wp => /=.
  rnd.
  skip => />.
  move => &hr _ size_bound.
  have : (fsize Red_CMA_KOA.m{hr})%r / order%r <= (QS + QR)%r / order%r.
  + apply ler_pmul2r.
    + smt(invr_gt0 gt0_order).
    smt().
  apply ler_trans.
  pose P := (fun (q : query_t) (x : exp) => q.`2 = g ^ x * Red_CMA_KOA.Simulator.pk{hr} ^ -chal{hr}).
  move : (mu_mem_le_fsize Red_CMA_KOA.m{hr} dt P (1%r / order%r) _).
  + move => q _.
    pose s := loge (q.`2 /  Red_CMA_KOA.Simulator.pk{hr} ^ -chal{hr}).
    rewrite -(dt1E s).
    apply mu_le.
    move => x _ rel /=.
    rewrite /pred1 /s rel.
    by rewrite -mulcA mulcV mulcC mul1c loggK.
  apply ler_trans.
  apply mu_le => /#.
+ move => c.
  proc; inline.
  rcondt 1; 1: auto.
  seq 5 : (
    c = size Red_CMA_KOA.Simulator.signed /\ c < QS /\
    fsize Red_CMA_KOA.m <= Red_Runner.d + size Red_CMA_KOA.Simulator.signed /\
  Red_Runner.d <= QR /\ size Red_CMA_KOA.Simulator.signed <= QS
  ); 1: auto.
  auto.
  smt(size_cat fsize_set).
+ move => b c.
  proc.
  rcondf 1; 1: auto.
  auto.
qed.

local lemma pr_bad_game &m :
  Pr[EUF_KOA_ROM(LRO, Schnorr, FAdv_KOA_Runner(Red_CMA_KOA(A))).main() @ &m : Red_CMA_KOA.Simulator.bad] <=
  QS%r * (QS + QR)%r / order%r.
proof.
byphoare => //.
proc.
inline EUF_KOA.
seq 3 : Red_CMA_KOA.Simulator.bad
  (QS%r * (QS + QR)%r / order%r) 1%r _ 0%r => //.
+ call (_ : true ==> Red_CMA_KOA.Simulator.bad).
  + bypr => &m0 /=.
    exact pr_bad_runner.
  auto.
hoare.
wp.
by call (_ : true).
qed.

local op signed (qs : msg_t list) (q : query_t) = q.`3 \in qs.

local op dom_supset ['a 'b] (m1 m2 : ('a, 'b) fmap) =
  forall a, a \notin m1 => a \notin m2.

(* Red_CMA_KOA.m is an "overlay" over LRO:
 * - RO queries are routed to LRO. When LRO returns a response, Red_CMA_KOA.m
 *   is set to this response unless the response is already fixed. In such case,
     the old value takes precedence.
 * - Red_CMA_KOA.m may contain values not present in LRO becaus Red_CMA_KOA.m
     may be programmed by the Simulator (for signature queries). *)
local op overlay (m m' : (query_t, chal_t) fmap) (qs : msg_t list) =
  dom_supset m' m /\ eq_except (signed qs) m' m.

local equiv simulator_equiv :
  BoundedSO(LRO, Schnorr(LRO)).sign ~ Red_CMA_KOA(A).Simulator.sign :
  ={arg} /\
    O_CMA_Default.qs{1} = Red_CMA_KOA.Simulator.signed{2} /\
    g ^ O_CMA_Default.sk{1} = Red_CMA_KOA.Simulator.pk{2} /\
    LRO.m{1} = Red_CMA_KOA.m{2} /\
    overlay LRO.m{2} Red_CMA_KOA.m{2} Red_CMA_KOA.Simulator.signed{2} ==>
  !Red_CMA_KOA.Simulator.bad{2} => ={res} /\
    O_CMA_Default.qs{1} = Red_CMA_KOA.Simulator.signed{2} /\
    LRO.m{1} = Red_CMA_KOA.m{2} /\
    overlay LRO.m{2} Red_CMA_KOA.m{2} Red_CMA_KOA.Simulator.signed{2}.
proof.
proc.
inline BoundedSO.
sp.
if => //; 2: auto.
inline.
seq 8 4 : (
  r{1} = chal{2} /\ x{1} = q{2} /\ ={com} /\ (nonce + sk * r){1} = resp{2} /\ m0{1} = msg{2} /\
  O_CMA_Default.qs{1} = Red_CMA_KOA.Simulator.signed{2} /\ LRO.m{1} = Red_CMA_KOA.m{2} /\
  overlay LRO.m{2} Red_CMA_KOA.m{2} Red_CMA_KOA.Simulator.signed{2} /\ x{1}.`3 = m0{1}
).
+ swap{1} 8 -7.
  wp.
  rnd (fun nonce, nonce + sk{1} * r{1}) (fun resp, resp - sk{1} * r{1}).
  wp.
  rnd.
  skip => />.
  progress; algebra.
if {2}; 1: auto.
rcondt{1} 1; 1: auto.
auto => />.
rewrite get_set_sameE cats1 /=.
move => &2.
pose ms := Red_CMA_KOA.Simulator.signed{2}; pose m := q{2}.`3.
have signed_sub : predU (signed ms) (pred1 q{2}) <= signed (rcons ms m).
+ rewrite /(<=) /predU /signed => q.
  smt(mem_rcons).
smt(eq_exceptSm eq_except_sub mem_set).
qed.

local lemma ro_get_eq_except (X : query_t -> bool) :
  equiv[LRO.get ~ LRO.get :
    eq_except X LRO.m{1} LRO.m{2} /\ ={arg} /\ ! X arg{1} ==> ={res}
  ].
proof.
proc.
seq 1 1 : (#pre /\ ={r}); 1: auto.
if.
+ smt(eq_except_notp_in).
+ auto; smt(eq_except_set_eq).
auto => /#.
qed.

(* This is for outline purposes only. *)
local module RedO = {
  proc get(q : query_t) : resp_t = {
    var r0, r1 : resp_t;
    r0 <@ LRO.get(q);
    r1 <- r0;
    r1 <@ Red_CMA_KOA(A).program(Red_CMA_KOA.q, r1);
    return r1;
  }
}.

local equiv lro_redo_equiv :
  LRO.get ~ RedO.get :
  ={arg} /\ arg{2} = Red_CMA_KOA.q{2} /\
    LRO.m{1} = Red_CMA_KOA.m{2} /\
    overlay LRO.m{2} Red_CMA_KOA.m{2} Red_CMA_KOA.Simulator.signed{2} ==>
  ={res} /\
    LRO.m{1} = Red_CMA_KOA.m{2} /\
    overlay LRO.m{2} Red_CMA_KOA.m{2} Red_CMA_KOA.Simulator.signed{2}.
proof.
proc; inline.
sp.
seq 1 1 : (#pre /\ ={r}); 1: auto.
if {1}.
+ rcondt {2} 1; 1: auto => /#.
  rcondt {2} 6; 1: auto.
  auto; smt(get_set_sameE eq_except_set_eq mem_set).
rcondf {2} 6; 1: auto.
case (! signed Red_CMA_KOA.Simulator.signed{2} q{2}).
+ rcondf {2} 1.
  + auto; smt(eq_except_notp_in).
  auto.
auto => />.
move => &2 sup eq q_in q_signed _.
pose signed_qs := signed Red_CMA_KOA.Simulator.signed{2}.
have signed_U_pred1q : (predU signed_qs (pred1 Red_CMA_KOA.q{2})) = signed_qs by smt().
smt(eq_exceptmS mem_set).
qed.

local equiv lro_redo_inv :
  LRO.get ~ RedO.get :
  !Red_CMA_KOA.Simulator.bad{2} => ={arg} /\ arg{2} = Red_CMA_KOA.q{2} /\
    LRO.m{1} = Red_CMA_KOA.m{2} /\
    overlay LRO.m{2} Red_CMA_KOA.m{2} Red_CMA_KOA.Simulator.signed{2} ==>
  !Red_CMA_KOA.Simulator.bad{2} => ={res} /\
    LRO.m{1} = Red_CMA_KOA.m{2} /\
    overlay LRO.m{2} Red_CMA_KOA.m{2} Red_CMA_KOA.Simulator.signed{2}.
proof.
proc *.
case (Red_CMA_KOA.Simulator.bad{2}).
+ inline; auto.
call lro_redo_equiv.
auto => /#.
qed.

local phoare simulator_bad_ll : [
  Red_CMA_KOA(A).Simulator.sign : Red_CMA_KOA.Simulator.bad ==> Red_CMA_KOA.Simulator.bad
] = 1%r.
proof.
proc.
if; auto.
smt(dchal_ll dt_ll).
qed.

local lemma pr_koa_cma &m :
  (* FIXME: This is likely a bug in the theory? LRO should not be specified twice? *)
  Pr[EUF_CMA_ROM(LRO, Schnorr, FAdv_CMA_Runner(A), BoundedSO, LRO).main() @ &m : res] <=
  Pr[EUF_KOA_ROM(LRO, Schnorr, FAdv_KOA_Runner(Red_CMA_KOA(A))).main() @ &m : res] +
  Pr[EUF_KOA_ROM(LRO, Schnorr, FAdv_KOA_Runner(Red_CMA_KOA(A))).main() @ &m : Red_CMA_KOA.Simulator.bad].
proof.
byequiv => //.
proc.
inline EUF_CMA EUF_KOA.
swap{1} 6 -1.
seq 4 3 : (!Red_CMA_KOA.Simulator.bad{2} =>
  ={pk, m, sig} /\ eq_except (signed O_CMA_Default.qs{1}) LRO.m{1} LRO.m{2}
); first last.
+ inline BoundedSO.
  sp.
  case (!is_fresh{1}).
  + inline; auto.
  case (Red_CMA_KOA.Simulator.bad{2}).
  + inline; auto.
  inline Schnorr.
  wp.
  exlim (O_CMA_Default.qs{1}) => qs.
  call (ro_get_eq_except (signed qs)).
  auto => /#.
inline FAdv_CMA_Runner FAdv_KOA_Runner.
inline Red_CMA_KOA -Red_CMA_KOA(A).program.
outline {2} [18-20] r2 <@ RedO.get.
wp.
call (_ : Red_CMA_KOA.Simulator.bad,
  O_CMA_Default.qs{1} = Red_CMA_KOA.Simulator.signed{2} /\
  g ^ O_CMA_Default.sk{1} = Red_CMA_KOA.Simulator.pk{2} /\
  LRO.m{1} = Red_CMA_KOA.m{2} /\
  overlay LRO.m{2} Red_CMA_KOA.m{2} Red_CMA_KOA.Simulator.signed{2}
).
+ move => SO; exact (A_finish_ll SO).
+ conseq simulator_equiv => //.
+ move => _ _; islossless.
+ move => _; exact simulator_bad_ll.
call lro_redo_inv.
while (
  ={pk, c} /\ q{2} = Red_CMA_KOA.q{2} /\
  (!Red_CMA_KOA.Simulator.bad{2} =>
    g ^ O_CMA_Default.sk{1} = Red_CMA_KOA.Simulator.pk{2} /\
    ={glob A, q} /\ O_CMA_Default.qs{1} = Red_CMA_KOA.Simulator.signed{2} /\
    LRO.m{1} = Red_CMA_KOA.m{2} /\
    overlay LRO.m{2} Red_CMA_KOA.m{2} Red_CMA_KOA.Simulator.signed{2})
).
+ wp => /=.
  outline {2} [1-3] r1 <@ RedO.get.
  call (_ : Red_CMA_KOA.Simulator.bad,
    O_CMA_Default.qs{1} = Red_CMA_KOA.Simulator.signed{2} /\
    g ^ O_CMA_Default.sk{1} = Red_CMA_KOA.Simulator.pk{2} /\
    LRO.m{1} = Red_CMA_KOA.m{2} /\
    overlay LRO.m{2} Red_CMA_KOA.m{2} Red_CMA_KOA.Simulator.signed{2}
  ).
  + move => SO; exact (A_continue_ll SO).
  + conseq simulator_equiv => //.
  + move => _ _; islossless.
  + move => _; exact simulator_bad_ll.
  call lro_redo_inv.
  auto => /#.
wp.
call (_ : Red_CMA_KOA.Simulator.bad,
  O_CMA_Default.qs{1} = Red_CMA_KOA.Simulator.signed{2} /\
  g ^ O_CMA_Default.sk{1} = Red_CMA_KOA.Simulator.pk{2} /\
  LRO.m{1} = Red_CMA_KOA.m{2} /\
  overlay LRO.m{2} Red_CMA_KOA.m{2} Red_CMA_KOA.Simulator.signed{2}
).
+ move => SO; exact (A_init_ll SO).
+ conseq simulator_equiv => //.
+ move => _ _; islossless.
+ move => _; exact simulator_bad_ll.
inline; auto => /#.
qed.

end section SECURITY_EUF_CMA.
