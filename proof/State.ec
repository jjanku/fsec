pragma Goals:printall.

require import AllCore.

type state_t.
op pair_st : state_t * state_t -> state_t.
op unpair_st : state_t -> state_t * state_t.
axiom pair_st_inj : injective pair_st.
axiom pair_st_can : cancel pair_st unpair_st.

op tuple3_st abc =
  let (a, b, c) = abc in
  pair_st (a, pair_st (b, c)).
op untuple3_st abc =
  let (a, bc) = unpair_st abc in
  let (b, c)  = unpair_st bc in
  (a, b, c).
lemma tuple3_st_inj : injective tuple3_st by smt(pair_st_inj).
lemma tuple3_st_can : cancel tuple3_st untuple3_st by smt(pair_st_can).

op tuple4_st abcd =
  let (a, b, c, d) = abcd in
  pair_st (a, tuple3_st (b, c, d)).
op untuple4_st abcd =
  let (a, bcd)  = unpair_st abcd in
  let (b, c, d) = untuple3_st bcd in
  (a, b, c, d).
lemma tuple4_st_inj : injective tuple4_st by smt(pair_st_inj).
lemma tuple4_st_can : cancel tuple4_st untuple4_st by smt(pair_st_can).

op tuple5_st abcde =
  let (a, b, c, d, e) = abcde in
  pair_st (a, tuple4_st (b, c, d, e)).
op untuple5_st abcde =
  let (a, bcde)  = unpair_st abcde in
  let (b, c, d, e) = untuple4_st bcde in
  (a, b, c, d, e).
lemma tuple5_st_inj : injective tuple5_st by smt(pair_st_inj).
lemma tuple5_st_can : cancel tuple5_st untuple5_st by smt(pair_st_can).

op tuple6_st abcdef =
  let (a, b, c, d, e, f) = abcdef in
  pair_st (a, tuple5_st (b, c, d, e, f)).
op untuple6_st abcdef =
  let (a, bcdef)  = unpair_st abcdef in
  let (b, c, d, e, f) = untuple5_st bcdef in
  (a, b, c, d, e, f).
lemma tuple6_st_inj : injective tuple6_st by smt(pair_st_inj).
lemma tuple6_st_can : cancel tuple6_st untuple6_st by smt(pair_st_can).

abstract theory ListState.

require import List.

(* Lists can be serialized if their elements can.
 * Additionally, we require serialization of ints. *)

type elem_t.
op elem2st : elem_t -> state_t.
op st2elem : state_t -> elem_t.
axiom elem2st_inj : injective elem2st.
axiom elem2st_can : cancel elem2st st2elem.

op int2st : int -> state_t.
op st2int : state_t -> int.
axiom int2st_inj : injective int2st.
axiom int2st_can : cancel int2st st2int.

op flatten_st (l : state_t list) =
  foldr (fun (st acc) => pair_st (st, acc)) witness l.

op unflatten_opr l_acc =
  let (l, acc) = l_acc in let (st, acc') = unpair_st acc in (l ++ [st], acc').

op unflatten_st_prefix (acc : state_t) (n : int) (pre : state_t list) =
  (iter n unflatten_opr (pre, acc)).`1.

op unflatten_st (acc : state_t) (n : int) =
  unflatten_st_prefix acc n [].

lemma flatten_st_inj : forall (l1 l2),
  size l1 = size l2 => flatten_st l1 = flatten_st l2 => l1 = l2.
proof.
apply seq2_ind => //=.
move => s1 s2 l1 l2.
rewrite /flatten_st /=.
smt(pair_st_inj).
qed.

lemma flatten_st_can : forall l,
  unflatten_st (flatten_st l) (size l) = l.
proof.
have strong : forall l pre,
  unflatten_st_prefix (flatten_st l) (size l) pre = pre ++ l;
first last.
+ move => l.
  apply strong.
elim. (* induction *)
+ move => pre /=.
  rewrite /unflatten_st_prefix.
  rewrite iter0 => //=.
  by rewrite cats0.
move => st l ind pre /=.
rewrite /unflatten_st_prefix.
rewrite addrC iterSr.
+ apply size_ge0.
rewrite {2} /unflatten_opr /=.
rewrite /flatten_st /=.
rewrite pair_st_can /=.
rewrite /unflatten_st_prefix /flatten_st in ind.
rewrite ind.
by rewrite -catA cat1s.
qed.

op list2st (l : elem_t list) =
  pair_st (int2st (size l), flatten_st (map elem2st l)).

op st2list (st : state_t) : elem_t list =
  let (n_st, l_st) = unpair_st st in
  map st2elem (unflatten_st l_st (st2int n_st)).

lemma list2st_inj : injective list2st.
proof.
rewrite /injective => l1 l2.
rewrite /list2st => st_eq.
have size_eq : size l1 = size l2.
+ smt(pair_st_inj int2st_inj).
have map_eq : map elem2st l1 = map elem2st l2.
+ smt(pair_st_inj flatten_st_inj size_map).
smt(elem2st_inj inj_map).
qed.

lemma list2st_can : cancel list2st st2list.
proof.
rewrite /cancel => l.
rewrite /st2list /list2st.
rewrite pair_st_can /=.
rewrite int2st_can.
have -> : size l = size (map elem2st l).
+ by rewrite size_map.
rewrite flatten_st_can.
rewrite -map_comp.
have -> : (st2elem \o elem2st = idfun).
+ smt(elem2st_can).
exact map_id.
qed.

end ListState.

(* TODO: Show that maps can be serialized if their keys and values can. *)
