(* This is a short showcase of how Coq can be used.
   It is not a tutorial; it is not complete in a sense, that you will probably
   not be able to re-create the examples on your own without following a proper
   Coq tutorial first. *)

(* Let us import some standard modules. *)
Require List.
Import List.
Import List.ListNotations.

(* Here we have some story:
   We send an astronaut to Mars. We want him to record a diary of
   the journey. There will be just three option for every day:
   bad day, ordinary day and good day. *)
Inductive day :=
  | bad_day : day
  | ordinary_day : day
  | good_day : day.

(* We will be encoding the diary as a stream of bits. *)
Inductive bit :=
  | bit_0 : bit
  | bit_1 : bit.

(* We want to efficiently encode the diary and we know the astronaut is a
   grumbler, so he will record most of his days as bad days. *)

(* To store the diary efficiently we will use variable length codes.
   We know the astronaut is a pesymist, so he will record most of his days
   as bad days. To take advantage of this let's use a single bit code for bad
   day and two bit codes for the others.
   Let's have some play with simple encoding / decoding functions. *)

Definition encode_single (l : day) : (list bit) :=
  match l with
  | bad_day => [bit_0]
  | ordinary_day => [bit_1; bit_0]
  | good_day => [bit_1; bit_1]
  end.

Definition decode_single (lb : list bit) : option day :=
  match lb with
  | [bit_0] => Some bad_day
  | [bit_1; bit_0] => Some ordinary_day
  | [bit_1; bit_1] => Some good_day
  | _ => None
  end.

Example encode_single_ex0 :
  encode_single ordinary_day = [bit_1; bit_0].
Proof. reflexivity. Qed.

Example decode_single_ex0 :
  decode_single [bit_1; bit_0] = Some ordinary_day.
Proof. reflexivity. Qed.

Theorem encode_decode_single_correct :
  forall (l : day),
    decode_single (encode_single l) = Some l.
Proof.
  intros l.
  destruct l.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Fixpoint encode_many (ll : list day) : list bit :=
  match ll with
  | [] => []
  | l :: llt => encode_single l ++ encode_many llt
  end.

Fixpoint decode_many (lb : list bit) : option (list day) :=
  match lb with
  | [] => Some []
  | bit_0 :: lbt =>
    match decode_many lbt with
    | None => None
    | Some llt => Some (bad_day :: llt)
    end
  | bit_1 :: bit_0 :: lbt =>
    match decode_many lbt with
    | None => None
    | Some llt => Some (ordinary_day :: llt)
    end
  | bit_1 :: bit_1 :: lbt =>
    match decode_many lbt with
    | None => None
    | Some llt => Some (good_day :: llt)
    end
  | _ => None
  end.

(* Let's skip examples and go directly to generic case.
   We will need to use induction this time. *)

Theorem encode_decode_many_correct :
  forall ll,
    decode_many (encode_many ll) = Some ll.
Proof.
  intros ll.
  induction ll as [ | llh llt IH].
  - reflexivity.
  - simpl.
    destruct llh.
    + simpl.
      rewrite IH.
      reflexivity.
    + simpl.
      rewrite IH.
      reflexivity.
    + simpl.
      rewrite IH.
      reflexivity.
Qed.





(* The functions above were not the simplest for of specification we could
   think of. We had to specify both encode and decode procedure. We could not
   fully reuse the decode specification for single day in specification of
   decode function for many bits.

   This was fun, but let's a have simple formal definition independent from
   implementation. *)

Inductive corresponds_single : list bit -> day -> Prop :=
  | cs_bad : corresponds_single [bit_0] bad_day
  | cs_ordinary : corresponds_single [bit_1; bit_0] ordinary_day
  | cs_good : corresponds_single [bit_1; bit_1] good_day.

Inductive corresponds_many : list bit -> list day -> Prop :=
  | cm_empty : corresponds_many [] []
  | cm_more :
    forall lb1 lb2 l ll,
      corresponds_single lb1 l ->
      corresponds_many lb2 ll ->
      corresponds_many (lb1 ++ lb2) (l :: ll).

(* In Coq, when we define inductive propositions, it is assumed that they are
   true if, and only if, they can be derived from the given constructors. This
   can be used in proofs: when we are given some assumption, we can reason by
   cases, assuming that at least one of propositions contructor is true. *)

(* Now there are many things we could prove. E.g.
  a) our encode/decode functions realize the above definitions.
  b) for every stream of day, there exists a stream of bits encoding it (at
     least one)
  c) for given stream of bits there is at most one list of days *)

Theorem encode_correct :
  forall ll,
    corresponds_many (encode_many ll) ll.
Proof.
  intros ll.
  induction ll.
  - simpl.
    apply cm_empty.
  - simpl.
    apply cm_more.
    + destruct a.
      * simpl.
        apply cs_bad.
      * simpl.
        apply cs_ordinary.
      * simpl.
        apply cs_good.
    + apply IHll.
Qed.

Theorem decode_correct :
  forall lb ll,
    corresponds_many lb ll -> decode_many lb = Some ll.
Proof.
  intros lb ll H.
  induction H.
  - (* cm_empty *)
    reflexivity.
  - (* cm_more *)
    inversion H.
    + simpl.
      rewrite IHcorresponds_many.
      reflexivity.
    + simpl.
      rewrite IHcorresponds_many.
      reflexivity.
    + simpl.
      rewrite IHcorresponds_many.
      reflexivity.
Qed.

Theorem can_encode_every_stream :
  forall ll,
    exists lb,
      corresponds_many lb ll.
Proof.
  intros ll.
  exists (encode_many ll).
  apply encode_correct.
Qed.

Theorem decode_deterministic :
  forall lb ll1 ll2,
    corresponds_many lb ll1 ->
    corresponds_many lb ll2 ->
    ll1 = ll2.
Proof.
  intros.
  apply decode_correct in H.
  apply decode_correct in H0.
  rewrite H in H0.
  inversion H0.
  reflexivity.
Qed.

(* For proper tutorial, best choice seems to be:
   https://softwarefoundations.cis.upenn.edu/lf-current/index.html *)









