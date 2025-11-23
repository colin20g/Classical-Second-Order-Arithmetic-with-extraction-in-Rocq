(**
   Author: Colin20G.

   The purpose of this text is to implement a version of classial second order arithmetic (SOA)
   and to prove, via Friedman Translation, that for every sigma_1 and pi_2 sentences,
   if classical second order arithmetic proves that sentence then not only oq/Rocq without
   assumption proves the same sentence, but in addition, the program which takes the sentence
   and its parameters and return a witness (in fact the smallest one) is a Rocq program.
   The reverse mathematics program has already established that in spite of the obvious
   limitations of SOA, a large part of mathematics (and probably almost everything seen in
   School up to undergratuate math level included) can be formalized and proven in it, at the
   price of sometimes heavy encoding (in fact reverse mathematics uses only a fragment of such
   a system).
   The reader is advised to look at "Subsystems of second order arithmetics" by
   Steven G. Simpson in order to discover the extent of what is doable in such a system.
 *)

(** Before we get started with SOA, we need an indispensable tool
    that can be reused freely for other purposes.
 *)

Section Extraction_of_witness_with_acc_for_decidable_properties.

(** In COQ ("why Rocq ?!") it is possible to extract a witness from every **decidable**
 arithmetical existential statement, thanks to the very simple
 program below, which uses the "Acc" predicate. *)

  Variable P: nat -> Prop.
  Hypothesis dec: forall n: nat, sumbool (P n) (~ P n).

  Inductive nat_back_auxiliary_relationship: nat -> nat -> Prop:=
    nbar_intro: forall n: nat, (~ P n) -> nat_back_auxiliary_relationship (S n) n.

  Notation anbar:= (fun n: nat => Acc nat_back_auxiliary_relationship n).

  Lemma property_to_anbar: forall n: nat, P n -> anbar n.
  Proof.
    intros x A; apply Acc_intro; intros y B; destruct B; contradiction.
  Defined.

  Lemma anbar_down_to_zero (n: nat): anbar n -> anbar 0.
  Proof.
    induction n. intro; assumption. intro B. apply IHn. apply Acc_intro; intros x Q.
    destruct Q; assumption.
  Defined.

  Lemma anbar_witness (x: nat): anbar x -> {y: nat | P y}.
  Proof.
    apply (Acc_rect (fun _: nat => {y: nat | P y})). intros z A B.
    destruct (dec z) as [Y|N]. exists z; assumption. apply (B (S z)).
    apply nbar_intro; apply N.
  Defined.

  Definition coq_witness_extraction_for_algorithmically_decidable_properties:
    (exists n: nat, P n) -> {m: nat | P m}.
  Proof.
    intro E. apply (anbar_witness 0). destruct E as (x, Q). apply (anbar_down_to_zero x).
    apply property_to_anbar; assumption.
  Defined.  
  
End Extraction_of_witness_with_acc_for_decidable_properties.  

Section Arithmetical_formulas_with_bounded_quantifiers.  

  (** We define the set of formulas of arithmetic with bounded quantifiers. All such
   formulas can be algorithmically decided to be true or false by induction, a property that
   will be useful later. *)
  
  Inductive BQ_Formula:=
  |bqf_eq: nat -> nat -> BQ_Formula
  |bqf_le: nat -> nat -> BQ_Formula
  |bqf_true: BQ_Formula
  |bqf_false: BQ_Formula
  |bqf_not: BQ_Formula -> BQ_Formula
  |bqf_and: BQ_Formula -> BQ_Formula -> BQ_Formula
  |bqf_or: BQ_Formula -> BQ_Formula -> BQ_Formula
  |bqf_implies: BQ_Formula -> BQ_Formula -> BQ_Formula
  |bqf_equiv: BQ_Formula -> BQ_Formula -> BQ_Formula
  |bqf_bounded_ex: nat -> (nat -> BQ_Formula) -> BQ_Formula
  |bqf_bounded_all: nat -> (nat -> BQ_Formula) -> BQ_Formula.

  Fixpoint bqf_natural_translation (u: BQ_Formula) {struct u}: Prop:=
    match u with
    | bqf_eq x y => x = y
    | bqf_le x y => le x y
    | bqf_true => True
    | bqf_false => False
    | bqf_not a => ~ (bqf_natural_translation a)
    | bqf_and a b => (bqf_natural_translation a) /\ (bqf_natural_translation b)
    | bqf_or a b => (bqf_natural_translation a) \/ (bqf_natural_translation b)
    | bqf_implies a b => (bqf_natural_translation a) -> (bqf_natural_translation b)
    | bqf_equiv a b => (bqf_natural_translation a) <-> (bqf_natural_translation b)
    | bqf_bounded_ex m f => exists x: nat, (le x m) /\ (bqf_natural_translation (f x))
    | bqf_bounded_all m f => forall x: nat, (le x m) -> (bqf_natural_translation (f x))
    end.

  Definition nat_eq_dec: forall (x y: nat), sumbool (x = y) (x <> y).
  Proof.
    intro x;  induction x; intro y; destruct y. left; reflexivity. right; discriminate.
    right; discriminate. destruct (IHx y). left; apply eq_S; assumption.
    right; intro F; apply eq_add_S in F; contradiction.
  Defined.

  Definition nat_le_dec: forall (x y: nat), sumbool (le x y) (~ le x y).
  Proof.
    induction x; intro y. left; apply le_0_n. destruct y. right; intro F; inversion F.
    destruct (IHx y) as [Y|N]. left; apply le_n_S; apply Y. right; intro F; apply N;
      apply le_S_n; apply F.
  Defined.

  Definition sumbool_bounded_ex (f: nat -> Prop) (t: forall x: nat, sumbool (f x) (~ f x)):
    forall n: nat, sumbool (exists x: nat, le x n /\ f x) (~ exists x: nat, le x n /\ f x).
  Proof.
    intro n; induction n. destruct (t 0) as [Y|N]. left; exists 0; split. apply le_n.
    apply Y. right; intro F. destruct F as (w, (G1, G2)). inversion G1.
    apply N; rewrite <- H; apply G2. destruct IHn as [L|R]. left; destruct L as (w, (L1, L2)).
    exists w; split. apply le_S; apply L1. apply L2. destruct (t (S n)) as [V|W]. left.
    exists (S n); split. apply le_n. apply V. right; intro F; destruct F as (z, (F1, F2)).
    inversion F1. apply W. rewrite <- H; apply F2. apply R; exists z; split; assumption.
  Defined.

  Definition sumbool_bounded_all (f: nat -> Prop) (t: forall x: nat, sumbool (f x) (~ f x)):
    forall n: nat, sumbool (forall x: nat, le x n -> f x) (~ forall x: nat, le x n -> f x).
  Proof.
    intro n; induction n. destruct (t 0) as [Y|N]. left; intros k P; inversion P; apply Y.
    right; intro F; apply N. apply F; apply le_n.
    destruct IHn as [L|R]. destruct (t (S n)) as [V|W]. left; intros x E; inversion E.
    apply V. apply L; assumption. right; intro F. apply W; apply F; apply le_n.
    right; intro F. apply R; intros x T; apply F; apply le_S; apply T.
  Defined.    

  (** The truth test for bounded quantifier formulas. *)
  
  Definition bqf_sumbool_test (u: BQ_Formula):
    sumbool (bqf_natural_translation u) (~ (bqf_natural_translation u)).
  Proof.
    induction u; simpl; try destruct IHu1 as [Y1|N1].
    apply nat_eq_dec. apply nat_le_dec. left; apply I.
    right; intro; assumption. destruct IHu as [Y|N]. right; intro; contradiction.
    left; assumption. destruct IHu2 as [Y2|N2]. left; split; assumption. right; intro F;
      apply N2; apply F. right; intro F; apply N1; apply F.
    left; left; apply Y1. destruct IHu2 as [Y2|N2]. left; right; apply Y2.
    right; intro F; destruct F; contradiction. destruct IHu2 as [Y2|N2].
    left; intro; apply Y2. right; intro F; apply N2; apply (F Y1). left; intro; contradiction.
    destruct IHu2 as [Y2|N2]. left; split; intro; assumption. right; intro F; apply N2;
      apply F; apply Y1. destruct IHu2 as [Y2|N2]. right; intro F; apply N1; apply F; apply Y2.
    left; split; intro; contradiction. apply sumbool_bounded_ex; assumption.
    apply sumbool_bounded_all; assumption.
  Defined.

  Section Parametric_Semantics.

    Variable O: Prop.

    Definition bqpf_or (a b: Prop):= (a -> O) -> (b -> O) -> O.
    Definition bqpf_and (a b: Prop):= (a -> b -> O) -> O.
    Definition bqpf_equiv (a b: Prop):= bqpf_and (a -> b) (b -> a).
    Definition bqpf_ex (m: nat) (f: nat -> Prop):=
      (forall k: nat, ((bqpf_and (((le k m) -> O) -> O) (f k)) -> O)) -> O.
    Definition bqpf_all (m: nat) (f: nat -> Prop):=
      forall k: nat, (((le k m) -> O) -> O) -> f k.

    Fixpoint bqf_parametric_translation (u: BQ_Formula) {struct u}: Prop:=
      match u with
      | bqf_eq x y => ((x = y) -> O) -> O
      | bqf_le x y => ((le x y) -> O) -> O
      | bqf_true => O -> O
      | bqf_false => O
      | bqf_not a => (bqf_parametric_translation a) -> O
      | bqf_and a b => bqpf_and (bqf_parametric_translation a) (bqf_parametric_translation b)
      | bqf_or a b => bqpf_or (bqf_parametric_translation a) (bqf_parametric_translation b)
      | bqf_implies a b => (bqf_parametric_translation a) -> (bqf_parametric_translation b)
      | bqf_equiv a b =>
          bqpf_equiv (bqf_parametric_translation a) (bqf_parametric_translation b)
      | bqf_bounded_ex m f => bqpf_ex m (fun x: nat => bqf_parametric_translation (f x))
      | bqf_bounded_all m f => bqpf_all m (fun x: nat => bqf_parametric_translation (f x))     
    end.

    Theorem bqpf_ex_equivalence (f g: nat -> Prop) (t: forall (n: nat), sumbool (f n) (~ f n)):
      (forall n: nat, ((f n -> O) -> O) <-> g n) -> forall (m: nat),
          (((exists k: nat, (le k m) /\ f k) -> O) -> O) <-> bqpf_ex m g.
    Proof.
      intros A m; induction m; unfold bqpf_ex; unfold bqpf_and; split; intro B. intro C.
      destruct (t 0) as [T1|T2]. apply (C 0); intro D; apply D. intro E; apply E; apply le_n.
      apply A; intro G; apply G; apply T1. apply B; intro B1; destruct B1 as (w, (B2, B3)).
      inversion B2. rewrite H in B3; contradiction. intro C. apply B. intros k D.
      apply D. intros E F. destruct k. apply (A 0). apply F. intro G. apply C.
      exists 0; split. apply le_n. apply G. apply E. intro K; inversion K.
      unfold bqpf_ex in IHm. unfold bqpf_and in IHm. intro C. apply B. intro D.
      destruct D as (w, (D1, D2)). destruct IHm as (I1,I2). inversion D1. apply I2.
      intro E. apply E with (k:= S m). intro F. apply C with (k:= S m). intro G. apply G.
      intro K; apply K; apply le_n. apply A. intro K; apply K. rewrite <- H; apply D2.
      intro E; apply I1. intro K; apply K. apply E. intros l F. apply (C l).
      intro G; apply F. intro K; apply G. intro L; apply K. intro M; apply L.
      apply le_S; apply M. apply I1. intro E; apply E; exists w; split; assumption.
      intros l E. apply (C l). intro G; apply E. intro K; apply G. intro L; apply K.
      intro M; apply L. apply le_S; apply M. destruct (t (S m)) as [T1|T2].
      intro C; apply C; exists (S m); split. apply le_n. apply T1.
      unfold bqpf_ex in IHm; unfold bqpf_and in IHm; destruct IHm as (I1, I2).
      intro C; apply I2. intro D. apply B. intros l E. apply (D l). intro F.
      destruct (A l) as (A1, A2). apply E. intro G. apply F. intro K. apply G. intro L. 
      destruct (t l) as [U1|U2]. apply C. exists l; split; assumption. apply E.
      intros F1 G1. apply A2. apply G1. intro; contradiction. intro D.
      destruct D as (w, (E,F)). apply C; exists w; split. apply le_S; apply E. apply F.
    Defined.

    Theorem bqpf_all_equivalence
      (f g: nat -> Prop) (t: forall (n: nat), sumbool (f n) (~ f n)):
      (forall n: nat, ((f n -> O) -> O) <-> g n) -> forall (m: nat),
          (((forall k:nat, le k m -> f k) -> O) -> O) <-> bqpf_all m g.
    Proof.
      intros A n; unfold bqpf_all; induction n; split; intro B. intros k C.
      apply A; intro D. apply C; intro E. apply B. intro F. apply D. apply F. apply E. intro C.
      apply (A 0). apply B. intro D; apply D; apply le_n. intro E; apply C. intros l F.
      inversion F; apply E. destruct IHn as (I1, I2).  intros p C. apply A. intro D. apply C.
      intro E. apply B. intro F. apply D. apply F. apply E. intro C. destruct IHn as (I1, I2).
      apply I2. intros q D. apply B; intro E. apply D. intro F. apply E; apply le_S; apply F.
      intro D. apply (A (S n)). apply B. intro E; apply E; apply le_n. intro E; apply C.
      intros q F; inversion F. apply E. apply D; assumption.
    Defined.
    
    Definition bqpf_equivalence: forall x: BQ_Formula,
        (((bqf_natural_translation x) -> O) -> O) <-> (bqf_parametric_translation x).
    Proof.
      induction x; simpl.  apply iff_refl. apply iff_refl. split; intros A B; apply B. apply I.
      split; intro A. apply A; apply False_ind. intro; apply A.
      split; intros A B. apply A; intro C. apply IHx. apply B. intro; contradiction.
      apply A. apply IHx. intro C. destruct (bqf_sumbool_test x) as [Y|N]. apply (C Y).
      apply (B N). simpl; split; intros A B. apply B. apply IHx1; intro C; apply A; intro D;
        apply C; apply D. apply IHx2; intro C; apply A; intro D; apply C; apply D.
      apply A; intros C D. apply IHx1 in C. apply C. intro E. apply IHx2 in D. apply D.
      intro F; apply B; split; assumption. split; intros A B. intro C; apply A; intro D.
      destruct D as [D1|D2]. apply B; apply IHx1; intro E; apply (E D1).
      apply C; apply IHx2; intro E; apply (E D2). destruct (bqf_sumbool_test x1) as [Y1|N1].
      apply B; left; apply Y1. destruct (bqf_sumbool_test x2) as [Y2|N2].
      apply B; right; apply Y2. apply A. intro E; apply IHx1. apply E. intro; contradiction.
      intro E; apply IHx2. apply E. intro; contradiction. split; intros A B.
      apply IHx2; intro C. apply A; intro D. apply IHx1. apply B. intro E; apply (C (D E)).
      apply IHx2. apply A. apply IHx1. intro C. destruct (bqf_sumbool_test x1) as [Y1|N1].
      apply (C Y1). apply B; intro; contradiction. intro; apply B; intro; assumption.
      split; intros A B. apply A; intro C. apply B; intro D. apply IHx2; intro E. 
      apply iff_sym in C. apply imp_iff_compat_r with (A:= O) in C. apply IHx1.
      apply D. apply C; apply E. apply IHx1; intro E. apply imp_iff_compat_r with (A:= O) in C.
      apply IHx2 in D. apply D. apply C. apply E. apply A; intros C D.
      destruct (bqf_sumbool_test x1) as [Y1|N1]. destruct (bqf_sumbool_test x2) as [Y2|N2].
      apply B; split; intro; assumption. apply IHx2. apply C. apply IHx1. intro E; apply E; 
        assumption. intro; contradiction. destruct (bqf_sumbool_test x2) as [Y2|N2].
      apply IHx1. apply D. apply IHx2. intro E; apply E; assumption. intro; contradiction.
      apply B; split; intro; contradiction.
      simpl; apply bqpf_ex_equivalence. intros; apply bqf_sumbool_test. assumption.
      simpl; apply bqpf_all_equivalence. intros; apply bqf_sumbool_test. assumption.
    Defined.  

    Definition parametric_existential_quantifier (T: Type) (f: T -> Prop): Prop:=
      (forall x: T, (f x -> O)) -> O.
    
  End Parametric_Semantics.

  Theorem Harvey_Friedman_sigma1_conservativity_property:
    forall (f: nat -> BQ_Formula),
      (forall O: Prop, parametric_existential_quantifier
                         O nat (fun n: nat => bqf_parametric_translation O (f n))) ->
      exists (n: nat), bqf_natural_translation (f n).
  Proof.
    intros f A. apply (A (exists n: nat, bqf_natural_translation (f n))).
    intros m B. apply bqpf_equivalence in B. apply B. intro C; exists m; apply C.
  Defined.

  Theorem Harvey_Friedman_pi2_conservativity_property:
    forall (g: nat -> nat -> BQ_Formula),
      (forall O: Prop, forall m: nat, parametric_existential_quantifier
                         O nat (fun n: nat => bqf_parametric_translation O (g m n))) ->
      forall m: nat, exists (n: nat), bqf_natural_translation (g m n).
  Proof.
    intros g A m; apply Harvey_Friedman_sigma1_conservativity_property. intro O; apply A.
  Defined.

  Definition Harvey_Friedman_sigma1_extraction:
    forall (f: nat -> BQ_Formula),
      (forall O: Prop, parametric_existential_quantifier
                         O nat (fun n: nat => bqf_parametric_translation O (f n))) ->
      {m: nat | bqf_natural_translation (f m)}.
  Proof.
    intros f A; apply coq_witness_extraction_for_algorithmically_decidable_properties.
    intro; apply bqf_sumbool_test. apply Harvey_Friedman_sigma1_conservativity_property.
    apply A.
  Defined.

  Definition Harvey_Friedman_pi2_extraction:
    forall (g: nat -> nat -> BQ_Formula),
      (forall O: Prop, forall m: nat, parametric_existential_quantifier
                         O nat (fun n: nat => bqf_parametric_translation O (g m n))) ->
      {prog: nat -> nat |forall m: nat,  bqf_natural_translation (g m (prog m))}.
  Proof.
    intros g A. assert (forall n: nat, {k: nat | bqf_natural_translation (g n k)}) as F.
    intro n; apply Harvey_Friedman_sigma1_extraction. intros O; apply A.
    exists (fun n: nat => proj1_sig (F n)). intro m; apply (proj2_sig (F m)).
  Defined.  
  
End Arithmetical_formulas_with_bounded_quantifiers.

Section Formal_second_order_arithmetic.

  (** Second order arithmetic is a mathematical theory which has integers and sets of integers
      as primary notions, the usual induction theorem which applies to every set of integers,
     and the full comprehension scheme for forming sets of integers from any formal property
     about them. If you want to have a glimpse of what it is possible to express in such
     a system, you can view an ordered pair (a,b) as the result of the operation
     a+ (a+b)^2; indeed a simple arithmetic theorem establishes that for every integers a,b,
     x and y, if x+(x+y)^2 = a+(a+b)^2 (said otherwise, (x,y) = (a,b)) then x = a and y = b
     (S. Simpson): hence the "coordinates" of the ordered pair are well defined.
     A real number is a special set of numbers (think of a set of ordered pairs (p,q) where
     q is the p-th digit of the real number); a triple is an integer of the form (a, (b, c))
     with a,b, c integers, a sequence of real numbers s is a set of triples such that for every
     n, the set of x such that (n, x) is in s is a real number (the value of the sequence
     at n); a doubly indexed sequence is a set d of numbers of the form ((x,y), (a,b))
     belonging to a sequence s, the value of d at x,y being the value of s at (x,y)
     a countable metric space is a set A of numbers and a doubly indexed sequence D
     defined on A satisfying the usual axioms of metric spaces including triangle inequality, 
     polish spaces are sets of Cauchy sequences of countable metric spaces up to equivalence
     (there is even a way to define in every such class a canonical representant and thus
     define the completion; this is an interesting exercise to the reader I think) and so on. 
   *)
  
Variable SOA_Set: Type.

Inductive SOA_Formula: Type:=
|soaf_not_eq: nat -> nat -> SOA_Formula
|soaf_not_le: nat -> nat -> SOA_Formula
|soaf_not_belongs: nat -> SOA_Set -> SOA_Formula
|soaf_false: SOA_Formula
|soaf_implies: SOA_Formula -> SOA_Formula -> SOA_Formula
|soaf_nat_all: (nat -> SOA_Formula) -> SOA_Formula
|soaf_set_all: (SOA_Set -> SOA_Formula) -> SOA_Formula.

(** In the future yours truly might attempt to include a class formation term in the
 language: "{x in N | P(x)}" and a minimization operator min(X):=
 0 is X is empty and the smallest element of X othewise; unless I'm mistaken it is
 feasible although not straightforward. The language above is utterly unexpressive and
 expressing meaningful results, not to mention proving them, is quite long and difficult.*)

Definition soaf_true: SOA_Formula:= soaf_implies soaf_false soaf_false.

Definition soaf_not (a: SOA_Formula): SOA_Formula:= soaf_implies a soaf_false.

Definition soaf_nat_ex (f: nat -> SOA_Formula): SOA_Formula:=
  soaf_implies (soaf_nat_all (fun n: nat => soaf_implies (f n) soaf_false)) soaf_false.

Definition soaf_set_ex (f: SOA_Set -> SOA_Formula): SOA_Formula :=
  soaf_implies (soaf_set_all (fun s: SOA_Set => soaf_implies (f s) soaf_false)) soaf_false.

Definition soaf_and (a b: SOA_Formula): SOA_Formula :=
  soaf_implies (soaf_implies a (soaf_implies b soaf_false)) soaf_false.

Definition soaf_equiv (c d: SOA_Formula): SOA_Formula:=
  soaf_and (soaf_implies c d) (soaf_implies d c).

Definition soaf_or (a b: SOA_Formula): SOA_Formula:=
  soaf_implies (soaf_implies a soaf_false)
    (soaf_implies (soaf_implies b soaf_false) soaf_false). 

Definition soaf_eq (x y: nat):= soaf_implies (soaf_not_eq x y) soaf_false.
Definition soaf_le (x y: nat):= soaf_implies (soaf_not_le x y) soaf_false.

Definition soaf_bounded_ex (n: nat) (f: nat -> SOA_Formula): SOA_Formula:=
  soaf_nat_ex (fun k: nat => soaf_and (soaf_le k n) (f k)).

Definition soaf_bounded_all (n: nat) (f: nat -> SOA_Formula): SOA_Formula:=
  soaf_nat_all (fun k: nat => soaf_implies (soaf_le k n) (f k)).

Definition soaf_belongs (x: nat) (m: SOA_Set):= soaf_implies (soaf_not_belongs x m) soaf_false.

Definition soa_comprehension_instance (f: nat -> SOA_Formula): SOA_Formula:=
  soaf_set_ex
    (fun m: SOA_Set => soaf_nat_all (fun x: nat => soaf_equiv (f x) (soaf_belongs x m))).

Definition soa_standard_integer (x: nat): SOA_Formula:=
  soaf_set_all
    (fun m: SOA_Set =>
       soaf_implies
         (soaf_belongs 0 m)
         (soaf_implies
            (soaf_nat_all (fun y: nat => soaf_implies
                                           (soaf_belongs y m)
                                           (soaf_belongs (S y) m)))
            (soaf_belongs x m)
         )
    ).

Definition soa_recurrence_axiom: SOA_Formula:=
  soaf_nat_all soa_standard_integer.

Definition soa_sum_0_axiom: SOA_Formula:=
  soaf_nat_all (fun x: nat => soaf_eq (0 + x) x).
Definition soa_sum_succ_axiom: SOA_Formula:=
  soaf_nat_all (fun x: nat => soaf_nat_all (fun y: nat => soaf_eq ((S y) + x) (S (y + x)))).
Definition soa_mul_0_axiom: SOA_Formula:=
  soaf_nat_all (fun x: nat => soaf_eq (0 * x) 0).
Definition soa_mul_succ_axiom: SOA_Formula:=
  soaf_nat_all (fun x: nat => soaf_nat_all (fun y: nat => soaf_eq ((S y) * x)
                                                            (x + (y * x)))).
Definition soa_le_axiom: SOA_Formula:=
  soaf_nat_all
    (fun x: nat =>
       soaf_nat_all
         (fun y: nat =>
            soaf_equiv (soaf_le x y) (soaf_nat_ex (fun z: nat => soaf_eq (z + x) y))
         )
    ).

Definition soa_eq_reflexivity: SOA_Formula:=
  soaf_nat_all (fun x: nat => soaf_eq x x).
             
Definition soa_eq_Leibniz_rule: SOA_Formula:=
  soaf_nat_all
    (fun x: nat =>
       soaf_nat_all
         (fun y: nat =>
            soaf_implies
              (soaf_eq x y)
              (soaf_set_all (fun m: SOA_Set =>
                               soaf_implies (soaf_belongs x m) (soaf_belongs y m)))
         )
    ).

Notation P:= SOA_Formula.
Notation "a -o b":= (soaf_implies a b) (right associativity, at level 41).

Inductive soa_theorem: P -> Type:=
|soat_tautology_b: forall a b c: P, soa_theorem ((b -o c) -o (a -o b) -o (a -o c))
|soat_tautology_c: forall a b c: P, soa_theorem ((a -o b -o c) -o b -o a -o c)
|soat_tautology_i: forall a: P, soa_theorem (a -o a)
|soat_tautology_k: forall a b: P, soa_theorem (a -o (b -o a))
|soat_tautology_w: forall a b: P, soa_theorem ((a -o a -o b) -o a -o b)
|soat_tautology_explosion: forall a: P, soa_theorem (soaf_false -o a)
|soat_tautology_Peirce: forall a b: P, soa_theorem (((a -o b) -o a) -o a)
|soat_nat_special_case: forall (f: nat -> P) (x: nat), soa_theorem ((soaf_nat_all f) -o (f x))
|soat_set_special_case: forall (f: SOA_Set -> P) (x: SOA_Set),
    soa_theorem ((soaf_set_all f) -o (f x))
|soat_comprehension_instance: forall (f: nat -> P),
    soa_theorem (soa_comprehension_instance f)
|soat_recurrence_axiom: soa_theorem soa_recurrence_axiom
|soat_sum_0_axiom: soa_theorem soa_sum_0_axiom
|soat_sum_succ_axiom: soa_theorem soa_sum_succ_axiom
|soat_mul_0_axiom: soa_theorem soa_mul_0_axiom
|soat_mul_succ_axiom: soa_theorem soa_mul_succ_axiom
|soat_le_axiom: soa_theorem soa_le_axiom
|soat_eq_reflexivity: soa_theorem soa_eq_reflexivity                            
|soat_eq_Leibniz_rule: soa_theorem soa_eq_Leibniz_rule
|soat_modus_ponens: forall a b: P, soa_theorem (a -o b) -> soa_theorem a -> soa_theorem b
|soat_nat_generalization: forall (a: P) (f: nat -> P),
    (forall x: nat, soa_theorem (a -o (f x))) -> soa_theorem (a -o soaf_nat_all f)
|soat_set_generalization:  forall (a: P) (f: SOA_Set -> P),
    (forall x: SOA_Set, soa_theorem (a -o (f x))) -> soa_theorem (a -o soaf_set_all f).   

Fixpoint bqf_to_soa_translation (u: BQ_Formula) {struct u}: SOA_Formula:=
  match u with
  | bqf_eq m n => soaf_eq m n
  | bqf_le m n => soaf_le m n
  | bqf_true => soaf_true
  | bqf_false => soaf_false
  | bqf_not a => soaf_not (bqf_to_soa_translation a)
  | bqf_and a b => soaf_and (bqf_to_soa_translation a) (bqf_to_soa_translation b)
  | bqf_or a b => soaf_or (bqf_to_soa_translation a) (bqf_to_soa_translation b)
  | bqf_implies a b => soaf_implies (bqf_to_soa_translation a) (bqf_to_soa_translation b)
  | bqf_equiv a b => soaf_equiv (bqf_to_soa_translation a) (bqf_to_soa_translation b)
  | bqf_bounded_ex n f => soaf_bounded_ex n (fun k: nat => bqf_to_soa_translation (f k))
  | bqf_bounded_all n f => soaf_bounded_all n (fun k: nat => bqf_to_soa_translation (f k))
  end.

End Formal_second_order_arithmetic.

Section Standard_Semantics.

  Variable O: Prop.
  
  Notation P:= (SOA_Formula (nat -> Prop)).
  
  Fixpoint soaf_value (u: P) {struct u}: Prop:=
    match u with
    | soaf_not_eq _ x y => (x = y) -> O
    | soaf_not_le _ x y => (le x y) -> O
    | soaf_not_belongs _ x m => (m x) -> O
    | soaf_false _ => O
    | soaf_implies _ a b => (soaf_value a) -> (soaf_value b)
    | soaf_nat_all _ f => forall n: nat, soaf_value (f n)
    | soaf_set_all _ g => forall (m: nat -> Prop), soaf_value (g m)
    end.

  Theorem imp_iff (A A' B B': Prop): (A <-> A') -> (B <-> B') -> ((A -> B) <-> (A' -> B')).
  Proof.
    intros P Q; split; intros  U V; apply Q; apply U; apply P; apply V.
  Defined.

  Theorem all_iff (T: Type) (f g: T -> Prop):
    (forall x: T, (f x <-> g x)) -> (all f <-> all g).
  Proof.
    intro A; split; intros B t; apply A; apply B.
  Defined.
    
  Theorem soaf_value_bq_formula:
    forall u: BQ_Formula,
      soaf_value (bqf_to_soa_translation (nat -> Prop) u) <-> bqf_parametric_translation O u.
  Proof.
    intro u; induction u; simpl; repeat apply imp_iff; try apply iff_refl; try assumption.
    apply all_iff; intro; repeat apply imp_iff; try apply iff_refl; try apply H.
    apply all_iff; intro; repeat apply imp_iff; try apply iff_refl; try apply H.
  Defined.
  
  Let regular:= (fun (p: Prop) => (((p -> O) -> O) -> p): Prop).

  Theorem regular_false: regular O.
  Proof.
    intro F; apply F; intro G; apply G.
  Defined.

  Theorem regular_implies (a b: Prop): regular b -> regular (a -> b).
  Proof.
    intros A B F. apply A; intro C. apply B; intro D. apply (C (D F)).
  Defined.

  Theorem regular_forall (T: Type) (f: T -> Prop):
    (forall t: T, regular (f t)) -> regular (all f).
  Proof.
    intros A F x. apply A; intro B. apply F; intro C. apply B; apply C.
  Defined.

  Definition regular_not (p: Prop): regular (p -> O):=
    (regular_implies p O regular_false).

  Definition regular_soaf_value (a: P): regular (soaf_value a).
  Proof.
    induction a. apply regular_not. apply regular_not. apply regular_not.
    apply regular_false. apply regular_implies; assumption.
    simpl; apply regular_forall; assumption. simpl; apply regular_forall; assumption.
  Defined.    
    
  Theorem regular_peirce (a b: Prop): regular a -> regular b ->
                                      ((a -> b) -> a) -> a.
  Proof.
    intros A B C. apply A; intro D. apply D. apply C. intro E. apply B. intro F.
    apply (D E).
  Defined.

  Theorem regular_explosion (a: Prop): (regular a) -> O -> a.
  Proof.
    intros A B. apply A. intro C. apply B.
  Defined.

  Theorem regular_and (a b: Prop):
    regular a -> regular b -> ((a /\ b) <->  ((a -> b -> O) -> O)).
  Proof.
    intros A B; split. intros C D. destruct C; apply D; assumption.
    intro D; split. apply A; intro E. apply D; intros; apply E; assumption.
    apply B; intro E. apply D; intros; apply E; assumption.
  Defined.

  Theorem regular_equiv (a b: Prop):
    regular a -> regular b -> ((a <-> b) <->  (((a -> b) -> (b -> a) -> O) -> O)).
  Proof.
    intros A B; apply regular_and; apply regular_implies; assumption.
  Defined.

  Theorem regular_ex_intro (T: Type) (f: T -> Prop) (t: T):
    f t -> ((forall x: T, (f x -> O)) -> O).
  Proof.
    intros A B. apply (B t A).
  Defined.
  
  Theorem soaf_comprehension_value:
    forall (f: nat -> P),
    soaf_value (soa_comprehension_instance (nat -> Prop) f).
  Proof.
    intro f. simpl. apply regular_ex_intro with (t:= fun (n: nat) => soaf_value (f n)).
    intro n. intro A. apply A. intros B C; apply (C B). apply regular_soaf_value.
  Defined.

  Theorem soaf_recurrence_value: soaf_value (soa_recurrence_axiom (nat -> Prop)).
  Proof.
    simpl; intros n M A B. induction n. apply A. apply B. apply IHn.
  Defined.

  Lemma le_add: forall (x y: nat), (x <= y) <-> (exists z: nat, z + x = y).
  Proof.
    assert (forall x y: nat, x <= y -> exists z: nat, z + x = y) as L1.
    intros x y i; induction i. exists 0; simpl. reflexivity. destruct IHi as (j, A).
    exists (S j); simpl; apply eq_S; apply A.
    assert (forall x y: nat, le y (x + y)) as L2. induction x. intros; simpl; apply le_n.
    intros; simpl; apply le_S; apply IHx. intros x y; split. apply L1.
    intro A; destruct A as (t, B). rewrite <- B. apply L2.
  Defined.
    
  Theorem soa_theorem_soundness (u: P) (pr: soa_theorem (nat -> Prop) u):
    soaf_value u.
  Proof.
    induction pr; simpl. intros A B C; apply (A (B C)). intros A B C; apply (A C B).
    intro A; apply A. intros A B; apply A. intros A B; apply (A B B).
    apply regular_explosion; apply regular_soaf_value.
    apply regular_peirce; apply regular_soaf_value. intro A; apply A. intro A; apply A.
    apply soaf_comprehension_value. apply soaf_recurrence_value.
    intros n A; apply A; reflexivity. intros p q A; apply A; reflexivity.
    intros n A; apply A; reflexivity. intros p q A; apply A; reflexivity.
    intros p q A. destruct (le_add p q) as (L,R). apply A. intros B C. apply B; intro D.
    destruct (L D) as (r, E). apply (C r). intro F; apply (F E). intros B C. apply B.
    intros r D; apply D; intro E. apply C. apply R; exists r; apply E.
    intros n E; apply E; reflexivity. intros p q A f B C; apply A; intro D. apply B.
    rewrite D; apply C. simpl in IHpr1; apply IHpr1; apply IHpr2.
    simpl in H; intros A n; apply H; apply A. simpl in H; intros A n; apply H; apply A.
  Defined.    
  
End Standard_Semantics.

Section Extraction_and_conservativity.

  Theorem SOA_sigma1_conservativity: forall (f: nat -> BQ_Formula),
      (soa_theorem (nat -> Prop)
         (soaf_nat_ex (nat-> Prop)
            (fun n: nat => bqf_to_soa_translation (nat -> Prop) (f n)))) ->
      exists n: nat, bqf_natural_translation (f n).
  Proof.
    intros f A. apply Harvey_Friedman_sigma1_conservativity_property. intro O.
    apply soa_theorem_soundness with (O:= O) in A.
    simpl in A. unfold parametric_existential_quantifier. intro B. apply A.
    intros n C. apply (B n). apply soaf_value_bq_formula. apply C.
  Defined.

  Theorem SOA_sigma1_extraction: forall (f: nat -> BQ_Formula),
      (soa_theorem (nat -> Prop)
         (soaf_nat_ex (nat-> Prop)
            (fun n: nat => bqf_to_soa_translation (nat -> Prop) (f n)))) ->
      {n: nat| bqf_natural_translation (f n)}.
  Proof.
    intros f A. apply Harvey_Friedman_sigma1_extraction. intro O.
    apply soa_theorem_soundness with (O:= O) in A.
    simpl in A. unfold parametric_existential_quantifier. intro B. apply A.
    intros n C. apply (B n). apply soaf_value_bq_formula. apply C.
  Defined.

  Theorem SOA_pi2_conservativity: forall (g: nat -> nat -> BQ_Formula),
      (soa_theorem (nat -> Prop)
         (soaf_nat_all (nat -> Prop)
            (fun m: nat =>
               (soaf_nat_ex (nat-> Prop)
                  (fun n: nat => bqf_to_soa_translation (nat -> Prop) (g m n)))))) ->
      forall m: nat, exists n: nat, bqf_natural_translation (g m n).
  Proof.
    intros g A. apply Harvey_Friedman_pi2_conservativity_property. intros O m.
    apply soa_theorem_soundness with (O:= O) in A.
    simpl in A. unfold parametric_existential_quantifier. intro B. apply (A m).
    intros n C. apply (B n). apply soaf_value_bq_formula. apply C.
  Defined.
  
  Theorem SOA_pi2_extraction: forall (g: nat -> nat -> BQ_Formula),
      (soa_theorem (nat -> Prop)
         (soaf_nat_all (nat -> Prop)
            (fun m: nat =>
               (soaf_nat_ex (nat-> Prop)
                  (fun n: nat => bqf_to_soa_translation (nat -> Prop) (g m n)))))) ->
      {prog: nat -> nat| forall m: nat, bqf_natural_translation (g m (prog m))}.
  Proof.
    intros g A. apply Harvey_Friedman_pi2_extraction. intros O m.
    apply soa_theorem_soundness with (O:= O) in A.
    simpl in A. unfold parametric_existential_quantifier. intro B. apply (A m).
    intros n C. apply (B n). apply soaf_value_bq_formula. apply C.
  Defined.
  
End Extraction_and_conservativity.
