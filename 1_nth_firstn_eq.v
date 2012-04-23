Require Import List Arith.

Variable A : Type.
Variable d : A.

Lemma nth_firstn_eq :
  forall (l:list A) (j i:nat),
    1+i <= j -> nth i (firstn j l) d = nth i l d.
Proof with simpl;trivial.
  induction l.
    induction j.
      induction i....
      induction i....
    induction j.
      induction i.
        simpl. intro H. contradict H. auto with arith.
        intro H. exfalso. contradict H. auto with arith.
      induction i....
        intro H. apply le_S_n in H. revert H. auto.
Qed.
