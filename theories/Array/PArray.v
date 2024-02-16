From Coq Require Import Uint63.
From Coq Require Export PrimArray ArrayAxioms.

Local Open Scope uint63_scope.
Local Open Scope array_scope.

(* Lemmas *)

Lemma default_copy A (t:array A) : default (copy t) = default t.
Proof.
  assert (irr_lt : length t <? length t = false). {
    destruct (Uint63.ltbP (length t) (length t)); try reflexivity.
    exfalso; eapply BinInt.Z.lt_irrefl; eassumption.
  }
  assert (get_copy := get_copy A t (length t)).
  rewrite !get_out_of_bounds in get_copy; try assumption.
  rewrite length_copy; assumption.
Qed.

Lemma default_make A (a : A) size : default (make size a) = a.
Proof.
  assert (irr_lt : length (make size a) <? length (make size a) = false). {
    destruct (Uint63.ltbP (length (make size a)) (length (make size a))); try reflexivity.
    exfalso; eapply BinInt.Z.lt_irrefl; eassumption.
  }
  assert (get_make := get_make A a size (length (make size a))).
  rewrite !get_out_of_bounds in get_make; assumption.
Qed.

Lemma get_set_same_default A (t : array A) (i : int) :
  t.[i <- default t].[i] = default t.
Proof.
 case_eq (i <? length t); intros.
 - rewrite get_set_same; trivial.
 - rewrite get_out_of_bounds, default_set; trivial.
   rewrite length_set; trivial.
Qed.

Lemma get_not_default_lt A (t:array A) x :
 t.[x] <> default t -> (x <? length t) = true.
Proof.
 intros Hd.
 case_eq (x <? length t); intros Heq; [trivial | ].
 elim Hd; rewrite get_out_of_bounds; trivial.
Qed.
