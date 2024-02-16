(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import ZArith Uint63 SpecFloat PrimFloat FloatOps FloatAxioms.
Require Import Psatz.

(** * Support results involving frexp and ldexp *)

Lemma shift_value : shift = (2*emax + prec)%Z.
Proof. reflexivity. Qed.

Theorem Z_frexp_spec : forall f, let (m,e) := Z.frexp f in (Prim2SF m, e) = SFfrexp prec emax (Prim2SF f).
Proof.
  intro.
  unfold Z.frexp.
  case_eq (frshiftexp f).
  intros.
  assert (H' := frshiftexp_spec f).
  now rewrite H in H'.
Qed.

(*
Theorem Z_ldexp_spec : forall f e, Prim2SF (Z.ldexp f e) = SFldexp prec emax (Prim2SF f) e.
Proof.
Admitted.
*)
