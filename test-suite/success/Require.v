(* -*- coq-prog-args: ("-noinit"); -*- *)

Require Import Coq.Init.Logic.
Locate Library Coq.Init.Logic.

(* Check that Init.Datatypes didn't get exported by the import above *)
Fail Check nat.
