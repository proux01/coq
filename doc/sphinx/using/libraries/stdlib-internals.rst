Stdlib internals
================

These commands and tactics are now provided in the Stdlib
hence documented in its refman.

.. comment to editors:
   when needing to change anything here, be sure to reflect the change
   in the stdlib refman

.. cmd:: Extraction @qualid
         Recursive Extraction {+ @qualid }
         Extraction @string {+ @qualid }
   :undocumented:

.. cmd:: Extraction Library @ident
   :undocumented:

.. cmd:: Recursive Extraction Library @ident
   :undocumented:

.. cmd:: Separate Extraction {+ @qualid }
   :undocumented:

.. cmd:: Extraction TestCompile {+ @qualid }
   :undocumented:

.. cmd:: Show Extraction
   :undocumented:

.. cmd:: Pwd
   :undocumented:

.. cmd:: Cd {? @string }
   :undocumented:

.. cmd:: Extraction Language @language

   .. insertprodn language language

   .. prodn::
      language ::= OCaml
      | Haskell
      | Scheme
      | JSON

.. flag:: Extraction Conservative Types
   :undocumented:

.. cmd:: Extraction Inline {+ @qualid }
   :undocumented:

.. cmd:: Extraction NoInline {+ @qualid }
   :undocumented:

.. cmd:: Print Extraction Inline
   :undocumented:

.. cmd:: Reset Extraction Inline
   :undocumented:

.. cmd:: Extraction Implicit @qualid [ {* {| @ident | @integer } } ]
   :undocumented:

.. cmd:: Extract Constant @qualid {* @string__tv } => {| @ident | @string }
   :undocumented:

.. cmd:: Extract Inlined Constant @qualid => {| @ident | @string }
   :undocumented:

.. cmd:: Extract Inductive @qualid => {| @ident | @string } [ {* {| @ident | @string } } ] {? @string__match }
   :undocumented:

.. cmd:: Extract Foreign Constant @qualid => @string
   :undocumented:

.. cmd:: Extract Callback {? @string } @qualid
   :undocumented:

.. cmd:: Print Extraction Foreign
   :undocumented:

.. cmd:: Print Extraction Callback
   :undocumented:

.. cmd:: Reset Extraction Callback
   :undocumented:

.. cmd:: Extraction Blacklist {+ @ident }
   :undocumented:

.. cmd:: Print Extraction Blacklist
   :undocumented:

.. cmd:: Reset Extraction Blacklist
   :undocumented:

.. cmd:: Derive @open_binders in @type as @ident
         Derive @open_binders SuchThat @type As @ident
   :undocumented:

.. cmd:: Function @fix_definition {* with @fix_definition }
   :undocumented:

.. tacn:: functional induction @term {? using @one_term_with_bindings } {? as @simple_intropattern }
   :undocumented:

.. tacn:: soft functional induction {+ @one_term } {? using @one_term_with_bindings } {? as @simple_intropattern }
   :undocumented:

.. tacn:: functional inversion {| @ident | @natural } {? @qualid }
   :undocumented:

.. cmd:: Functional Scheme @func_scheme_def {* with @func_scheme_def }

   .. insertprodn func_scheme_def func_scheme_def

   .. prodn::
      func_scheme_def ::= @ident := Induction for @qualid Sort @sort_family

.. cmd:: Functional Case @func_scheme_def
         Generate graph for @qualid
   :undocumented:

.. cmd:: Print Rings
   :undocumented:

.. tacn:: ring_lookup @ltac_expr0 [ {* @one_term } ] {+ @one_term }
          protect_fv @string {? in @ident }
   :undocumented:

.. cmd:: Add Ring @ident : @one_term {? ( {+, @ring_mod } ) }

   .. insertprodn ring_mod ring_mod

   .. prodn::
      ring_mod ::= decidable @one_term
      | abstract
      | morphism @one_term
      | constants [ @ltac_expr ]
      | preprocess [ @ltac_expr ]
      | postprocess [ @ltac_expr ]
      | setoid @one_term @one_term
      | sign @one_term
      | power @one_term [ {+ @qualid } ]
      | power_tac @one_term [ @ltac_expr ]
      | div @one_term
      | closed [ {+ @qualid } ]

.. tacn:: field_lookup @ltac_expr [ {* @one_term } ] {+ @one_term }
   :undocumented:

.. cmd:: Add Field @ident : @one_term {? ( {+, @field_mod } ) }

   .. insertprodn field_mod field_mod

   .. prodn::
      field_mod ::= @ring_mod
      | completeness @one_term

.. cmd:: Print Fields
   :undocumented:

.. tacn:: nsatz_compute @one_term
   :undocumented:

.. cmd:: Show Lia Profile
   :undocumented:

.. tacn:: xlra_Q @ltac_expr
          xlra_R @ltac_expr
   :undocumented:

.. tacn:: wlra_Q @ident @one_term
   :undocumented:

.. tacn:: xlia @ltac_expr
   :undocumented:

.. tacn:: wlia @ident @one_term
   :undocumented:

.. tacn:: xnra_Q @ltac_expr
          xnra_R @ltac_expr
   :undocumented:

.. tacn:: wnra_Q @ident @one_term
   :undocumented:

.. tacn:: xnia @ltac_expr
   :undocumented:

.. tacn:: wnia @ident @one_term
   :undocumented:

.. tacn:: xsos_Q @ltac_expr
          xsos_R @ltac_expr
          xsos_Z @ltac_expr
          xpsatz_Q @nat_or_var @ltac_expr
          xpsatz_R @nat_or_var @ltac_expr
          xpsatz_Z @nat_or_var @ltac_expr
   :undocumented:

.. tacn:: wsos_Q @ident @one_term
          wsos_Z @ident @one_term
          wpsatz_Q @nat_or_var @ident @one_term
          wpsatz_Z @nat_or_var @ident @one_term
   :undocumented:

.. cmd:: Add Zify @add_zify @qualid

   .. insertprodn add_zify add_zify

   .. prodn::
      add_zify ::= {| InjTyp | BinOp | UnOp | CstOp | BinRel | UnOpSpec | BinOpSpec }
      | {| PropOp | PropBinOp | PropUOp | Saturate }

.. cmd:: Show Zify @show_zify

   .. insertprodn show_zify show_zify

   .. prodn::
      show_zify ::= {| InjTyp | BinOp | UnOp | CstOp | BinRel | UnOpSpec | BinOpSpec | Spec }

.. tacn:: zify_elim_let
          zify_iter_let @ltac_expr
          zify_iter_specs
          zify_op
          zify_saturate
   :undocumented:
