(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util

(** {1 Helper functions} *)

let getenv_else s dft = try Sys.getenv s with Not_found -> dft ()

let safe_getenv warning n =
  getenv_else n (fun () ->
    warning ("Environment variable "^n^" not found: using '$"^n^"' .");
    ("$"^n)
  )

let ( / ) a b =
  if Filename.is_relative b then a ^ "/" ^ b else b

let coqify d = d / "coq"

let home ~warn =
  getenv_else "HOME" (fun () ->
    try (Sys.getenv "HOMEDRIVE")^(Sys.getenv "HOMEPATH") with Not_found ->
      getenv_else "USERPROFILE" (fun () ->
        warn ("Cannot determine user home directory, using '.' .");
        Filename.current_dir_name))

let path_to_list p =
  let sep = if String.equal Sys.os_type "Win32" then ';' else ':' in
    String.split_on_char sep p

let expand_path_macros ~warn s =
  let rec expand_atom s i =
    let l = String.length s in
    if i<l && (Util.is_digit s.[i] || Util.is_letter s.[i] || s.[i] == '_')
    then expand_atom s (i+1)
    else i in
  let rec expand_macros s i =
    let l = String.length s in
    if Int.equal i l then s else
      match s.[i] with
        | '$' ->
          let n = expand_atom s (i+1) in
          let v = safe_getenv warn (String.sub s (i+1) (n-i-1)) in
          let s = (String.sub s 0 i)^v^(String.sub s n (l-n)) in
          expand_macros s (i + String.length v)
        | '~' when Int.equal i 0 ->
          let n = expand_atom s (i+1) in
          let v =
            if Int.equal n (i + 1) then home ~warn
            else (Unix.getpwnam (String.sub s (i+1) (n-i-1))).Unix.pw_dir
          in
          let s = v^(String.sub s n (l-n)) in
          expand_macros s (String.length v)
        | c -> expand_macros s (i+1)
  in expand_macros s 0

(** {1 Paths} *)

(** {2 Coq paths} *)

let coqbin =
  CUnix.canonical_path_name (Filename.dirname Sys.executable_name)

(** The following only makes sense when executables are running from
    source tree (e.g. during build or in local mode). *)
let coqroot =
  Filename.dirname coqbin

(** On win32, we add coqbin to the PATH at launch-time (this used to be
    done in a .bat script). *)
let _ =
  if Coq_config.arch_is_win32 then
    Unix.putenv "PATH" (coqbin ^ ";" ^ getenv_else "PATH" (fun () -> ""))

(** Add a local installation suffix (unless the suffix is itself
    absolute in which case the prefix does not matter) *)
let use_suffix prefix suffix =
  if String.length suffix > 0 && suffix.[0] = '/' then suffix else prefix / suffix

(** [check_file_else ~dir ~file oth] checks if [file] exists in
    the installation directory [dir] given relatively to [coqroot],
    which maybe has been relocated.
    If the check fails, then [oth ()] is evaluated.
    Using file system equality seems well enough for this heuristic *)
let check_file_else ~dir ~file oth =
  let path = use_suffix coqroot dir in
  if Sys.file_exists (path / file) then path else oth ()

let guess_coqlib fail =
  getenv_else "COQLIB" (fun () ->
  let prelude = "theories/Init/Prelude.vo" in
  check_file_else ~dir:Coq_config.coqlibsuffix ~file:prelude
    (fun () ->
      if not Coq_config.local && Sys.file_exists (Coq_config.coqlib / prelude)
      then Coq_config.coqlib
      else
        fail "cannot guess a path for Coq libraries; please use -coqlib option")
  )

let coqlib : string option ref = ref None
let set_user_coqlib path = coqlib := Some path

(** coqlib is now computed once during coqtop initialization *)

let set_coqlib ~fail =
  match !coqlib with
  | Some _ -> ()
  | None ->
    let lib = guess_coqlib fail in
    coqlib := Some lib

let coqlib () = Option.default "" !coqlib

let docdir () =
  (* This assumes implicitly that the suffix is non-trivial *)
  let path = use_suffix coqroot Coq_config.docdirsuffix in
  if Sys.file_exists path then path else Coq_config.docdir

let datadir () =
  (* This assumes implicitly that the suffix is non-trivial *)
  let path = use_suffix coqroot Coq_config.datadirsuffix in
  if Sys.file_exists path then path else Coq_config.datadir

let configdir () =
  (* This assumes implicitly that the suffix is non-trivial *)
  let path = use_suffix coqroot Coq_config.configdirsuffix in
  if Sys.file_exists path then path else Coq_config.configdir

let coqpath =
  let coqpath = getenv_else "COQPATH" (fun () -> "") in
  let make_search_path path =
    let paths = path_to_list path in
    let valid_paths = List.filter Sys.file_exists paths in
    List.rev valid_paths
  in
  make_search_path coqpath

(** {2 Caml paths} *)

let ocamlfind () = Coq_config.ocamlfind

(** {1 XDG utilities} *)

let xdg_data_home warn =
  coqify
    (getenv_else "XDG_DATA_HOME" (fun () -> (home ~warn) / ".local/share"))

let xdg_config_home warn =
  coqify
    (getenv_else "XDG_CONFIG_HOME" (fun () -> (home ~warn) / ".config"))

let xdg_data_dirs warn =
  let sys_dirs =
    try
      List.map coqify (path_to_list (Sys.getenv "XDG_DATA_DIRS"))
    with
      | Not_found -> [datadir ()]
  in
  xdg_data_home warn :: sys_dirs

let xdg_dirs ~warn =
  List.filter Sys.file_exists (xdg_data_dirs warn)

(* Print the configuration information *)

let print_config ?(prefix_var_name="") f coq_src_subdirs =
  let open Printf in
  fprintf f "%sLOCAL=%s\n" prefix_var_name (if Coq_config.local then "1" else "0");
  fprintf f "%sCOQLIB=%s/\n" prefix_var_name (coqlib ());
  fprintf f "%sDOCDIR=%s/\n" prefix_var_name (docdir ());
  fprintf f "%sOCAMLFIND=%s\n" prefix_var_name (ocamlfind ());
  fprintf f "%sCAMLFLAGS=%s\n" prefix_var_name Coq_config.caml_flags;
  fprintf f "%sWARN=%s\n" prefix_var_name "-warn-error +a-3";
  fprintf f "%sHASNATDYNLINK=%s\n" prefix_var_name
    (if Coq_config.has_natdynlink then "true" else "false");
  fprintf f "%sCOQ_SRC_SUBDIRS=%s\n" prefix_var_name (String.concat " " coq_src_subdirs)

