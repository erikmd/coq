(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(**********************************)
(**  Configuration script for Coq *)
(**********************************)
open Printf
open Conf.Util
open Conf.CmdArgs
open Conf.CmdArgs.Prefs

let (/) = Filename.concat

let coq_version = "8.15+alpha"
let vo_magic = 81491
let state_magic = 581491
let is_a_released_version = false
let _verbose = ref false (* for debugging this script *)

(* Support don't ask *)
let cprintf prefs x =
  if prefs.interactive
  then cprintf x
  else Printf.ifprintf stdout x

(** Default OCaml binaries *)

type camlexec =
  { mutable find : string;
    mutable top : string;
    mutable lex : string;
    mutable yacc : string;
  }

let camlexec =
  { find = "ocamlfind";
    top = "ocaml";
    lex = "ocamllex";
    yacc = "ocamlyacc";
  }

let reset_caml_lex c o = c.lex <- o
let reset_caml_yacc c o = c.yacc <- o
let reset_caml_top c o = c.top <- o
let reset_caml_find c o = c.find <- o

let coq_debug_flag prefs = if prefs.debug then "-g" else ""
let coq_profile_flag prefs = if prefs.profile then "-p" else ""
let coq_annot_flag prefs = if prefs.annot then "-annot" else ""
let coq_bin_annot_flag prefs = if prefs.bin_annot then "-bin-annot" else ""

(* This variable can be overridden only for debug purposes, use with
   care. *)
let coq_safe_string = "-safe-string"
let coq_strict_sequence = "-strict-sequence"

(* Query for the arch *)
let arch prefs = arch prefs.arch

(** NB: [arch_is_win32] is broader than [os_type_win32], cf. cygwin *)

let arch_is_win32 arch = arch = "win32"

let resolve_binary_suffixes arch =
  (if arch_is_win32 arch then ".exe" else ""),
  (if os_type_win32 then ".dll" else ".so")

(** * Git Precommit Hook *)
let install_precommit_hook prefs =
  let f = ".git/hooks/pre-commit" in
  if dir_exists ".git/hooks" && not (Sys.file_exists f) then begin
    cprintf prefs "Creating pre-commit hook in %s" f;
    let o = open_out f in
    let pr s = fprintf o s in
    pr "#!/bin/sh\n";
    pr "\n";
    pr "if [ -x dev/tools/pre-commit ]; then\n";
    pr "    exec dev/tools/pre-commit\n";
    pr "fi\n";
    close_out o;
    Unix.chmod f 0o775
  end

(** * Browser command *)

let browser prefs arch =
  match prefs.browser with
  | Some b -> b
  | None when arch_is_win32 arch -> "start %s"
  | None when arch = "Darwin" -> "open %s"
  | _ -> "firefox -remote \"OpenURL(%s,new-tab)\" || firefox %s &"

(** * OCaml programs *)
module CamlConf = struct
  type t =
    { camlbin : string
    ; caml_version : string
    ; camllib : string
    ; findlib_version : string
    }
end

let resolve_caml prefs =
  let () = match prefs.ocamlfindcmd with
    | Some cmd -> reset_caml_find camlexec cmd
    | None ->
       try reset_caml_find camlexec (which camlexec.find)
       with Not_found ->
         die (sprintf "Error: cannot find '%s' in your path!\n" camlexec.find ^
                "Please adjust your path or use the -ocamlfind option of ./configure")
  in
  if not (is_executable camlexec.find)
  then die ("Error: cannot find the executable '"^camlexec.find^"'.")
  else
    let findlib_version, _ = run camlexec.find ["query"; "findlib"; "-format"; "%v"] in
    let caml_version, _ = run camlexec.find ["ocamlc";"-version"] in
    let camllib, _ = run camlexec.find ["printconf";"stdlib"] in
    let camlbin = (* TODO beurk beurk beurk *)
      Filename.dirname (Filename.dirname camllib) / "bin/" in
    let () =
      if is_executable (camlbin / "ocamllex")
      then reset_caml_lex camlexec (camlbin / "ocamllex") in
    let () =
      if is_executable (camlbin / "ocamlyacc")
      then reset_caml_yacc camlexec (camlbin / "ocamlyacc") in
    let () =
      if is_executable (camlbin / "ocaml")
      then reset_caml_top camlexec (camlbin / "ocaml") in
    { CamlConf.camlbin; caml_version; camllib; findlib_version }

(** Caml version as a list of string, e.g. ["4";"00";"1"] *)

let caml_version_list { CamlConf.caml_version } =
  numeric_prefix_list caml_version

(** Same, with integers in the version list *)

let caml_version_nums caml_version_list =
  try
    if List.length caml_version_list < 2 then failwith "bad version";
    List.map int_of_string caml_version_list
  with _ ->
    die ("I found the OCaml compiler but cannot read its version number!\n" ^
         "Is it installed properly?")

let check_caml_version prefs caml_version caml_version_nums =
  if caml_version_nums >= [4;5;0] then
    cprintf prefs "You have OCaml %s. Good!" caml_version
  else
    let () = cprintf prefs "Your version of OCaml is %s." caml_version in
    if prefs.force_caml_version then
      warn "Your version of OCaml is outdated."
    else
      die "You need OCaml 4.05.0 or later."

let findlib_version_list { CamlConf.findlib_version } =
  numeric_prefix_list findlib_version

let findlib_version_nums findlib_version_list =
  try
    if List.length findlib_version_list < 2 then failwith "bad version";
    List.map int_of_string findlib_version_list
  with _ ->
    die ("I found ocamlfind but cannot read its version number!\n" ^
         "Is it installed properly?")

let check_findlib_version prefs findlib_version findlib_version_nums =
  if findlib_version_nums >= [1;4;1] then
    cprintf prefs "You have OCamlfind %s. Good!" findlib_version
  else
    let () = cprintf prefs "Your version of OCamlfind is %s." findlib_version in
    if prefs.force_findlib_version then
      warn "Your version of OCamlfind is outdated."
    else
      die "You need OCamlfind 1.4.1 or later."

let camltag caml_version_list =
  match caml_version_list with
  | x::y::_ -> "OCAML"^x^y
  | _ -> assert false

(** Explanation of disabled warnings:
    4: fragile pattern matching: too common in the code and too annoying to avoid in general
    9: missing fields in a record pattern: too common in the code and not worth the bother
    27: innocuous unused variable: innocuous
    41: ambiguous constructor or label: too common
    42: disambiguated counstructor or label: too common
    44: "open" shadowing already defined identifier: too common, especially when some are aliases
    45: "open" shadowing a label or constructor: see 44
    48: implicit elimination of optional arguments: too common
    58: "no cmx file was found in path": See https://github.com/ocaml/num/issues/9
    67: "unused functor parameter" seems totally bogus
    68: "This pattern depends on mutable state" no idea what it means, dune builds don't display it
*)

let coq_warnings = "-w +a-4-9-27-41-42-44-45-48-58-67-68"
let coq_warn_error prefs =
    if prefs.warn_error
    then "-warn-error +a"
    else ""

(* Flags used to compile Coq and plugins (via coq_makefile) *)
let caml_flags coq_annot_flag coq_bin_annot_flag =
  Printf.sprintf "-thread -rectypes %s %s %s %s %s" coq_warnings coq_annot_flag coq_bin_annot_flag coq_safe_string coq_strict_sequence

(* Flags used to compile Coq but _not_ plugins (via coq_makefile) *)
let coq_caml_flags =
  coq_warn_error

let shorten_camllib camlenv s =
  let { CamlConf.camllib } = camlenv in
  if starts_with s (camllib^"/") then
    let l = String.length camllib + 1 in
    "+" ^ String.sub s l (String.length s - l)
  else s

(** * Native compiler *)

let msg_byteonly =
  "Only the bytecode version of Coq will be available."

let msg_no_ocamlopt () =
  warn "Cannot find the OCaml native-code compiler.\n%s" msg_byteonly

let msg_no_dynlink_cmxa prefs =
  warn "Cannot find native-code dynlink library.\n%s" msg_byteonly;
  cprintf prefs "For building a native-code Coq, you may try to first";
  cprintf prefs "compile and install a dummy dynlink.cmxa (see dev/dynlink.ml)";
  cprintf prefs "and then run ./configure -natdynlink no"

let check_native prefs camlenv =
  let () = if prefs.byteonly then raise Not_found in
  let version, _ = tryrun camlexec.find ["opt";"-version"] in
  if version = "" then let () = msg_no_ocamlopt () in raise Not_found
  else if fst (tryrun camlexec.find ["query";"dynlink"]) = ""
  then let () = msg_no_dynlink_cmxa prefs in raise Not_found
  else
    let () =
      let { CamlConf.caml_version } = camlenv in
      if version <> caml_version then
        warn "Native and bytecode compilers do not have the same version!"
    in cprintf prefs "You have native-code compilation. Good!"

let best_compiler prefs camlenv =
  try check_native prefs camlenv; "opt" with Not_found -> "byte"

(** * Native dynlink *)

let hasnatdynlink prefs best_compiler = prefs.natdynlink && best_compiler = "opt"

let natdynlinkflag hasnatdynlink =
  if hasnatdynlink then "true" else "false"

(** * OS dependent libraries *)

let operating_system arch =
  if starts_with arch "sun4" then
    let os, _ = run "uname" ["-r"] in
    if starts_with os "5" then
      "Sun Solaris "^os
    else
      "Sun OS "^os
  else
    (try Sys.getenv "OS" with Not_found -> "")

(** Check for dune *)

let dune_install_warning () =
  warn "You are using Dune < 2.9, the install procedure will not respect the -docdir and -configdir configure directives; please see dev/doc/INSTALL.make.md for more information"

(* returns true if dune >= 2.9 *)
let check_for_dune_29 () =
  let dune_version, _  = tryrun "dune" ["--version"] in
  let dune_version = List.map int_of_string (numeric_prefix_list dune_version) in
  match dune_version with
  (* Development version, consider it >= 2.9 *)
  | [] -> true
  | _ ->
    if dune_version < [2;9;0] then
      (dune_install_warning ();
       false)
    else
      true

(** Zarith library *)

let check_for_zarith prefs =
  let zarith,_ = tryrun camlexec.find ["query";"zarith"] in
  let zarith_cmai base = Sys.file_exists (base / "z.cmi") && Sys.file_exists (base / "zarith.cma") in
  let zarith_version, _ = run camlexec.find ["query"; "zarith"; "-format"; "%v"] in
  match zarith with
  | ""  ->
    die "Zarith library not installed, required"
  | _ when not (zarith_cmai zarith) ->
    die "Zarith library installed but no development files found (try installing the -dev package)"
  | _   ->
    let zarith_version_int = List.map int_of_string (numeric_prefix_list zarith_version) in
    if zarith_version_int >= [1;10;0] then
      cprintf prefs "You have the Zarith library %s installed. Good!" zarith_version
    else
      die ("Zarith version 1.10 is required, you have " ^ zarith_version)

(** * lablgtk3 and CoqIDE *)

(** Detect and/or verify the Lablgtk3 location *)

let get_lablgtkdir () =
  tryrun camlexec.find ["query";"lablgtk3-sourceview3"]

(** Detect and/or verify the Lablgtk2 version *)

let check_lablgtk_version () =
  let v, _ = tryrun camlexec.find ["query"; "-format"; "%v"; "lablgtk3"] in
  try
    let vl = numeric_prefix_list v in
    let vn = List.map int_of_string vl in
    if vn < [3; 1; 0] then
      (false, v)
    else
      (true, v)
  with _ -> (false, v)

let pr_ide = function No -> "no" | Byte -> "only bytecode" | Opt -> "native"

exception Ide of ide

(** If the user asks an impossible coqide, we abort the configuration *)

let set_ide prefs ide msg = match ide, prefs.coqide with
  | No, Some (Byte|Opt)
  | Byte, Some Opt -> die (msg^":\n=> cannot build requested CoqIDE")
  | _ ->
    cprintf prefs "%s:\n=> %s CoqIDE will be built." msg (pr_ide ide);
    raise (Ide ide)

(* XXX *)
let lablgtkdir = ref ""

(** Which CoqIDE is possible ? Which one is requested ?
    This function also sets the lablgtkdir reference in case of success. *)

let check_coqide prefs best_compiler camlenv =
  if prefs.coqide = Some No then set_ide prefs No "CoqIde manually disabled";
  let dir, via = get_lablgtkdir () in
  if dir = ""
  then set_ide prefs No "LablGtk3 or LablGtkSourceView3 not found"
  else
    let (ok, version) = check_lablgtk_version () in
    let found = sprintf "LablGtk3 and LablGtkSourceView3 found (%s)" version in
    if not ok then set_ide prefs No (found^", but too old (required >= 3.1.0, found " ^ version ^ ")");
    (* We're now sure to produce at least one kind of coqide *)
    lablgtkdir := shorten_camllib camlenv dir;
    if prefs.coqide = Some Byte then set_ide prefs Byte (found^", bytecode requested");
    if best_compiler <> "opt" then set_ide prefs Byte (found^", but no native compiler");
    let { CamlConf.camllib } = camlenv in
    if not (Sys.file_exists (camllib/"threads"/"threads.cmxa")) then
      set_ide prefs Byte (found^", but no native threads");
    set_ide prefs Opt (found^", with native threads")

let coqide prefs best_compiler camlenv =
  try check_coqide prefs best_compiler camlenv
  with Ide Opt -> "opt" | Ide Byte -> "byte" | Ide No -> "no"

(** System-specific CoqIDE flags *)

(* XXX *)
let idearchflags = ref ""
let idearchfile = ref ""
let idecdepsflags = ref ""
let idearchdef = ref "X11"

let coqide_flags prefs coqide arch =
  match coqide, arch with
    | "opt", "Darwin" when prefs.macintegration ->
      let osxdir,_ = tryrun camlexec.find ["query";"lablgtkosx"] in
      if osxdir <> "" then begin
        idearchflags := "lablgtkosx.cma";
        idearchdef := "QUARTZ"
      end
    | "opt", "win32" ->
      idearchfile := "ide/coqide/ide_win32_stubs.o ide/coqide/coq_icon.o";
      idecdepsflags := "-custom";
      idearchflags := "-ccopt '-subsystem windows'";
      idearchdef := "WIN32"
    | _, "win32" ->
      idearchflags := "-ccopt '-subsystem windows'";
      idearchdef := "WIN32"
    | _ -> ()

(** * strip command *)

let strip prefs arch hasnatdynlink =
  if arch = "Darwin" then
    if hasnatdynlink then "true" else "strip"
  else
    if prefs.profile || prefs.debug then "true" else begin
    let _, all = run camlexec.find ["ocamlc";"-config"] in
    let strip = String.concat "" (List.map (fun l ->
        match string_split ' ' l with
        | "ranlib:" :: cc :: _ -> (* on windows, we greb the right strip *)
             Str.replace_first (Str.regexp "ranlib") "strip" cc
        | _ -> ""
      ) all) in
    if strip = "" then "strip" else strip
    end


(** * Documentation : do we have latex, hevea, ... *)

let check_sphinx_deps () =
  ignore (run (which "python3") ["doc/tools/coqrst/checkdeps.py"])

let check_doc () =
  let err s =
    die (sprintf "A documentation build was requested, but %s was not found." s);
  in
  if not (program_in_path "python3") then err "python3";
  if not (program_in_path "sphinx-build") then err "sphinx-build";
  check_sphinx_deps ()

(** * Installation directories : bindir, libdir, mandir, docdir, etc *)

let coqtop = Sys.getcwd ()

let unix arch = os_type_cygwin || not (arch_is_win32 arch)

(** Variable name, description, ref in prefs, default dir, prefix-relative *)

type path_style =
  | Absolute of string (* Should start with a "/" *)
  | Relative of string (* Should not start with a "/" *)

let install prefs = [
  "COQPREFIX", "Coq", prefs.prefix,
    Relative "", Relative "";
  "COQLIBINSTALL", "the Coq library", prefs.libdir,
    Relative "lib", Relative "lib/coq";
  "CONFIGDIR", "the Coqide configuration files", prefs.configdir,
    Relative "config", Absolute "/etc/xdg/coq";
  "DATADIR", "the Coqide data files", prefs.datadir,
    Relative "share", Relative "share/coq";
  "MANDIR", "the Coq man pages", prefs.mandir,
    Relative "man", Relative "share/man";
  "DOCDIR", "documentation prefix path for all Coq packages", prefs.docdir,
    Relative "doc", Relative "share/doc";
 ]

let strip_trailing_slash_if_any p =
  if p.[String.length p - 1] = '/' then String.sub p 0 (String.length p - 1) else p

let use_suffix prefix = function
  | Relative "" -> prefix
  | Relative suff -> prefix ^ "/" ^ suff
  | Absolute path -> path

let relativize = function
  (* Turn a global layout based on some prefix to a relative layout *)
  | Relative _ as suffix -> suffix
  | Absolute path -> Relative (String.sub path 1 (String.length path - 1))

let find_suffix prefix path = match prefix with
  | None -> Absolute path
  | Some p ->
     let p = strip_trailing_slash_if_any p in
     let lpath = String.length path in
     let lp = String.length p in
     if lpath > lp && String.sub path 0 lp = p then
       Relative (String.sub path (lp+1) (lpath - lp - 1))
     else
       Absolute path

let do_one_instdir prefs arch (var,msg,uservalue,selfcontainedlayout,unixlayout) =
  let dir,suffix =
    let env_prefix =
      match prefs.prefix with
      | None ->
        begin
          try Some (Sys.getenv "COQ_CONFIGURE_PREFIX")
          with
          | Not_found when prefs.interactive -> None
          | Not_found -> Some Sys.(getcwd () ^ "/../install/default")
        end
      | p -> p
    in match uservalue, env_prefix with
    | Some d, p -> d,find_suffix p d
    | _, Some p ->
      let suffix = if (arch_is_win32 arch) then selfcontainedlayout else relativize unixlayout in
      use_suffix p suffix, suffix
    | _, p ->
      let suffix = if (unix arch) then unixlayout else selfcontainedlayout in
      let base = if (unix arch) then "/usr/local" else "C:/coq" in
      let dflt = use_suffix base suffix in
      let () = printf "Where should I install %s [%s]? " msg dflt in
      let line = read_line () in
      if line = "" then (dflt,suffix) else (line,find_suffix None line)
  in
  (var,msg,dir,suffix)

let install_dirs prefs arch = List.map (do_one_instdir prefs arch) (install prefs)

let select var install_dirs = List.find (fun (v,_,_,_) -> v=var) install_dirs

module CoqEnv = struct
  type t =
    { coqlib : string
    ; coqlibsuffix : path_style
    ; docdir : string
    ; docdirsuffix : path_style
    ; configdir : string
    ; configdirsuffix : path_style
    ; datadir : string
    ; datadirsuffix : path_style }
end

let resolve_coqenv install_dirs =
  let coqlib,coqlibsuffix =
    let (_,_,d,s) = select "COQLIBINSTALL" install_dirs in d,s in
  let docdir,docdirsuffix =
    let (_,_,d,s) = select "DOCDIR" install_dirs in d,s in
  let configdir,configdirsuffix =
    let (_,_,d,s) = select "CONFIGDIR" install_dirs in d,s in
  let datadir,datadirsuffix =
    let (_,_,d,s) = select "DATADIR" install_dirs in d,s in
  { CoqEnv.coqlib; coqlibsuffix; docdir; docdirsuffix; configdir; configdirsuffix; datadir; datadirsuffix }

(** * CC runtime flags *)

(* Note that Coq's VM requires at least C99-compliant floating-point
   arithmetic; this should be ensured by OCaml's own C flags, which
   set a minimum of [--std=gnu99] ; modern compilers by default assume
   C11 or later, so no explicit [--std=] flags are added by OCaml *)
let cflags_dflt = "-Wall -Wno-unused -g -O2"

let cflags_sse2 = "-msse2 -mfpmath=sse"

(* cflags, sse2_math = *)
let compute_cflags () =
  let _, slurp =
    (* Test SSE2_MATH support <https://stackoverflow.com/a/45667927> *)
    tryrun camlexec.find
      ["ocamlc"; "-ccopt"; cflags_dflt ^ " -march=native -dM -E " ^ cflags_sse2;
       "-c"; coqtop/"dev/header.c"] in  (* any file *)
  if List.exists (fun line -> starts_with line "#define __SSE2_MATH__ 1") slurp
  then (cflags_dflt ^ " " ^ cflags_sse2, true)
  else (cflags_dflt, false)

(** Test at configure time that no harmful double rounding seems to
    be performed with an intermediate 80-bit representation (x87).

    If this test fails but SSE2_MATH is available, the build can go
    further as Coq's primitive floats will use it through a dedicated
    external C implementation (instead of relying on OCaml operations)

    If this test fails and SSE2_MATH is not available, abort.
 *)
let check_fmath sse2_math =
  let add = (+.) in
  let b = ldexp 1. 53 in
  let s = add 1. (ldexp 1. (-52)) in
  if (add b s <= b || add b 1. <> b || ldexp 1. (-1074) <= 0.)
     && not sse2_math then
    die "Detected non IEEE-754 compliant architecture (or wrong \
         rounding mode). Use of Float is thus unsafe."

(** * OCaml runtime flags *)

(** Do we use -custom (yes by default on Windows and MacOS) *)

let custom_os arch = arch_is_win32 arch || arch = "Darwin"

let use_custom prefs arch = match prefs.custom with
  | Some b -> b
  | None -> custom_os arch

let custom_flag prefs arch = if use_custom prefs arch then "-custom" else ""

(* XXX *)
let build_loadpath =
  ref "# you might want to set CAML_LD_LIBRARY_PATH by hand!"

let config_runtime prefs arch coqenv =
  let { CoqEnv.coqlib } = coqenv in
  match prefs.vmbyteflags with
  | Some flags -> string_split ',' flags
  | _ when use_custom prefs arch -> [custom_flag prefs arch]
  | _ ->
    let ld="CAML_LD_LIBRARY_PATH" in
    build_loadpath := sprintf "export %s:=%s/kernel/byterun:$(%s)" ld coqtop ld;
    ["-dllib";"-lcoqrun";"-dllpath";coqlib/"kernel/byterun"]

let vmbyteflags prefs arch coqenv = config_runtime prefs arch coqenv

let esc s = if String.contains s ' ' then "\"" ^ s ^ "\"" else s

(** * Summary of the configuration *)

let pr_native = function
  | NativeYes -> "yes" | NativeNo -> "no" | NativeOndemand -> "ondemand"

let print_summary prefs arch operating_system camlenv vmbyteflags custom_flag best_compiler install_dirs coqide hasnatdynlink browser =
  let { CamlConf.caml_version; camlbin; camllib } = camlenv in
  let pr s = printf s in
  pr "\n";
  pr "  Architecture                : %s\n" arch;
  if operating_system <> "" then
    pr "  Operating system            : %s\n" operating_system;
  pr "  Sys.os_type                 : %s\n" Sys.os_type;
  pr "  Coq VM bytecode link flags  : %s\n" (String.concat " " vmbyteflags);
  pr "  Other bytecode link flags   : %s\n" custom_flag;
  pr "  OCaml version               : %s\n" caml_version;
  pr "  OCaml binaries in           : %s\n" (esc camlbin);
  pr "  OCaml library in            : %s\n" (esc camllib);
  pr "  OCaml flambda flags         : %s\n" (String.concat " " prefs.flambda_flags);
  if best_compiler = "opt" then
    pr "  Native dynamic link support : %B\n" hasnatdynlink;
  if coqide <> "no" then
    pr "  Lablgtk3 library in         : %s\n" (esc !lablgtkdir);
  if !idearchdef = "QUARTZ" then
    pr "  Mac OS integration is on\n";
  pr "  CoqIDE                      : %s\n" coqide;
  pr "  Documentation               : %s\n"
    (if prefs.withdoc then "All" else "None");
  pr "  Web browser                 : %s\n" browser;
  pr "  Coq web site                : %s\n" prefs.coqwebsite;
  pr "  Bytecode VM enabled         : %B\n" prefs.bytecodecompiler;
  pr "  Native Compiler enabled     : %s\n\n" (pr_native prefs.nativecompiler);
  (pr "  Paths for true installation:\n";
   List.iter
     (fun (_,msg,dir,_) -> pr "  - %s will be copied in %s\n" msg (esc dir))
     install_dirs);
  pr "\n";
  pr "If anything is wrong above, please restart './configure'.\n\n";
  pr "*Warning* To compile the system for a new architecture\n";
  pr "          don't forget to do a 'make clean' before './configure'.\n"

(** * Build the dev/ocamldebug-coq file *)

let write_dbg_wrapper camlenv f =
  let { CamlConf.camlbin } = camlenv in
  safe_remove f;
  let o = open_out_bin f in  (* _bin to avoid adding \r on Cygwin/Windows *)
  let pr s = fprintf o s in
  pr "#!/bin/sh\n\n";
  pr "###### ocamldebug-coq : a wrapper around ocamldebug for Coq ######\n\n";
  pr "# DO NOT EDIT THIS FILE: automatically generated by ../configure #\n\n";
  pr "export COQTOP=%S\n" coqtop;
  pr "OCAMLDEBUG=%S\n" (camlbin^"/ocamldebug");
  pr ". $COQTOP/dev/ocamldebug-coq.run\n";
  close_out o;
  Unix.chmod f 0o555

(** * Build the config/coq_config.ml file *)

let write_configml camlenv coqenv caml_flags caml_version_nums arch arch_is_win32 hasnatdynlink browser prefs f =
  let { CoqEnv.coqlib; coqlibsuffix; configdir; configdirsuffix; docdir; docdirsuffix; datadir; datadirsuffix } = coqenv in
  let { CamlConf.caml_version } = camlenv in
  safe_remove f;
  let o = open_out f in
  let pr s = fprintf o s in
  let pr_s = pr "let %s = %S\n" in
  let pr_b = pr "let %s = %B\n" in
  let pr_i = pr "let %s = %d\n" in
  let pr_i32 = pr "let %s = %dl\n" in
  let pr_p s o = pr "let %s = %S\n" s
    (match o with Relative s -> s | Absolute s -> s) in
  let pr_li n l = pr "let %s = [%s]\n" n (String.concat ";" (List.map string_of_int l)) in
  pr "(* DO NOT EDIT THIS FILE: automatically generated by ../configure *)\n";
  pr "(* Exact command that generated this file: *)\n";
  pr "(* %s *)\n\n" (String.concat " " (Array.to_list Sys.argv));
  pr_s "coqlib" coqlib;
  pr_s "configdir" configdir;
  pr_s "datadir" datadir;
  pr_s "docdir" docdir;
  pr_p "coqlibsuffix" coqlibsuffix;
  pr_p "configdirsuffix" configdirsuffix;
  pr_p "datadirsuffix" datadirsuffix;
  pr_p "docdirsuffix" docdirsuffix;
  pr_s "ocamlfind" camlexec.find;
  pr_s "caml_flags" caml_flags;
  pr_s "version" coq_version;
  pr_s "caml_version" caml_version;
  pr_li "caml_version_nums" caml_version_nums;
  pr_s "arch" arch;
  pr_b "arch_is_win32" arch_is_win32;
  pr_s "exec_extension" !exe;
  pr "let gtk_platform = `%s\n" !idearchdef;
  pr_b "has_natdynlink" hasnatdynlink;
  pr_i32 "vo_version" vo_magic;
  pr_i "state_magic_number" state_magic;
  pr_s "browser" browser;
  pr_s "wwwcoq" prefs.coqwebsite;
  pr_s "wwwbugtracker" (prefs.coqwebsite ^ "bugs/");
  pr_s "wwwrefman" (prefs.coqwebsite ^ "distrib/V" ^ coq_version ^ "/refman/");
  pr_s "wwwstdlib" (prefs.coqwebsite ^ "distrib/V" ^ coq_version ^ "/stdlib/");
  pr_s "localwwwrefman"  ("file:/" ^ docdir ^ "/html/refman");
  pr_b "bytecode_compiler" prefs.bytecodecompiler;
  pr "type native_compiler = NativeOff | NativeOn of { ondemand : bool }\n";
  pr "let native_compiler = %s\n"
    (match prefs.nativecompiler with
     | NativeYes -> "NativeOn {ondemand=false}" | NativeNo -> "NativeOff"
     | NativeOndemand -> "NativeOn {ondemand=true}");

  let core_src_dirs = [ "boot"; "config"; "lib"; "clib"; "kernel"; "library";
                        "engine"; "pretyping"; "interp"; "gramlib"; "parsing"; "proofs";
                        "tactics"; "toplevel"; "printing"; "ide"; "stm"; "vernac" ] in
  let core_src_dirs = List.fold_left (fun acc core_src_subdir -> acc ^ "  \"" ^ core_src_subdir ^ "\";\n")
                                    ""
                                    core_src_dirs in

  pr "\nlet core_src_dirs = [\n%s]\n" core_src_dirs;
  pr "\nlet plugins_dirs = [\n";

  let plugins = match open_in "config/plugin_list" with
    | exception Sys_error _ ->
      let plugins =
        try Sys.readdir "plugins"
        with _ -> [||]
      in
      Array.sort compare plugins;
      plugins
    | ch -> Array.of_list (snd (read_lines_and_close ch))
  in
  Array.iter
    (fun f ->
      let f' = "plugins/"^f in
      if Sys.is_directory f' && f.[0] <> '.' then pr "  %S;\n" f')
    plugins;
  pr "]\n";

  pr "\nlet all_src_dirs = core_src_dirs @ plugins_dirs\n";

  close_out o;
  Unix.chmod f 0o444

(** * Build the config/Makefile file *)

let write_makefile prefs camlenv custom_flag vmbyteflags natdynlinkflag install_dirs best_compiler camltag cflags caml_flags coq_caml_flags coq_debug_flag coq_profile_flag coqide strip arch exe dll dune_29 f =
  let { CamlConf.camllib } = camlenv in
  safe_remove f;
  let o = open_out f in
  let pr s = fprintf o s in
  pr "###### config/Makefile : Configuration file for Coq ##############\n";
  pr "#                                                                #\n";
  pr "# This file is generated by the script \"configure\"               #\n";
  pr "# DO NOT EDIT IT !! DO NOT EDIT IT !! DO NOT EDIT IT !!          #\n";
  pr "# If something is wrong below, then rerun the script \"configure\" #\n";
  pr "# with the good options (see the file INSTALL).                  #\n";
  pr "#                                                                #\n";
  pr "##################################################################\n\n";
  pr "#Variable used to detect whether ./configure has run successfully.\n";
  pr "COQ_CONFIGURED=yes\n\n";
  pr "# Bytecode link flags : should we use -custom or not ?\n";
  pr "CUSTOM=%s\n" custom_flag;
  pr "VMBYTEFLAGS=%s\n" (String.concat " " vmbyteflags);
  pr "%s\n\n" !build_loadpath;
  pr "# Paths for true installation\n";
  List.iter (fun (v,msg,_,_) -> pr "# %s: path for %s\n" v msg) install_dirs;
  List.iter (fun (v,_,dir,_) -> pr "%s=%S\n" v dir) install_dirs;
  pr "\n# Coq version\n";
  pr "VERSION=%s\n" coq_version;
  pr "# Objective-Caml compile command\n";
  pr "OCAML=%S\n" camlexec.top;
  pr "OCAMLFIND=%S\n" camlexec.find;
  pr "OCAMLLEX=%S\n" camlexec.lex;
  pr "OCAMLYACC=%S\n" camlexec.yacc;
  pr "# The best compiler: native (=opt) or bytecode (=byte)\n";
  pr "BEST=%s\n\n" best_compiler;
  pr "# Ocaml version number\n";
  pr "CAMLVERSION=%s\n\n" camltag;
  pr "# Ocaml libraries\n";
  pr "CAMLLIB=%S\n\n" camllib;
  pr "# Ocaml .h directory\n";
  pr "CAMLHLIB=%S\n\n" camllib;
  pr "# Caml link command and Caml make top command\n";
  pr "# Caml flags\n";
  pr "CAMLFLAGS=%s %s\n" caml_flags coq_caml_flags;
  pr "# User compilation flag\n";
  pr "USERFLAGS=\n\n";
  (* XXX make this configurable *)
  pr "FLAMBDA_FLAGS=%s\n" (String.concat " " prefs.flambda_flags);
  pr "# Flags for GCC\n";
  pr "CFLAGS=%s\n\n" cflags;
  pr "# Compilation debug flags\n";
  pr "CAMLDEBUG=%s\n" coq_debug_flag;
  pr "CAMLDEBUGOPT=%s\n\n" coq_debug_flag;
  pr "# Compilation profile flag\n";
  pr "CAMLTIMEPROF=%s\n\n" coq_profile_flag;
  pr "# Your architecture\n";
  pr "# Can be obtain by UNIX command arch\n";
  pr "ARCH=%s\n" arch;
  pr "OCAML_INT_SIZE:=%d\n" Sys.int_size;
  pr "HASNATDYNLINK=%s\n\n" natdynlinkflag;
  pr "# Supplementary libs for some systems, currently:\n";
  pr "#  . Sun Solaris: -cclib -lunix -cclib -lnsl -cclib -lsocket\n";
  pr "#  . others     : -cclib -lunix\n";
  pr "# executable files extension, currently:\n";
  pr "#  Unix systems:\n";
  pr "#  Win32 systems : .exe\n";
  pr "EXE=%s\n" exe;
  pr "DLLEXT=%s\n\n" dll;
  pr "# the command MKDIR (try to use mkdirhier if you have problems)\n";
  pr "MKDIR=mkdir -p\n\n";
  pr "#the command STRIP\n";
  pr "# Unix systems and profiling: true\n";
  pr "# Unix systems and no profiling: strip\n";
  pr "STRIP=%s\n\n" strip;
  pr "# LablGTK\n";
  pr "# CoqIDE (no/byte/opt)\n";
  pr "HASCOQIDE=%s\n" coqide;
  pr "IDEFLAGS=%s\n" !idearchflags;
  pr "IDEOPTCDEPS=%s\n" !idearchfile;
  pr "IDECDEPS=%s\n" !idearchfile;
  pr "IDECDEPSFLAGS=%s\n" !idecdepsflags;
  pr "IDEINT=%s\n\n" !idearchdef;
  pr "# Defining REVISION\n";
  pr "# Option to control compilation and installation of the documentation\n";
  pr "WITHDOC=%s\n\n" (if prefs.withdoc then "all" else "no");
  pr "# Option to produce precompiled files for native_compute\n";
  pr "NATIVECOMPUTE=%s\n" (if prefs.nativecompiler = NativeYes then "-native-compiler yes" else "");
  pr "COQWARNERROR=%s\n" (if prefs.warn_error then "-w +default" else "");
  pr "CONFIGURE_DPROFILE=%s\n" prefs.dune_profile;
  pr "COQ_INSTALL_ENABLED=%b\n" prefs.install_enabled;
  if dune_29 then pr "DUNE_29_PLUS=yes\n";
  close_out o;
  Unix.chmod f 0o444

let write_dune_c_flags cflags f =
  safe_remove f;
  let o = open_out f in
  let pr s = fprintf o s in
  pr "(%s)\n" cflags;
  close_out o;
  Unix.chmod f 0o444

let write_configpy f =
  safe_remove f;
  let o = open_out f in
  let pr s = fprintf o s in
  pr "# DO NOT EDIT THIS FILE: automatically generated by ../configure\n";
  pr "version = '%s'\n" coq_version;
  pr "is_a_released_version = %s\n" (if is_a_released_version then "True" else "False")

(* Main configure routine *)
let main () =
  let prefs = Conf.CmdArgs.parse_args () in
  let dune_29 = check_for_dune_29 () in
  let coq_annot_flag = coq_annot_flag prefs in
  let coq_bin_annot_flag = coq_bin_annot_flag prefs in
  let coq_debug_flag = coq_debug_flag prefs in
  let coq_profile_flag = coq_profile_flag prefs in
  let arch = arch prefs in
  let arch_is_win32 = arch_is_win32 arch in
  let exe, dll = resolve_binary_suffixes arch in
  Conf.Util.exe := exe;
  install_precommit_hook prefs;
  let browser = browser prefs arch in
  let camlenv = resolve_caml prefs in
  let caml_version_list = caml_version_list camlenv in
  let caml_version_nums = caml_version_nums caml_version_list in
  check_caml_version prefs camlenv.CamlConf.caml_version caml_version_nums;
  let findlib_version_list = findlib_version_list camlenv in
  let findlib_version_nums = findlib_version_nums findlib_version_list in
  check_findlib_version prefs camlenv.CamlConf.findlib_version findlib_version_nums;
  let camltag = camltag caml_version_list in
  let best_compiler = best_compiler prefs camlenv in
  let caml_flags = caml_flags coq_annot_flag coq_bin_annot_flag in
  let coq_caml_flags = coq_caml_flags prefs in
  let hasnatdynlink = hasnatdynlink prefs best_compiler in
  let natdynlinkflag = natdynlinkflag hasnatdynlink in
  let operating_system = operating_system arch in
  check_for_zarith prefs;
  let coqide = coqide prefs best_compiler camlenv in
  let _coqide_flags : unit = coqide_flags prefs coqide arch in
  let strip = strip prefs arch hasnatdynlink in
  (if prefs.withdoc then check_doc ());
  let install_dirs = install_dirs prefs arch in
  let coqenv = resolve_coqenv install_dirs in
  let cflags, sse2_math = compute_cflags () in
  check_fmath sse2_math;
  let custom_flag = custom_flag prefs arch in
  let vmbyteflags = vmbyteflags prefs arch coqenv in
  if prefs.interactive then
    print_summary prefs arch operating_system camlenv vmbyteflags custom_flag best_compiler install_dirs coqide hasnatdynlink browser;
  write_dbg_wrapper camlenv "dev/ocamldebug-coq";
  write_configml camlenv coqenv caml_flags caml_version_nums arch arch_is_win32 hasnatdynlink browser prefs "config/coq_config.ml";
  write_makefile prefs camlenv custom_flag vmbyteflags natdynlinkflag install_dirs best_compiler camltag cflags caml_flags coq_caml_flags coq_debug_flag coq_profile_flag coqide strip arch exe dll dune_29 "config/Makefile";
  write_dune_c_flags cflags "config/dune.c_flags";
  write_configpy "config/coq_config.py";
  ()

let _ =
  main ()
