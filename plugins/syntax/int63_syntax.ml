(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)


(* Poor's man DECLARE PLUGIN *)
let __coq_plugin_name = "int63_syntax_plugin"
let () = Mltop.add_known_module __coq_plugin_name

(* digit-based syntax for int63 *)

open Bigint
open Names
open Glob_term

(*** Constants for locating int63 constructors ***)

let make_dir l = DirPath.make (List.rev_map Id.of_string l)
let make_path dir id = Libnames.make_path (make_dir dir) (Id.of_string id)

let is_gr c gr = match DAst.get c with
| GRef (r, _) -> GlobRef.equal r gr
| _ -> false

let make_mind mp id = Names.MutInd.make2 mp (Label.make id)
let make_mind_mpfile dir id = make_mind (ModPath.MPfile (make_dir dir)) id
let make_mind_mpdot dir modname id =
  let mp = ModPath.MPdot (ModPath.MPfile (make_dir dir), Label.make modname)
  in make_mind mp id


(* int63 stuff *)
let int63_module = ["Coq"; "Numbers"; "Cyclic"; "Int63"; "Int63"]
let int63_path = make_path int63_module "int"
let int63_id = make_mind_mpfile int63_module
let int63_scope = "int63_scope"

(*** Definition of the Non_closed exception, used in the pretty printing ***)
exception Non_closed

(*** Parsing for int63 in digital notation ***)

(* parses a *non-negative* integer (from bigint.ml) into an int63
   wraps modulo 2^63 *)

(* TODO: should use string conversion rather than going through bigint *)

let rec int63_of_pos_bigint i =
  if equal i zero then Uint63.of_int 0
  else
    let (quo,rem) = div2_with_rest i in
    if rem then Uint63.add (Uint63.of_int 1)
      (Uint63.mul (Uint63.of_int 2) (int63_of_pos_bigint quo))
    else Uint63.mul (Uint63.of_int 2) (int63_of_pos_bigint quo)

let int63_of_pos_bigint ?loc n =
  let i = int63_of_pos_bigint n in
  DAst.make ?loc (GInt i)

let error_negative ?loc =
  CErrors.user_err ?loc ~hdr:"interp_int63" (Pp.str "int63 are only non-negative numbers.")

let error_overflow ?loc n =
  CErrors.user_err ?loc ~hdr:"interp_int63" Pp.(str "overflow in int63 literal: " ++ str (to_string n))

let interp_int63 ?loc n =
  if is_pos_or_zero n
  then
    if less_than n (pow two 63)
    then int63_of_pos_bigint ?loc n
    else error_overflow ?loc n
  else error_negative ?loc

(* Pretty prints an int63 *)

let bigint_of_int63 c =
  match DAst.get c with
  | GInt i -> of_string (Uint63.to_string i)
  | _ -> raise Non_closed

let uninterp_int63 (AnyGlobConstr i) =
  try Some (bigint_of_int63 i)
  with Non_closed -> None

let at_declare_ml_module f x =
  Mltop.declare_cache_obj (fun () -> f x) __coq_plugin_name

(* Actually declares the interpreter for int63 *)

let _ =
  let open Notation in
  register_bignumeral_interpretation int63_scope (interp_int63, uninterp_int63);
  at_declare_ml_module enable_prim_token_interpretation
    { pt_local = false;
      pt_scope = int63_scope;
      pt_interp_info = Uid int63_scope;
      pt_required = (int63_path, int63_module);
      pt_refs = [];
      pt_in_match = false }
