(** Equivalent of rm -f *)

let safe_remove f =
  try Unix.chmod f 0o644; Sys.remove f with _ -> ()

(** * Generate an implementation of 63-bit arithmetic *)

let ml_file_copy input output =
  safe_remove output;
  let i = open_in input in
  let o = open_out output in
  let pr s = Printf.fprintf o s in
  pr "(* DO NOT EDIT THIS FILE: automatically generated by ./write_uint63.ml *)\n";
  pr "(* see uint63_amd64.ml and uint63_x86.ml *)\n";
  try
    while true do
      output_string o (input_line i); output_char o '\n'
    done
  with End_of_file ->
    close_in i;
    close_out o;
    Unix.chmod output 0o444

let write_uint63 () =
  ml_file_copy
    (if max_int = 1073741823 (* 32-bits *) then "uint63_x86.ml"
     else (* 64 bits *) "uint63_amd64.ml")
    "uint63.ml"

let () = write_uint63 ()
