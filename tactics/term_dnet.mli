(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr
open Mod_subst

(** Dnets on constr terms.

   An instantiation of Dnet on (an approximation of) constr. It
   associates a term (possibly with Evar) with an
   identifier. Identifiers must be unique (no two terms sharing the
   same ident), and there must be a way to recover the full term from
   the identifier (function constr_of).

   The results returned here are perfect, since post-filtering is done
   inside here.

   See tactics/dnet.mli for more details.
*)

(** Identifiers to store (right hand side of the association) *)
module type IDENT = sig
  type t
  val compare : t -> t -> int

  (** how to substitute them for storage *)
  val subst : substitution -> t -> t

  (** how to recover the term from the identifier *)
  val constr_of : t -> constr
end

module type S =
sig
  type t
  type ident

  val empty : t

  (** [add c i dn] adds the binding [(c,i)] to [dn]. [c] can be a
     closed term or a pattern (with untyped Evars). No Metas accepted *)
  val add : constr -> ident -> t -> t

  (** merge of dnets. Faster than re-adding all terms *)
  val union : t -> t -> t

  val subst : substitution -> t -> t

  (*
   * High-level primitives describing specific search problems
   *)

  (** [search_pattern dn c] returns all terms/patterns in dn
     matching/matched by c *)
  val search_pattern : t -> constr -> ident list

  (** [find_all dn] returns all idents contained in dn *)
  val find_all : t -> ident list

  val map : (ident -> ident) -> t -> t

  val refresh_metas : t -> t
end

module Make :
  functor (Ident : IDENT) ->
    S with type ident = Ident.t
