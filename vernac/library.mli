(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

(** This module provides functions to load, open and save
  libraries. Libraries correspond to the subclass of modules that
  coincide with a file on disk (the ".vo" files). Libraries on the
  disk comes with checksums (obtained with the [Digest] module), which
  are checked at loading time to prevent inconsistencies between files
  written at various dates.
*)

(** Type of libraries loaded in memory *)
type library_t

(** {6 ... }
    Require = load in the environment *)
val require_library_from_dirpath : library_t list -> unit

(** Intern from a .vo file located by libresolver *)
val intern_from_file :
  CUnix.physical_path -> library_t

module Intern : sig
  module Provenance : sig
    type t = string * string
    (** A pair of [kind, object], for example ["file",
        "/usr/local/foo.vo"], used for error messages. *)
  end
  type t = DirPath.t -> library_t * Provenance.t
end

val require_library_syntax_from_dirpath
  :  intern:Intern.t
  -> DirPath.t Loc.located list
  -> library_t list

(** {6 Start the compilation of a library } *)

(** Segments of a library *)
type seg_sum
type seg_lib
type seg_proofs = Opaques.opaque_disk
type seg_vm = Vmlibrary.compiled_library

(** End the compilation of a library and save it to a ".vo" file, or a
    ".vos" file, depending on the todo_proofs argument.

    [output_native_objects]: when producing vo objects, also compile
    the native-code version. *)

type 'doc todo_proofs =
 | ProofsTodoNone (* for .vo *)
 | ProofsTodoSomeEmpty of Future.UUIDSet.t (* for .vos *)

val save_library_to :
  'document todo_proofs ->
  output_native_objects:bool ->
  DirPath.t -> string -> unit

(** Save library to library_t format, that can be used later in
    [require_library_syntax_from_dirpath] *)
val save_library : DirPath.t -> library_t

val save_library_raw : string -> seg_sum -> seg_lib -> seg_proofs -> seg_vm -> unit

(** {6 Interrogate the status of libraries } *)

  (** - Tell if a library is loaded *)
val library_is_loaded : DirPath.t -> bool

  (** - Tell which libraries are loaded *)
val loaded_libraries : unit -> DirPath.t list

(** {6 Native compiler. } *)
val native_name_from_filename : string -> string

(** {6 Opaque accessors} *)
val indirect_accessor : Global.indirect_accessor
[@@deprecated "Most commands should not be accessing opaque data."]
