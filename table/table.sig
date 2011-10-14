(* Tables *)
(* Author: Frank Pfenning *)

(* This provides a common interface to hash tables *)
(* red/black trees and similar data structures *)

signature TABLE =
sig
  type key (* parameter *)
  type 'a entry = key * 'a

  type 'a Table
  val new : int -> 'a Table		(* size hint *)
  val insert : 'a Table -> 'a entry -> unit
  val insertShadow : 'a Table -> 'a entry -> ('a entry) option
  val lookup : 'a Table -> key -> 'a option
  val clear : 'a Table -> unit

  val app : ('a entry -> unit) -> 'a Table -> unit
end;
