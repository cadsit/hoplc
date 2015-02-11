(*
 * File:    var.sig
 * Author:  Connor Adsit
 * Date:    2015-01-28
 * 
 * Outlines the structure and functionality of variables
 *)

signature VAR =
sig
   type t

   val compare : (t * t) -> order
   val equals : (t * t) -> bool
   val hash : t -> word

   structure Set : ORD_SET where type Key.ord_key = t
   structure Map : ORD_MAP where type Key.ord_key = t
   structure Tbl : MONO_HASH_TABLE where type Key.hash_key = t
end
