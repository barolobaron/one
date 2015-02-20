(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "basics/logic.ma".
include "genbinding/names.ma".

(*****************************************************************************
 * An ostensibly named formalization of the simply typed lambda calculus     *
 *                                                                           *
 * Version history:                                                          *
 * 0.4 - file created (definition moved from theory.ma)                      * 
 *****************************************************************************)
 
inductive tp : Type[0] ≝ 
| top : tp
| arr : tp → tp → tp.

(***********************************)
(* here for lack of a better place *)
(***********************************)

definition alpha : Nset ≝ X.
notation "𝔸" non associative with precedence 90 for @{'alphabet}.
interpretation "set of names" 'alphabet = alpha.

(* duplicate-free lists of names *)
definition valid ≝ λxl:list 𝔸.∀x,xl1,xl2.xl = xl1@x::xl2 → x ∉ xl2.

(* domain of a typing environment *)
definition dom ≝ λG:list (𝔸×tp).map ?? (fst ??) G.
