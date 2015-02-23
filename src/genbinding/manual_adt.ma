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

include "basics/lists/list.ma".
include "basics/deqsets.ma".
include "genbinding/names.ma".
include "genbinding/tp.ma".

record STT_sig : Type[1] ≝ {
  (* types *)
  stt_ctx  : ℕ → Type[0];
  
  (* constructors *)
  stt_par  : 𝔸 → stt_ctx 0;
  stt_app  : stt_ctx 0 → stt_ctx 0 → stt_ctx 0;
  stt_lam  : 𝔸 → stt_ctx 0 → stt_ctx 0;
  
  (* free variables *)
  stt_FV   : ∀k.stt_ctx k → list 𝔸;
  
  (* ctx operations *)
  stt_nu   : ∀k.stt_ctx k → 𝔸 → stt_ctx (S k);
  stt_open : ∀k.stt_ctx (S k) → 𝔸 → stt_ctx k;
    
  (* recursion principle *)
  stt_tm_rec : ∀P:stt_ctx 0 → Type[0].∀C.
      (∀x:𝔸.P (stt_par x)) → 
      (∀v1,v2. P v1 → P v2 → P (stt_app v1 v2)) → 
      (∀x,v.x ∉ stt_FV ? v → x ∉ C →  P (stt_open ? v x) → P (stt_lam x (stt_open ? v x))) →
      ∀u.P u

}.

(*** TERMS AND CONTEXTS ***)
definition stt_tm ≝ λS.stt_ctx S O.

(* notation for open and close *)
notation "hvbox(u⌈x⌉)"
  with precedence 45
  for @{ 'open $u $x }.
interpretation "ln term variable open" 'open u x = (stt_open ?? u x).
notation < "hvbox(ν x break . u)"
 with precedence 20
for @{'nu $x $u }.
notation > "ν list1 x sep , . term 19 u" with precedence 20
  for ${ fold right @{$u} rec acc @{'nu $x $acc)} }.
interpretation "ln term variable close" 'nu x u = (stt_nu ?? u x).