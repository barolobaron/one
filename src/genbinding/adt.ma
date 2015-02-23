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
include "basics/vectors.ma".

(*****************************************************************************
 * The ostensibly named axiomatization of the simply typed lambda calculus   *
 *                                                                           *
 * Version history:                                                          *
 * 0.4 - rewritten axiomatization as a record: theory.ma is subsequently     *
 *       split into                                                          *
 *       * adt.ma      -- axiomatization up to typing                        *
 *       * adtbeta.ma  -- axiomatization of beta reduction                   *
 *       * typing.ma   -- abstract proofs up to typing                       *
 *       * subst.ma    -- definition and properties of substitution          *
 *       * subjred.ma  -- abstract proof of subject reduction                *
 * 0.3 - substantial rework up to beta reduction                             *
 * 0.2 - added proof of weakening                                            *
 * 0.1 - initial version                                                     *
 *****************************************************************************)

record SIG : Type[1] ≝ {
  sig_idx : Type[0];
  sig_ar  : sig_idx → list ℕ
}.

(*
definition IH : ∀T:ℕ → Type[0].∀P:T 0 → Type[0].
                ∀n:ℕ. (Vector 𝔸 n × T n) → Type[0] ≝ 
  λT,P,n,p. ∀yl:Vector 𝔸 n. yl # (\snd p) → P ((\snd p)⌈yl⌉).
  
definition IHs ≝ map ?? (IH T P ? ...

--→ it's a dependent types mess, we propose to define IHs inductively, 
    roughly in this form:
    
  inductive IHs (P: tm 0 → Type) : list ? → Type ≝ 
  | nil : IHs P [] 
  | cons : ∀p:?. (∀y: Vector 𝔸 ?. y # (\snd p) → P ((\fst p)⌈y⌉)) → IHs P pl → IHs P (p::pl)
  
  
-→ dom is also likely to benefit from the same kind of definition
  
*)

(*
example implementation of sig_idx for lambda calculus
inductive th_constr : Type[0] ≝ 
(* | th_par  not needed *)
| th_app : th_constr
| th_lam : th_constr.
*)

(* 
  dom ([1;2],tm) = (𝔸^1 × tm) × (𝔸^2 × tm) × unit
*)

(* CONSTRUCTOR domain = as used by the user *)
let rec cdom (T:Type[0]) (ar: list ℕ) on ar: Type[0] ≝ 
 match ar with
 [ nil ⇒ unit
 | cons n ar0 ⇒ (Vector 𝔸 n × T) × (cdom T ar0) ].


record THEORY (th_sig : SIG) : Type[1] ≝ {
  
  (* types *)
  th_ctx  : ℕ → Type[0];
  
  (* constructors *)
  th_par    : 𝔸 → th_ctx 0;
  th_constr : ∀c:sig_idx th_sig. cdom (th_ctx 0) (sig_ar th_sig c) → th_ctx 0;
  
  (* free variables 
     (doesn't depend on signature *)
  th_FV   : ∀k.th_ctx k → list 𝔸;
  
  (* ctx operations 
     (don't depend on signature) *)
  th_nu   : ∀k.th_ctx k → 𝔸 → th_ctx (S k);
  th_open : ∀k.th_ctx (S k) → 𝔸 → th_ctx k
}.

(* notation for open and close *)
notation "hvbox(u⌈x⌉)"
  with precedence 45
  for @{ 'open $u $x }.
interpretation "ln term variable open" 'open u x = (th_open ??? u x).
notation < "hvbox(ν x break . u)"
 with precedence 20
for @{'nu $x $u }.
notation > "ν list1 x sep , . term 19 u" with precedence 20
  for ${ fold right @{$u} rec acc @{'nu $x $acc)} }.
interpretation "ln term variable close" 'nu x u = (th_nu ??? u x).
definition th_apart_xl_ctx ≝ λS,T,k,xl.λu:th_ctx S T k.∀x.x ∈ xl → x ∈ th_FV ??? u → False.
definition th_apart_xl_xl ≝ λxl,yl:list 𝔸.∀x.x ∈ xl → x ∈ yl → False.
interpretation "apartness (name list-name list)" 
  'apart xl yl = (th_apart_xl_xl xl yl).
interpretation "apartness (name list-term/ctx)" 
  'apart xl u = (th_apart_xl_ctx ??? xl u).

(* we decided to put the recursion principle in a different record:
   the definitions in the THEORY record are sufficient to write more definitions
   for operations that will be used in the recursion principle
 *)

(* the domain of a constructor with the given arity (expressed as a list of ℕ) *)
inductive dom (T:ℕ → Type[0]) : list ℕ → Type[0] ≝ 
| dom_nil  : dom T [ ] 
| dom_cons : ∀m,nl. Vector 𝔸 m → T m → dom T nl → dom T (m::nl).

let rec bvars_of_dom T ar (d:dom T ar) on d : list 𝔸  ≝
  match d with
  [ dom_nil ⇒ [ ]
  | dom_cons m nl xl _ d0 ⇒ xl@(bvars_of_dom … d0) ].

axiom th_nu_list : ∀S,T,h,k.th_ctx S T k → Vector 𝔸 h → th_ctx S T (k+h).
axiom th_open_list : ∀S,T,h,k.th_ctx S T (k+h) → Vector 𝔸 h → th_ctx S T k.

interpretation "ln term generalize variable open" 'open u xl = (th_open_list ???? u xl).
interpretation "ln term generalize variable close" 'nu xl u = (th_nu_list ???? u xl).

(* the type of the set of induction hypotheses for a given constructor *)
(* takes as input the domain of a certain constructor
   (which is dependently typed with an explicit arity) *)
inductive IHs (S : SIG) (T : THEORY S) (P : th_ctx … T 0 → Type[0])
  : ∀ar:list ℕ. dom (th_ctx … T) ar → Type[0] ≝ 
| ihs_nil  : IHs S T P [ ] (dom_nil …)
| ihs_cons : ∀n,nl,xl,v,d. 
             (∀yl:Vector 𝔸 n. yl # v → P (v⌈yl⌉)) 
             → IHs S T P nl d
             → IHs S T P (n::nl) (dom_cons (th_ctx … T) n nl xl v d).
             
definition cdom_of_dom : 
  ∀S,T,c.dom (th_ctx S T) (sig_ar S c) → cdom (th_ctx S T 0) (sig_ar S c).
#S #T #c #Hdom
elim Hdom
[ normalize //
| #m #nl #xl #u #dom0 #IH
  normalize % [ %
  [ @xl
  | @((u:th_ctx S T (0+m))⌈xl⌉) ]
  | // ]
]
qed.

record THEORY_rec (S:SIG) (T:THEORY S) : Type[1] ≝ {
  (* recursion principle *)
  th_tm_rec : ∀P:th_ctx S T 0 → Type[0].∀C:list 𝔸.
      (∀x:𝔸.P (th_par S T x)) → 
      (∀c:sig_idx S.∀d:dom (th_ctx S T) (sig_ar S c).
         bvars_of_dom … d # C → 
         IHs S T P (sig_ar S c) d → 
         P (th_constr S T c (cdom_of_dom … d))) → 
      ∀u. P u
}.