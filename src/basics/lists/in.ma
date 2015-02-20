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

include "basics/lists/listb.ma".

inductive in_list (A:Type[0]): A → (list A) → Prop ≝
| in_list_head : ∀ x,l.(in_list A x (x::l))
| in_list_cons : ∀ x,y,l.(in_list A x l) → (in_list A x (y::l)).

definition incl : ∀A.(list A) → (list A) → Prop ≝
  λA,l,m.∀x.in_list A x l → in_list A x m.

notation "hvbox(a break ∉ b)" non associative with precedence 45
for @{ 'notmem $a $b }. 
  
interpretation "list member" 'mem x l = (in_list ? x l).
interpretation "list not member" 'notmem x l = (Not (in_list ? x l)).
interpretation "list inclusion" 'subseteq l1 l2 = (incl ? l1 l2).
  
lemma not_in_list_nil : ∀A.∀x:A. x ∉ [].
#A #x % #H1 @(in_list_inv_ind ??? H1)
[ #a0 #al0 #H2 #H3 destruct (H3)
| #a0 #a1 #al0 #H2 #H3 #H4 #H5 destruct (H5)
]
qed.

axiom in_list_cons_case : ∀A,x,a,l.in_list A x (a::l) →
                          x = a ∨ in_list A x l.
(*
#A a0 a1 al0 H1;ninversion H1
##[#a2 al1 H2 H3;ndestruct (H3);@;@
##|#a2 a3 al1 H2 H3 H4 H5;ndestruct (H5);@2;//
##]
nqed.
*)

axiom in_list_tail : ∀A,l,x,y.
      in_list A x (y::l) → x ≠ y → in_list A x l.
(*
#A;#l;#x;#y;#H;#Hneq;
ninversion H;
##[#x1;#l1;#Hx;#Hl;ndestruct;nelim Hneq;#Hfalse;
   nelim (Hfalse ?);@;
##|#x1;#y1;#l1;#H1;#_;#Hx;#Heq;ndestruct;//;
##]
nqed.
*)

axiom in_list_singleton_to_eq : ∀A,x,y.in_list A x [y] → x = y.
(*
#A a0 a1 H1;ncases (in_list_cons_case ???? H1)
##[//
##|#H2;napply False_ind;ncases (not_in_list_nil ? a0);#H3;/2/
##]
nqed.
*)

axiom in_list_to_in_list_append_l: ∀A.∀x:A.
  ∀l1,l2.in_list ? x l1 → in_list ? x (l1@l2).
(*
#A a0 al0 al1 H1;nelim H1
##[#a1 al2;@;
##|#a1 a2 al2 H2 H3;@2;//
##]
nqed.
*)

axiom in_list_to_in_list_append_r: ∀A.∀x:A.
  ∀l1,l2. in_list ? x l2 → in_list ? x (l1@l2).
(*
#A a0 al0 al1 H1;nelim al0
##[napply H1
##|#a1 al2 IH;@2;napply IH
##]
nqed.
*)

axiom in_list_append_to_or_in_list: \forall A:Type[0].\forall x:A.
\forall l,l1. in_list ? x (l@l1) \to in_list ? x l \lor in_list ? x l1.
(*
#A a0 al0;nelim al0
##[#al1 H1;@2;napply H1
##|#a1 al1 IH al2 H1;nnormalize in H1;
   ncases (in_list_cons_case ???? H1);#H2
   ##[@;nrewrite > H2;@
   ##|ncases (IH … H2);#H3
      ##[@;@2;//
      ##|@2;//
      ##]
   ##]
##]
nqed.
*)

axiom memb_true_to_in_list :
  ∀A,x,l.memb A x l = true \to in_list A x l.
(*
#A equ H1 a0 al0;nelim al0
##[nnormalize;#H2;ndestruct (H2)
##|#a1 al1 IH H2;nwhd in H2:(??%?);
   nlapply (refl ? (equ a0 a1));ncases (equ a0 a1) in ⊢ (???% → %);#H3
   ##[nrewrite > (H1 … H3);@
   ##|@2;napply IH;nrewrite > H3 in H2;nnormalize;//;
   ##]
##]
nqed.
*)

axiom in_list_to_memb_true :
  \forall A:DeqSet.∀x,l.in_list A x l \to memb A x l = true.
(*
#A equ H1 a0 al0;nelim al0
##[#H2;napply False_ind;ncases (not_in_list_nil ? a0);/2/
##|#a1 al1 IH H2;nelim H2
   ##[nnormalize;#a2 al2;nrewrite > (H1 …);@
   ##|#a2 a3 al2 H3 H4;nnormalize;ncases (equ a2 a3);nnormalize;//;
   ##]
##]
nqed.
*)

axiom in_list_filter_to_p_true : \forall A,l,x,p.
in_list A x (filter A p l) \to p x = true.
(*
#A al0 a0 p;nelim al0
##[nnormalize;#H1;napply False_ind;ncases (not_in_list_nil ? a0);/2/
##|#a1 al1 IH H1;nnormalize in H1;nlapply (refl ? (p a1));
   ngeneralize in match H1;ncases (p a1) in ⊢ (???% -> ???% → %);
   ##[#H2 H3;ncases (in_list_cons_case ???? H2);#H4
      ##[nrewrite > H4;//
      ##|napply (IH H4);
      ##]
   ##|#H2 H3;napply (IH H2);
   ##]
##]
nqed.
*)

axiom in_list_filter : \forall A,l,p,x.in_list A x (filter A p l) \to in_list A x l.
(*
#A al0 p a0;nelim al0
##[nnormalize;//;
##|#a1 al1 IH H1;nnormalize in H1;
   nlapply (refl ? (p a1));ncases (p a1) in ⊢ (???% → %);#H2
   ##[nrewrite > H2 in H1;#H1;ncases (in_list_cons_case ???? H1);#H3
      ##[nrewrite > H3;@
      ##|@2;napply IH;napply H3
      ##]
   ##|@2;napply IH;nrewrite > H2 in H1;#H1;napply H1;
   ##]
##]
nqed.
*)

axiom in_list_filter_r : \forall A,l,p,x.
              in_list A x l \to p x = true \to in_list A x (filter A p l).
(*
#A al0 p a0;nelim al0
##[#H1;napply False_ind;ncases (not_in_list_nil ? a0);/2/
##|#a1 al1 IH H1 H2;ncases (in_list_cons_case ???? H1);#H3
   ##[nnormalize;nrewrite < H3;nrewrite > H2;@
   ##|nnormalize;ncases (p a1);nnormalize;
      ##[@2;napply IH;//
      ##|napply IH;//
      ##]
   ##]
##]
nqed.
*)
   
axiom incl_A_A: ∀T,A.incl T A A.
(*
#A al0 a0 H1;//;
nqed.
*)

axiom incl_append_l : ∀T,A,B.incl T A (A @ B).
(*
#A al0 al1 a0 H1;/2/;
nqed.
*)

axiom incl_append_r : ∀T,A,B.incl T B (A @ B).
(*
#A al0 al1 a0 H1;/2/;
nqed.
*)

axiom incl_cons : ∀T,A,B,x.incl T A B → incl T (x::A) (x::B).
(*
#A al0 al1 a0 H1 a1 H2;ncases (in_list_cons_case ???? H2);/2/;
#H3;@2;napply H1;//;
nqed.
*)

(*
nlet rec foldl (A,B:Type[0]) (f:A → B → A) (a:A) (l:list B) on l ≝ 
 match l with
 [ nil ⇒ a
 | cons b bl ⇒ foldl A B f (f a b) bl ].

nlet rec foldl2 (A,B,C:Type[0]) (f:A → B → C → A) (a:A) (bl:list B) (cl:list C) on bl ≝ 
 match bl with
 [ nil ⇒ a
 | cons b0 bl0 ⇒ match cl with
   [ nil ⇒ a
   | cons c0 cl0 ⇒ foldl2 A B C f (f a b0 c0) bl0 cl0 ] ].

nlet rec foldr2 (A,B : Type[0]) (X : Type[0]) (f: A → B → X → X) (x:X)
                (al : list A) (bl : list B) on al : X ≝
  match al with
  [ nil ⇒ x
  | cons a al1 ⇒ match bl with
    [ nil ⇒ x
    | cons b bl1 ⇒ f a b (foldr2 ??? f x al1 bl1) ] ].
 
nlet rec rev (A:Type[0]) (l:list A) on l ≝ 
 match l with
 [ nil ⇒ nil A
 | cons hd tl ⇒ (rev A tl)@[hd] ]. 
*)
 
definition coincl : ∀A.list A → list A → Prop ≝  λA,l1,l2.∀x.x ∈ l1 ↔ x ∈ l2.

notation > "hvbox(a break ≡ b)"
  non associative with precedence 45
for @{'equiv $a $b}.

notation < "hvbox(term 46 a break ≡ term 46 b)"
  non associative with precedence 45
for @{'equiv $a $b}.

interpretation "list coinclusion" 'equiv x y = (coincl ? x y).

axiom refl_coincl : ∀A.∀l:list A.l ≡ l.
(*
#;@;#;//;
nqed.
*)

axiom coincl_rev : ∀A.∀l:list A.l ≡ reverse ? l.
(*
#A l x;@;nelim l
##[##1,3:#H;napply False_ind;ncases (not_in_list_nil ? x);
   #H1;napply (H1 H);
##|#a l0 IH H;ncases (in_list_cons_case ???? H);#H1
   ##[napply in_list_to_in_list_append_r;nrewrite > H1;@
   ##|napply in_list_to_in_list_append_l;/2/
   ##]
##|#a l0 IH H;ncases (in_list_append_to_or_in_list ???? H);#H1
   ##[/3/;
   ##|nrewrite > (in_list_singleton_to_eq ??? H1);@
   ##]
##] 
nqed.    
*)

axiom not_in_list_nil_r : ∀A.∀l:list A.l = [] → ∀x.x ∉ l.
(*
#A l;nelim l
##[#;napply not_in_list_nil
##|#a l0 IH Hfalse;ndestruct (Hfalse)
##]
nqed.
*)

axiom map_ind : 
 ∀A,B:Type[0].∀f:A→B.∀P:B → Prop.
  ∀al.(∀a.a ∈ al → P (f a)) → 
  ∀b. b ∈ map ?? f al → P b.
(*
#A B f P al;nelim al
##[#H1 b Hfalse;napply False_ind;
   ncases (not_in_list_nil ? b);#H2;napply H2;napply Hfalse;
##|#a1 al1 IH H1 b Hin;nwhd in Hin:(???%);ncases (in_list_cons_case ???? Hin);
   ##[#e;nrewrite > e;napply H1;@
   ##|#Hin1;napply IH;
      ##[#a2 Hin2;napply H1;@2;//;
      ##|//
      ##]
   ##]
##]
nqed.
*)

axiom incl_incl_to_incl_append : 
  ∀A.∀l1,l2,l1',l2':list A.l1 ⊆ l1' → l2 ⊆ l2' → l1@l2 ⊆ l1'@l2'.
(*
#A al0 al1 al2 al3 H1 H2 a0 H3;
ncases (in_list_append_to_or_in_list ???? H3);#H4;
##[napply in_list_to_in_list_append_l;napply H1;//
##|napply in_list_to_in_list_append_r;napply H2;//
##]
nqed.
*)
  
axiom not_in_list_to_memb_false :
  ∀A:DeqSet.
  ∀x:A.∀l. x ∉ l → memb A x l = false.
(*
#A equ H1 a0 al0;nelim al0
##[#_;@
##|#a1 al1 IH H2;nwhd in ⊢ (??%?);
   nlapply (refl ? (equ a0 a1));ncases (equ a0 a1) in ⊢ (???% → %);#H3;
   ##[napply False_ind;ncases H2;#H4;napply H4;
      nrewrite > (H1 … H3);@
   ##|napply IH;@;#H4;ncases H2;#H5;napply H5;@2;//
   ##]
##]
nqed.
*)

let rec list_forall (A:Type[0]) (l:list A) (p:A → bool) on l : bool ≝ 
 match l with
 [ nil ⇒ (true:bool)
 | cons a al ⇒ p a ∧ list_forall A al p ].

axiom eq_map_f_g :
 ∀A,B,f,g,xl.(∀x.x ∈ xl → f x = g x) → map A B f xl = map A B g xl.
(*
#A B f g xl;nelim xl
##[#;@
##|#a al IH H1;nwhd in ⊢ (??%%);napply eq_f2
   ##[napply H1;@;
   ##|napply IH;#x Hx;napply H1;@2;//
   ##]
##]
nqed.
*)

axiom x_in_map_to_eq :
  ∀A,B,f,x,l.x ∈ map A B f l → ∃x'.x = f x' ∧ x' ∈ l.
(*
#A B f x l;nelim l
##[#H;ncases (not_in_list_nil ? x);#H1;napply False_ind;napply (H1 H)
##|#a l0 IH H;ncases (in_list_cons_case ???? H);#H1
   ##[nrewrite > H1;@ a;@;@
   ##|ncases (IH H1);#a0;*;#H2 H3;@a0;@
      ##[// ##|@2;// ##]
   ##]
##]
nqed.
*)

axiom list_forall_false :
 ∀A:Type[0].∀x,xl,p. p x = false → x ∈ xl → list_forall A xl p = false.
(*
#A x xl p H1;nelim xl
##[#Hfalse;napply False_ind;ncases (not_in_list_nil ? x);#H2;napply (H2 Hfalse)
##|#x0 xl0 IH H2;ncases (in_list_cons_case ???? H2);#H3
   ##[nwhd in ⊢ (??%?);nrewrite < H3;nrewrite > H1;@
   ##|nwhd in ⊢ (??%?);ncases (p x0)
      ##[nrewrite > (IH H3);@
      ##|@
      ##]
   ##]
##]
nqed.
*)

axiom list_forall_true :
 ∀A:Type[0].∀xl,p. (∀x.x ∈ xl → p x = true) → list_forall A xl p = true.
(*
#A xl p;nelim xl
##[#;@
##|#x0 xl0 IH H1;nwhd in ⊢ (??%?);nrewrite > (H1 …)
   ##[napply IH;#x Hx;napply H1;@2;//
   ##|@
   ##]
##]
nqed.
*)
