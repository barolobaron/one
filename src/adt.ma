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

(* we decided to put the recursion principle in a different record:
   the definitions in the THEORY record are sufficient to write more definitions
   for operations that will be used in the recursion principle
 *)

(* the domain of a constructor with the given arity (expressed as a list of ℕ) *)
inductive dom (T:ℕ → Type[0]) : list ℕ → Type[0] ≝ 
| dom_nil  : dom T [ ] 
| dom_cons : ∀m,nl. Vector 𝔸 m → T m → dom T nl → dom T (m::nl).

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



record THEORY_rec (S:SIG) (T:THEORY S) ≝ {
  (* recursion principle *)
  th_tm_rec : ∀P:th_ctx S T 0 → Type[0].∀C.
      (∀x:𝔸.P (th_par S T x)) → 
      (∀c:sig_idx S.∀d:dom (th_ctx S T) (sig_ar S c). (* something about C-freshness *)
         IHs S T P (sig_ar S c) d → 
         P (th_constr c d*)) → 
      ∀u. P u;
      
  (* to be updated  
    stt_typing : list (𝔸 × tp) → stt_ctx 0 → tp → Prop *)

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

(* REN is more notation for renaming, with a specific computational behaviour *)
definition REN ≝ λS.λu:stt_tm S.λp.let 〈x,y〉 ≝ p in ((νx.u)⌈y⌉).
let rec REN_list S (u:stt_tm S) pl on pl ≝ match pl with
 [ nil ⇒ u
 | cons p0 pl0 ⇒ REN_list S (REN S u p0) pl0 ].
lemma REN_def : ∀S,u,x,y.REN S u 〈x,y〉 = ((νx.u)⌈y⌉). // qed.

(* term notation *)
notation < "\PAR \nbsp term 90 x" with precedence 69 for @{'parm $x}.
notation > "\PAR" with precedence 90 for @{'parm0}.
notation < "\APP \nbsp term 90 u \nbsp term 90 v" with precedence 69 for @{'app $u $v}.
notation > "\APP" with precedence 90 for @{'app0}.
notation < "\LAM \nbsp term 90 x \nbsp term 90 s \nbsp term 90 u" with precedence 69 
  for @{'lam $x $s $u}.
notation > "\LAM" with precedence 90 for @{'lam0}.
interpretation "STT param" 'parm x = (stt_par ? x).
interpretation "STT param" 'parm0 = (stt_par ?).
interpretation "STT app" 'app x y = (stt_app ? x y).
interpretation "STT app" 'app0 = (stt_app ?).
interpretation "STT lam" 'lam x s u = (stt_lam ? x s u).
interpretation "STT lam" 'lam0 = (stt_lam ?).

(* permutation notation *)
interpretation "single renaming" 'times u p = (REN ? u p).
interpretation "multiple renaming" 'times u pl = (REN_list ? u pl).

(* free variables notation *)
notation < "\FV \nbsp term 90 u" with precedence 69 for @{'fv $u}.
notation > "\FV" with precedence 90 for @{'fv0}.
interpretation "STT fv" 'fv u = (stt_FV ?? u).
interpretation "STT fv" 'fv0 = (stt_FV ??).

(* recursion principle notation 

alas Matita doesn't seem to like it (termContentPres line 358 assertion failed)

notation < "\Rec \nbsp term 90 P \nbsp term 90 C \nbsp 
              term 90 Hpar \nbsp term 90 Happ \nbsp term 90 Hlam \nbsp term 90 u" 
         with precedence 69 for @{'Rec $P $C $HPar $Happ $Hlam $u}.
notation > "\Rec" with precedence 90 for @{'Rec0}.
interpretation "STT recursor" 'Rec P C Hpar Happ Hlam u = (stt_tm_rec ? P C Hpar Happ Hlam u).
interpretation "STT recursor" 'Rec0 = (stt_tm_rec ?).

*)

notation "G ⊪ u : s" with precedence 45 for @{'Vvdash $G $u $s}.
interpretation "STT typing" 'Vvdash G u s = (stt_typing ? G u s).


record STT : Type[1] ≝ {

  (* operations: they are partitioned in a different structure for practical
     purposes (e.g. defining notation separately) *)
  stt_sig :> STT_sig;
  
  stt_ren_par_eq     : ∀x,y.REN stt_sig (\PAR x) 〈x,y〉 = \PAR y;
  stt_ren_par_not_eq : ∀x,y,z.z ≠ x → REN stt_sig (\PAR z) 〈x,y〉 = \PAR z;
  stt_ren_app        : ∀x,y.∀u,v:stt_tm stt_sig.
                         (\APP u v)*〈x,y〉 = \APP (u*〈x,y〉) (v*〈x,y〉);
  stt_ren_lam        : ∀x,y,z,s.∀u:stt_tm stt_sig.
                         z ≠ x → z ≠ y → (\LAM z s u)*〈x,y〉 = \LAM z s (u*〈x,y〉);

  (* FV properties *)
  stt_fv_par   : ∀x.stt_FV stt_sig ? (\PAR x) = [x];
  stt_fv_app   : ∀u,v:stt_tm stt_sig. \FV (\APP u v) = \FV u @ \FV v;
  stt_fv_lam   : ∀x,s.∀u:stt_tm stt_sig. \FV (\LAM x s u) = \FV (\nu x.u);
  stt_fv_nu    : ∀k,x,y.∀u:stt_ctx stt_sig k. x ∈ \FV (νy.u) ↔ (x ≠ y ∧ x ∈ \FV u);
  stt_fv_open1 : ∀k,x.∀u:stt_ctx stt_sig (S k). \FV (u⌈x⌉) ⊆ x::(\FV u);
  stt_fv_open2 : ∀k,x.∀u:stt_ctx stt_sig (S k). \FV u ⊆ \FV (u⌈x⌉);
  
  (* alpha equivalence *)
  stt_tm_alpha : ∀x,y,s.∀u:stt_ctx stt_sig 1.x ∉ \FV u → y ∉ \FV u →
                   \LAM x s (u⌈x⌉) = \LAM y s (u⌈y⌉); 
                 
  (* ctx properties *)
  stt_open_nu : ∀k,x.∀u:stt_ctx stt_sig k.    (νx.u)⌈x⌉ = u;
  stt_ctx_eta : ∀k,x.∀u:stt_ctx stt_sig (S k). x ∉ \FV u → (νx.(u⌈x⌉)) = u;
  
  (* commutation properties *)
  stt_tm_rec_par : ∀P,x,C,Hpar,Happ,Hlam. 
      stt_tm_rec stt_sig P C Hpar Happ Hlam (\PAR x) = Hpar x;
  stt_tm_rec_app : ∀P,u,v,C,Hpar,Happ,Hlam. 
      stt_tm_rec stt_sig P C Hpar Happ Hlam (\APP u v) =
      Happ u v (stt_tm_rec stt_sig P C Hpar Happ Hlam u) (stt_tm_rec stt_sig P C Hpar Happ Hlam v);
  stt_tm_rec_lam : ∀Q.∀P:∀v.Q v → Type[0].
      ∀x,s.∀u:stt_ctx stt_sig 1.∀C,Hpar,Happ.
      ∀Hlam:∀x0:𝔸.∀s0.∀v:stt_ctx stt_sig 1.x0∉ \FV v→x0∉C→Q (v⌈x0⌉)→Q (\LAM x0 s0 (v⌈x0⌉)).
      x ∉ \FV u → 
      (∀x0,px0,pC.
       P ? (Hlam x0 s u px0 pC (stt_tm_rec stt_sig Q C Hpar Happ Hlam (u⌈x0⌉)))) → 
      P ? (stt_tm_rec stt_sig Q C Hpar Happ Hlam (\LAM x s (u⌈x⌉)));
      
  (* intro rules for typing *)
  stt_t_par : ∀G,x,s.valid (dom G) → 〈x,s〉 ∈ G → stt_typing stt_sig G (\PAR x) s;
  stt_t_app : ∀G.∀u,v:stt_tm stt_sig.∀s,t. G ⊪ u : arr s t → G ⊪ v : s → G ⊪ \APP u v : t;
  stt_t_lam : ∀G,x,s.∀u:stt_tm stt_sig.∀t.〈x,s〉::G ⊪ u : t → G ⊪ \LAM x s u : arr s t;
  
  (* (ostensibly named) induction on typing *)
  stt_t_ind : ∀P:list (𝔸 × tp) → stt_tm stt_sig → tp → Prop.
      (∀G,x,s.valid (dom G) → 〈x,s〉 ∈ G → P G (\PAR x) s) → 
      (∀G,s,t,u,v.G ⊪ u : arr s t → G ⊪ v : s → 
          P G u (arr s t) → P G v s → P G (\APP u v) t) → 
      (∀G,x,s.∀u:stt_ctx stt_sig 1.∀t. x ∉ \FV u → x ∉ dom G → 
        (∀y.y ∉ \FV u → y ∉ dom G → 〈y,s〉::G ⊪  (u⌈y⌉) : t) → 
        (∀y.y ∉ \FV u → y ∉ dom G → P (〈y,s〉::G) (u⌈y⌉) t) → 
        P G (\LAM x s (u⌈x⌉)) (arr s t)) → 
      ∀G,u,t.G ⊪ u : t → P G u t
}.