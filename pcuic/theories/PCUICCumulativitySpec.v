(* Distributed under the terms of the MIT license. *)
From Coq Require Import CRelationClasses.
From Equations.Type Require Import Relation Relation_Properties.
From MetaCoq.Template Require Import config utils BasicAst Reflect.
From MetaCoq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils PCUICEquality
     PCUICLiftSubst PCUICUnivSubst PCUICContextRelation PCUICCases PCUICOnFreeVars.

Set Default Goal Selector "!".

Reserved Notation " Σ ;;; Γ |- t <=s u " (at level 50, Γ, t, u at next level).
Reserved Notation " Σ ;;; Γ |- t =s u " (at level 50, Γ, t, u at next level).

Definition cumul_predicate (cumul : context -> term -> term -> Type) Γ Re p p' :=
  All2 (cumul Γ) p.(pparams) p'.(pparams) *
  (R_universe_instance Re p.(puinst) p'.(puinst) *
  ((eq_context_gen eq eq p.(pcontext) p'.(pcontext)) *
    cumul (Γ ,,, inst_case_predicate_context p) p.(preturn) p'.(preturn))).

(** * Definition of cumulativity and conversion relations *)

Inductive cumulSpec0 (Σ : global_env) (Re Rle : Universe.t -> Universe.t -> Prop) (Γ : context) : term -> term -> Type :=

(* transitivity *)

| cumul_Trans t u v :
    is_closed_context Γ -> is_open_term Γ u -> 
    cumulSpec0 Σ Re Rle Γ t u ->
    cumulSpec0 Σ Re Rle Γ u v ->    
    cumulSpec0 Σ Re Rle Γ t v 

(* symmetry *)

| cumul_Sym t u :
    cumulSpec0 Σ Re Re Γ t u ->
    cumulSpec0 Σ Re Rle Γ u t  

(* reflexivity *)

| cumul_Refl t :
    cumulSpec0 Σ Re Rle Γ t t 

(* Cumulativity rules *)

| cumul_Ind i u u' args args':
    R_global_instance Σ Re Rle (IndRef i) #|args| u u' ->
    All2 (cumulSpec0 Σ Re Re Γ) args args' ->
    cumulSpec0 Σ Re Rle Γ (mkApps (tInd i u) args) (mkApps (tInd i u') args')

| cumul_Construct i k u u' args args':
    R_global_instance Σ Re Rle (ConstructRef i k) #|args| u u' ->
    All2 (cumulSpec0 Σ Re Re Γ) args args' ->
    cumulSpec0 Σ Re Rle Γ (mkApps (tConstruct i k u) args) (mkApps (tConstruct i k u') args')

| cumul_Sort s s' :
    Rle s s' ->
    cumulSpec0 Σ Re Rle Γ (tSort s) (tSort s')

| cumul_Const c u u' :
    R_universe_instance Re u u' ->
    cumulSpec0 Σ Re Rle Γ (tConst c u) (tConst c u')

(* congruence rules *)

| cumul_Evar e args args' :
    All2 (cumulSpec0 Σ Re Re Γ) args args' ->
    cumulSpec0 Σ Re Rle Γ (tEvar e args) (tEvar e args')

| cumul_App t t' u u' :
    cumulSpec0 Σ Re Rle Γ t t' ->
    cumulSpec0 Σ Re Re Γ u u' ->
    cumulSpec0 Σ Re Rle Γ (tApp t u) (tApp t' u')

| cumul_Lambda na na' ty ty' t t' :
    eq_binder_annot na na' ->
    cumulSpec0 Σ Re Re Γ ty ty' ->
    cumulSpec0 Σ Re Rle (Γ ,, vass na ty) t t' ->
    cumulSpec0 Σ Re Rle Γ (tLambda na ty t) (tLambda na' ty' t')

| cumul_Prod na na' a a' b b' :
    eq_binder_annot na na' ->
    cumulSpec0 Σ Re Re Γ a a' ->
    cumulSpec0 Σ Re Rle (Γ ,, vass na a) b b' ->
    cumulSpec0 Σ Re Rle Γ (tProd na a b) (tProd na' a' b')

| cumul_LetIn na na' t t' ty ty' u u' :
    eq_binder_annot na na' ->
    cumulSpec0 Σ Re Re Γ t t' ->
    cumulSpec0 Σ Re Re Γ ty ty' ->
    cumulSpec0 Σ Re Rle (Γ ,, vdef na t ty) u u' ->
    cumulSpec0 Σ Re Rle Γ (tLetIn na t ty u) (tLetIn na' t' ty' u')

| cumul_Case indn p p' c c' brs brs' :
    cumul_predicate (cumulSpec0 Σ Re Re) Γ Re p p' ->
    cumulSpec0 Σ Re Re Γ c c' ->
    All2 (fun br br' =>
      eq_context_gen eq eq (bcontext br) (bcontext br') * 
      cumulSpec0 Σ Re Re (Γ ,,, inst_case_branch_context p br) (bbody br) (bbody br')
    ) brs brs' ->
    cumulSpec0 Σ Re Rle Γ (tCase indn p c brs) (tCase indn p' c' brs')

| cumul_Proj p c c' :
    cumulSpec0 Σ Re Re Γ c c' ->
    cumulSpec0 Σ Re Rle Γ (tProj p c) (tProj p c')

| cumul_Fix mfix mfix' idx :
    All2 (fun x y =>
      cumulSpec0 Σ Re Re Γ x.(dtype) y.(dtype) *
      cumulSpec0 Σ Re Re (Γ ,,, fix_context mfix) x.(dbody) y.(dbody) *
      (x.(rarg) = y.(rarg)) *
      eq_binder_annot x.(dname) y.(dname)
    )%type mfix mfix' ->
    cumulSpec0 Σ Re Rle Γ (tFix mfix idx) (tFix mfix' idx)

| cumul_CoFix mfix mfix' idx :
    All2 (fun x y =>
      cumulSpec0 Σ Re Re Γ x.(dtype) y.(dtype) *
      cumulSpec0 Σ Re Re (Γ ,,, fix_context mfix) x .(dbody) y.(dbody) *
      (x.(rarg) = y.(rarg)) *
      eq_binder_annot x.(dname) y.(dname)
    ) mfix mfix' ->
    cumulSpec0 Σ Re Rle Γ (tCoFix mfix idx) (tCoFix mfix' idx)

(** Reductions *)

(** Beta red *)
| cumul_beta na t b a :
    cumulSpec0 Σ Re Rle Γ (tApp (tLambda na t b) a) (b {0 := a})

(** Let *)
| cumul_zeta na b t b' :
    cumulSpec0 Σ Re Rle Γ (tLetIn na b t b') (b' {0 := b})

| cumul_rel i body :
    option_map decl_body (nth_error Γ i) = Some (Some body) ->
    cumulSpec0 Σ Re Rle Γ (tRel i) (lift0 (S i) body)

(** iota red *)
| cumul_iota ci c u args p brs br :
    nth_error brs c = Some br ->
    #|skipn (ci_npar ci) args| = context_assumptions br.(bcontext) ->
    cumulSpec0 Σ Re Rle Γ (tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs)
                         (iota_red ci.(ci_npar) p args br)

(** Fix unfolding, with guard *)
| cumul_fix mfix idx args narg fn :
    unfold_fix mfix idx = Some (narg, fn) ->
    is_constructor narg args = true ->
    cumulSpec0 Σ Re Rle Γ (mkApps (tFix mfix idx) args)
                         (mkApps fn args)

(** CoFix-case unfolding *)
| cumul_cofix_case ip p mfix idx args narg fn brs :
    unfold_cofix mfix idx = Some (narg, fn) ->
    cumulSpec0 Σ Re Rle Γ (tCase ip p (mkApps (tCoFix mfix idx) args) brs)
                         (tCase ip p (mkApps fn args) brs)

(** CoFix-proj unfolding *)
| cumul_cofix_proj p mfix idx args narg fn :
    unfold_cofix mfix idx = Some (narg, fn) ->
    cumulSpec0 Σ Re Rle Γ (tProj p (mkApps (tCoFix mfix idx) args))
                         (tProj p (mkApps fn args))

(** Constant unfolding *)
| cumul_delta c decl body (isdecl : declared_constant Σ c decl) u :
    decl.(cst_body) = Some body ->
    cumulSpec0 Σ Re Rle Γ (tConst c u) (subst_instance u body)

(** Proj *)
| cumul_proj i pars narg args u arg:
    nth_error args (pars + narg) = Some arg ->
    cumulSpec0 Σ Re Rle Γ (tProj (i, pars, narg) (mkApps (tConstruct i 0 u) args)) arg.

Definition convSpec `{checker_flags} Σ :=
  let φ := (global_ext_constraints Σ) in cumulSpec0 Σ.1 (eq_universe φ) (eq_universe φ).

(* ** Syntactic cumulativity up-to universes *)

Definition cumulSpec `{checker_flags} Σ :=
  let φ := (global_ext_constraints Σ) in cumulSpec0 Σ.1 (eq_universe φ) (leq_universe φ).

Notation " Σ ;;; Γ |- t <=s u " := (@cumulSpec _ Σ Γ t u).
Notation " Σ ;;; Γ |- t =s u " := (@convSpec _ Σ Γ t u).
  
Module PCUICConversionParSpec <: EnvironmentTyping.ConversionParSig PCUICTerm PCUICEnvironment PCUICEnvTyping.
  Definition conv := @convSpec.
  Definition cumul := @cumulSpec.
End PCUICConversionParSpec.

Module PCUICConversionSpec := EnvironmentTyping.Conversion PCUICTerm PCUICEnvironment PCUICEnvTyping PCUICConversionParSpec.
Include PCUICConversionSpec.

Notation conv_context Σ Γ Γ' := (All2_fold (conv_decls Σ) Γ Γ').
Notation cumul_context Σ Γ Γ' := (All2_fold (cumul_decls Σ) Γ Γ').


#[global]
Instance conv_decls_refl {cf:checker_flags} Σ Γ Γ' : Reflexive (conv_decls Σ Γ Γ').
Proof.
  intros x. destruct x as [na [b|] ty]; constructor; auto.
  all:constructor; apply eq_term_refl.
Qed.

#[global]
Instance cumul_decls_refl {cf:checker_flags} Σ Γ Γ' : Reflexive (cumul_decls Σ Γ Γ').
Proof.
  intros x. destruct x as [na [b|] ty]; constructor; auto.
  all:constructor; apply eq_term_refl || apply leq_term_refl.
Qed.

#[global]
Instance cumul_refl' {cf:checker_flags} Σ Γ : Reflexive (cumulSpec Σ Γ).
Proof.
  intro. constructor 3.
Qed.

#[global]
Instance conv_refl' {cf:checker_flags} Σ Γ : Reflexive (convSpec Σ Γ).
Proof.
  intro; constructor 3. 
Qed.

Section ContextConversion.
  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).

  Notation conv_context Γ Γ' := (All2_fold (conv_decls Σ) Γ Γ').
  Notation cumul_context Γ Γ' := (All2_fold (cumul_decls Σ) Γ Γ').

  Global Instance conv_ctx_refl : Reflexive (All2_fold (conv_decls Σ)).
  Proof.
    intro Γ; induction Γ; try econstructor; auto.
    reflexivity.
  Qed.

  Global Instance cumul_ctx_refl : Reflexive (All2_fold (cumul_decls Σ)).
  Proof.
    intro Γ; induction Γ; try econstructor; auto.
    reflexivity. 
  Qed.

  Definition conv_ctx_refl' Γ : conv_context Γ Γ
  := conv_ctx_refl Γ.

  Definition cumul_ctx_refl' Γ : cumul_context Γ Γ
    := cumul_ctx_refl Γ.

End ContextConversion.


Definition cumulSpec0_ctx Σ Re Rle := (OnOne2_local_env (on_one_decl (fun Δ t t' => cumulSpec0 Σ Re Rle Δ t t'))).
Definition cumulSpec0_ctx_rel Σ Re Rle Γ := (OnOne2_local_env (on_one_decl (fun Δ t t' => cumulSpec0 Σ Re Rle (Γ ,,, Δ) t t'))).

Lemma cumulSpec0_ind_all :
  forall (Σ : global_env) (Re : Universe.t -> Universe.t -> Prop)
         (P : (Universe.t -> Universe.t -> Prop) -> context -> term -> term -> Type),

        (* beta *)
       (forall (Rle : Universe.t -> Universe.t -> Prop) (Γ : context) (na : aname) (t b a : term),
        P Rle Γ (tApp (tLambda na t b) a) (b {0 := a})) ->

        (* let *)
       (forall (Rle : Universe.t -> Universe.t -> Prop) (Γ : context) (na : aname) (b t b' : term), P Rle  Γ (tLetIn na b t b') (b' {0 := b})) ->

       (forall (Rle : Universe.t -> Universe.t -> Prop) (Γ : context) (i : nat) (body : term),
        option_map decl_body (nth_error Γ i) = Some (Some body) -> P Rle  Γ (tRel i) ((lift0 (S i)) body)) ->

        (* iota *)
       (forall (Rle : Universe.t -> Universe.t -> Prop) (Γ : context) (ci : case_info) (c : nat) (u : Instance.t) (args : list term)
          (p : predicate term) (brs : list (branch term)) br,
          nth_error brs c = Some br ->
          #|skipn (ci_npar ci) args| = context_assumptions br.(bcontext) ->
          P Rle  Γ (tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs)
              (iota_red ci.(ci_npar) p args br)) ->

        (* fix unfolding *)
       (forall (Rle : Universe.t -> Universe.t -> Prop) (Γ : context) (mfix : mfixpoint term) (idx : nat) (args : list term) (narg : nat) (fn : term),
        unfold_fix mfix idx = Some (narg, fn) ->
        is_constructor narg args = true -> P Rle Γ (mkApps (tFix mfix idx) args) (mkApps fn args)) ->

      (* cofix unfolding *)
       (forall (Rle : Universe.t -> Universe.t -> Prop) (Γ : context) ci (p : predicate term) (mfix : mfixpoint term) (idx : nat)
          (args : list term) (narg : nat) (fn : term) (brs : list (branch term)),
        unfold_cofix mfix idx = Some (narg, fn) ->
        P Rle Γ (tCase ci p (mkApps (tCoFix mfix idx) args) brs) (tCase ci p (mkApps fn args) brs)) ->

       (forall (Rle : Universe.t -> Universe.t -> Prop) (Γ : context) (p : projection) (mfix : mfixpoint term) (idx : nat) (args : list term)
          (narg : nat) (fn : term),
        unfold_cofix mfix idx = Some (narg, fn) -> P Rle Γ (tProj p (mkApps (tCoFix mfix idx) args)) (tProj p (mkApps fn args))) ->

        (* constant unfolding *)
       (forall (Rle : Universe.t -> Universe.t -> Prop) (Γ : context) c (decl : constant_body) (body : term),
        declared_constant Σ c decl ->
        forall u : Instance.t, cst_body decl = Some body -> P Rle Γ (tConst c u) (subst_instance u body)) ->

        (* Proj *)
       (forall (Rle : Universe.t -> Universe.t -> Prop) (Γ : context) (i : inductive) (pars narg : nat) (args : list term) (u : Instance.t)
         (arg : term),
           nth_error args (pars + narg) = Some arg ->
           P Rle  Γ (tProj (i, pars, narg) (mkApps (tConstruct i 0 u) args)) arg) ->

        (* transitivity *)
       (forall (Rle : Universe.t -> Universe.t -> Prop) (Γ : context) (t u v : term),
          is_closed_context Γ -> is_open_term Γ u ->
          cumulSpec0 Σ Re Rle Γ t u -> P Rle Γ t u ->
          cumulSpec0 Σ Re Rle Γ u v -> P Rle Γ u v ->
          P Rle Γ t v) ->

        (* symmetry *)
       (forall (Rle : Universe.t -> Universe.t -> Prop) (Γ : context) (t u : term),
        cumulSpec0 Σ Re Re Γ u t -> P Re Γ u t ->
        P Rle Γ t u) ->

        (* reflexivity *)
        (forall (Rle : Universe.t -> Universe.t -> Prop) (Γ : context) (t : term),
        P Rle Γ t t) ->
        
        (* congruence rules *)

        (forall (Rle : Universe.t -> Universe.t -> Prop) (Γ : context) (ev : nat) (l l' : list term),
          All2 (Trel_conj (cumulSpec0 Σ Re Re Γ) (P Re Γ)) l l' -> P Rle Γ (tEvar ev l) (tEvar ev l')) ->

        (forall (Rle : Universe.t -> Universe.t -> Prop) (Γ : context) (t t' u u' : term), 
          cumulSpec0 Σ Re Rle Γ t t' -> P Rle Γ t t' ->
          cumulSpec0 Σ Re Re Γ u u' -> P Re Γ u u' ->
          P Rle Γ (tApp t u) (tApp t' u')) ->

        (forall (Rle : Universe.t -> Universe.t -> Prop) (Γ : context) (na na' : aname) (ty ty' t t' : term),
          eq_binder_annot na na' ->  
          cumulSpec0 Σ Re Re Γ ty ty' -> P Re Γ ty ty' -> 
          cumulSpec0 Σ Re Rle (Γ ,, vass na ty) t t' -> P Rle (Γ ,, vass na ty) t t' -> 
          P Rle Γ (tLambda na ty t) (tLambda na' ty' t')) ->

        (forall (Rle : Universe.t -> Universe.t -> Prop) (Γ : context) (na na' : binder_annot name) (a a' b b' : term), 
          eq_binder_annot na na' ->
          cumulSpec0 Σ Re Re Γ a a' -> P Re Γ a a' ->
          cumulSpec0 Σ Re Rle (Γ,, vass na a) b b' -> P Rle (Γ,, vass na a) b b' ->
          P Rle Γ (tProd na a b) (tProd na' a' b')) ->

     (forall (Rle : Universe.t -> Universe.t -> Prop) (Γ : context) (na na' : binder_annot name) (t t' ty ty' u u' : term),
        eq_binder_annot na na' ->  cumulSpec0 Σ Re Re Γ t t' -> P Re Γ t t' ->
        cumulSpec0 Σ Re Re Γ ty ty' -> P Re Γ ty ty' ->
        cumulSpec0 Σ Re Rle (Γ,, vdef na t ty) u u' -> P Rle (Γ,, vdef na t ty) u u' ->
        P Rle Γ (tLetIn na t ty u) (tLetIn na' t' ty' u')) ->

      (forall (Rle : Universe.t -> Universe.t -> Prop) (Γ : context) (indn : case_info) (p p' : predicate term)
        (c c' : term) (brs brs' : list (branch term)),
        cumul_predicate (fun Γ t u => cumulSpec0 Σ Re Re Γ t u * P Re Γ t u) Γ Re p p' -> 
        cumulSpec0 Σ Re Re Γ c c' -> P Re Γ c c' ->
        All2
          (Trel_conj (fun br br' : branch term =>
               eq_context_gen eq eq (bcontext br) (bcontext br') *
               cumulSpec0 Σ Re Re (Γ,,, inst_case_branch_context p br)
                 (bbody br) (bbody br')) 
            (fun br br' => P Re (Γ,,, inst_case_branch_context p br) (bbody br) (bbody br'))) brs brs' -> 
       P Rle Γ (tCase indn p c brs) (tCase indn p' c' brs')) ->

       (forall (Rle : Universe.t -> Universe.t -> Prop) (Γ : context) 
          (p : projection) (c c' : term),
        cumulSpec0 Σ Re Re Γ c c' -> P Re Γ c c' ->
         P Rle Γ (tProj p c) (tProj p c')) ->

       (forall (Rle : Universe.t -> Universe.t -> Prop) (Γ : context) 
          (mfix : mfixpoint term) (mfix' : list (def term)) (idx : nat),
          All2
            (fun x y : def term =>
             ((cumulSpec0 Σ Re Re Γ (dtype x) (dtype y) × 
                P Re Γ (dtype x) (dtype y)
               × cumulSpec0 Σ Re Re (Γ,,, fix_context mfix) 
                   (dbody x) (dbody y)) × P Re (Γ,,, fix_context mfix) 
                   (dbody x) (dbody y) × rarg x = rarg y) *
             eq_binder_annot (dname x) (dname y)) mfix mfix' ->
           P Rle Γ (tFix mfix idx) (tFix mfix' idx)) ->

       (forall (Rle : Universe.t -> Universe.t -> Prop) (Γ : context) 
           (mfix : mfixpoint term) (mfix' : list (def term)) (idx : nat),
           All2
             (fun x y : def term =>
              ((cumulSpec0 Σ Re Re Γ (dtype x) (dtype y) × 
                 P Re Γ (dtype x) (dtype y)
                × cumulSpec0 Σ Re Re (Γ,,, fix_context mfix) 
                    (dbody x) (dbody y)) × P Re (Γ,,, fix_context mfix) 
                    (dbody x) (dbody y) × rarg x = rarg y) *
              eq_binder_annot (dname x) (dname y)) mfix mfix' ->
            P Rle Γ (tCoFix mfix idx) (tCoFix mfix' idx)) ->
 
      (* cumulativiity rules *)
      
      (forall (Rle : Universe.t -> Universe.t -> Prop) 
            (Γ : context) (i : inductive) (u u' : list Level.t)
            (args args' : list term), 
      R_global_instance Σ Re Rle (IndRef i) #|args| u u' ->
      All2 (Trel_conj (cumulSpec0 Σ Re Re Γ) (P Re Γ)) args args' ->
      P Rle Γ (mkApps (tInd i u) args) (mkApps (tInd i u') args')) ->

    (forall (Rle : Universe.t -> Universe.t -> Prop) 
      (Γ : context) (i : inductive) (k : nat) 
      (u u' : list Level.t) (args args' : list term), 
      R_global_instance Σ Re Rle (ConstructRef i k) #|args| u u' ->
      All2 (Trel_conj (cumulSpec0 Σ Re Re Γ) (P Re Γ)) args args' ->
      P Rle Γ (mkApps (tConstruct i k u) args)
              (mkApps (tConstruct i k u') args')) ->

      (forall (Rle : Universe.t -> Universe.t -> Prop) 
          (Γ : context) (s s' : Universe.t),
          Rle s s' -> P Rle Γ (tSort s) (tSort s')) ->

      (forall (Rle : Universe.t -> Universe.t -> Prop) 
          (Γ : context) (c : kername) (u u' : list Level.t),
          R_universe_instance Re u u' -> P Rle Γ (tConst c u) (tConst c u') ) ->

       forall (Rle : Universe.t -> Universe.t -> Prop) (Γ : context) (t t0 : term), cumulSpec0 Σ Re Rle Γ t t0 -> P Rle Γ t t0.
Proof.
  intros. rename X24 into Xlast. revert Rle Γ t t0 Xlast.
  fix  aux 4. intros Rle Γ t u.
  move aux at top.
  destruct 1.
  - eapply X8; eauto.
  - eapply X9; eauto.   
  - eapply X10; eauto.   
  - eapply X20; eauto. clear -a aux. induction a; econstructor; eauto.
  - eapply X21; eauto. clear -a aux. induction a; econstructor; eauto.
  - eapply X22; eauto. 
  - eapply X23; eauto. 
  - eapply X11. induction a; econstructor; eauto.
  - eapply X12; eauto.
  - eapply X13; eauto.   
  - eapply X14; eauto.   
  - eapply X15; eauto.   
  - eapply X16 ; eauto. 
    + unfold cumul_predicate in *. destruct c0 as [c0 [cuniv [ccontext creturn]]].
      repeat split ; eauto.
      * induction c0; econstructor; eauto.
    + induction a; econstructor; eauto. intuition.    
  - eapply X17 ; eauto. 
  - eapply X18 ; eauto. 
    set (mfixAbs := mfix). unfold mfixAbs at 3.  
    assert (Habs : mfixAbs = mfix) by reflexivity. clearbody mfixAbs.
     induction a; destruct Habs;  econstructor; eauto; intuition. 
  - eapply X19 ; eauto. 
     set (mfixAbs := mfix). unfold mfixAbs at 3.  
     assert (Habs : mfixAbs = mfix) by reflexivity. clearbody mfixAbs.
      induction a; destruct Habs;  econstructor; eauto; intuition. 
  - eapply X.
  - eapply X0.
  -  eapply X1; eauto. 
  - eapply X2; eauto.
  - eapply X3; eauto.
  - eapply X4; eauto.
  - eapply X5; eauto.
  - eapply X6; eauto.
  - eapply X7; eauto.
Admitted.
      

Lemma convSpec0_ind_all :
  forall (Σ : global_env) (Re : Universe.t -> Universe.t -> Prop)
         (P : context -> term -> term -> Type),

        (* beta *)
       (forall  (Γ : context) (na : aname) (t b a : term),
        P Γ (tApp (tLambda na t b) a) (b {0 := a})) ->

        (* let *)
       (forall  (Γ : context) (na : aname) (b t b' : term), P  Γ (tLetIn na b t b') (b' {0 := b})) ->

       (forall  (Γ : context) (i : nat) (body : term),
        option_map decl_body (nth_error Γ i) = Some (Some body) -> P  Γ (tRel i) ((lift0 (S i)) body)) ->

        (* iota *)
       (forall  (Γ : context) (ci : case_info) (c : nat) (u : Instance.t) (args : list term)
          (p : predicate term) (brs : list (branch term)) br,
          nth_error brs c = Some br ->
          #|skipn (ci_npar ci) args| = context_assumptions br.(bcontext) ->
          P  Γ (tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs)
              (iota_red ci.(ci_npar) p args br)) ->

        (* fix unfolding *)
       (forall  (Γ : context) (mfix : mfixpoint term) (idx : nat) (args : list term) (narg : nat) (fn : term),
        unfold_fix mfix idx = Some (narg, fn) ->
        is_constructor narg args = true -> P Γ (mkApps (tFix mfix idx) args) (mkApps fn args)) ->

      (* cofix unfolding *)
       (forall  (Γ : context) ci (p : predicate term) (mfix : mfixpoint term) (idx : nat)
          (args : list term) (narg : nat) (fn : term) (brs : list (branch term)),
        unfold_cofix mfix idx = Some (narg, fn) ->
        P Γ (tCase ci p (mkApps (tCoFix mfix idx) args) brs) (tCase ci p (mkApps fn args) brs)) ->

       (forall  (Γ : context) (p : projection) (mfix : mfixpoint term) (idx : nat) (args : list term)
          (narg : nat) (fn : term),
        unfold_cofix mfix idx = Some (narg, fn) -> P Γ (tProj p (mkApps (tCoFix mfix idx) args)) (tProj p (mkApps fn args))) ->

        (* constant unfolding *)
       (forall  (Γ : context) c (decl : constant_body) (body : term),
        declared_constant Σ c decl ->
        forall u : Instance.t, cst_body decl = Some body -> P Γ (tConst c u) (subst_instance u body)) ->

        (* Proj *)
       (forall  (Γ : context) (i : inductive) (pars narg : nat) (args : list term) (u : Instance.t)
         (arg : term),
           nth_error args (pars + narg) = Some arg ->
           P  Γ (tProj (i, pars, narg) (mkApps (tConstruct i 0 u) args)) arg) ->

        (* transitivity *)
       (forall  (Γ : context) (t u v : term),
          is_closed_context Γ -> is_open_term Γ u ->
          cumulSpec0 Σ Re Re Γ t u -> P Γ t u ->
          cumulSpec0 Σ Re Re Γ u v -> P Γ u v ->
          P Γ t v) ->

        (* symmetry *)
       (forall  (Γ : context) (t u : term),
        cumulSpec0 Σ Re Re Γ u t -> P Γ u t ->
        P Γ t u) ->

        (* reflexivity *)
        (forall  (Γ : context) (t : term),
        P Γ t t) ->
        
        (* congruence rules *)

        (forall  (Γ : context) (ev : nat) (l l' : list term),
          All2 (Trel_conj (cumulSpec0 Σ Re Re Γ) (P Γ)) l l' -> P Γ (tEvar ev l) (tEvar ev l')) ->

        (forall  (Γ : context) (t t' u u' : term), 
          cumulSpec0 Σ Re Re Γ t t' -> P Γ t t' ->
          cumulSpec0 Σ Re Re Γ u u' -> P Γ u u' ->
          P Γ (tApp t u) (tApp t' u')) ->

        (forall  (Γ : context) (na na' : aname) (ty ty' t t' : term),
          eq_binder_annot na na' ->  
          cumulSpec0 Σ Re Re Γ ty ty' -> P Γ ty ty' -> 
          cumulSpec0 Σ Re Re (Γ ,, vass na ty) t t' -> P (Γ ,, vass na ty) t t' -> 
          P Γ (tLambda na ty t) (tLambda na' ty' t')) ->

        (forall  (Γ : context) (na na' : binder_annot name) (a a' b b' : term), 
          eq_binder_annot na na' ->
          cumulSpec0 Σ Re Re Γ a a' -> P Γ a a' ->
          cumulSpec0 Σ Re Re (Γ,, vass na a) b b' -> P (Γ,, vass na a) b b' ->
          P Γ (tProd na a b) (tProd na' a' b')) ->

     (forall  (Γ : context) (na na' : binder_annot name) (t t' ty ty' u u' : term),
        eq_binder_annot na na' ->  cumulSpec0 Σ Re Re Γ t t' -> P Γ t t' ->
        cumulSpec0 Σ Re Re Γ ty ty' -> P Γ ty ty' ->
        cumulSpec0 Σ Re Re (Γ,, vdef na t ty) u u' -> P (Γ,, vdef na t ty) u u' ->
        P Γ (tLetIn na t ty u) (tLetIn na' t' ty' u')) ->

      (forall  (Γ : context) (indn : case_info) (p p' : predicate term)
        (c c' : term) (brs brs' : list (branch term)),
        cumul_predicate (fun Γ t u => cumulSpec0 Σ Re Re Γ t u * P Γ t u) Γ Re p p' -> 
        cumulSpec0 Σ Re Re Γ c c' -> P Γ c c' ->
        All2
          (Trel_conj (fun br br' : branch term =>
               eq_context_gen eq eq (bcontext br) (bcontext br') *
               cumulSpec0 Σ Re Re (Γ,,, inst_case_branch_context p br)
                 (bbody br) (bbody br')) 
            (fun br br' => P (Γ,,, inst_case_branch_context p br) (bbody br) (bbody br'))) brs brs' -> 
       P Γ (tCase indn p c brs) (tCase indn p' c' brs')) ->

       (forall  (Γ : context) 
          (p : projection) (c c' : term),
        cumulSpec0 Σ Re Re Γ c c' -> P Γ c c' ->
         P Γ (tProj p c) (tProj p c')) ->

       (forall  (Γ : context) 
          (mfix : mfixpoint term) (mfix' : list (def term)) (idx : nat),
          All2
            (fun x y : def term =>
             ((cumulSpec0 Σ Re Re Γ (dtype x) (dtype y) × 
                P Γ (dtype x) (dtype y)
               × cumulSpec0 Σ Re Re (Γ,,, fix_context mfix) 
                   (dbody x) (dbody y)) × P (Γ,,, fix_context mfix) 
                   (dbody x) (dbody y) × rarg x = rarg y) *
             eq_binder_annot (dname x) (dname y)) mfix mfix' ->
           P Γ (tFix mfix idx) (tFix mfix' idx)) ->

       (forall  (Γ : context) 
           (mfix : mfixpoint term) (mfix' : list (def term)) (idx : nat),
           All2
             (fun x y : def term =>
              ((cumulSpec0 Σ Re Re Γ (dtype x) (dtype y) × 
                 P Γ (dtype x) (dtype y)
                × cumulSpec0 Σ Re Re (Γ,,, fix_context mfix) 
                    (dbody x) (dbody y)) × P (Γ,,, fix_context mfix) 
                    (dbody x) (dbody y) × rarg x = rarg y) *
              eq_binder_annot (dname x) (dname y)) mfix mfix' ->
            P Γ (tCoFix mfix idx) (tCoFix mfix' idx)) ->
 
      (* cumulativiity rules *)
      
      (forall  
            (Γ : context) (i : inductive) (u u' : list Level.t)
            (args args' : list term), 
      R_global_instance Σ Re Re (IndRef i) #|args| u u' ->
      All2 (Trel_conj (cumulSpec0 Σ Re Re Γ) (P Γ)) args args' ->
      P Γ (mkApps (tInd i u) args) (mkApps (tInd i u') args')) ->

    (forall  
      (Γ : context) (i : inductive) (k : nat) 
      (u u' : list Level.t) (args args' : list term), 
      R_global_instance Σ Re Re (ConstructRef i k) #|args| u u' ->
      All2 (Trel_conj (cumulSpec0 Σ Re Re Γ) (P Γ)) args args' ->
      P Γ (mkApps (tConstruct i k u) args)
              (mkApps (tConstruct i k u') args')) ->

      (forall  
          (Γ : context) (s s' : Universe.t),
          Re s s' -> P Γ (tSort s) (tSort s')) ->

      (forall  
          (Γ : context) (c : kername) (u u' : list Level.t),
          R_universe_instance Re u u' -> P Γ (tConst c u) (tConst c u') ) ->

       forall  (Γ : context) (t t0 : term), cumulSpec0 Σ Re Re Γ t t0 -> P Γ t t0.
       Proof.
        intros. rename X24 into Xlast. revert Γ t t0 Xlast.
        fix  aux 4. intros Γ t u.
        move aux at top.
        destruct 1.
        - eapply X8; eauto.
        - eapply X9; eauto.   
        - eapply X10; eauto.   
        - eapply X20; eauto. clear -a aux. induction a; econstructor; eauto.
        - eapply X21; eauto. clear -a aux. induction a; econstructor; eauto.
        - eapply X22; eauto. 
        - eapply X23; eauto. 
        - eapply X11. induction a; econstructor; eauto.
        - eapply X12; eauto.
        - eapply X13; eauto.   
        - eapply X14; eauto.   
        - eapply X15; eauto.   
        - eapply X16 ; eauto. 
          + unfold cumul_predicate in *. destruct c0 as [c0 [cuniv [ccontext creturn]]].
            repeat split ; eauto.
            * induction c0; econstructor; eauto.
          + induction a; econstructor; eauto. intuition.    
        - eapply X17 ; eauto. 
        - eapply X18 ; eauto. 
          set (mfixAbs := mfix). unfold mfixAbs at 3.  
          assert (Habs : mfixAbs = mfix) by reflexivity. clearbody mfixAbs.
           induction a; destruct Habs;  econstructor; eauto; intuition. 
        - eapply X19 ; eauto. 
           set (mfixAbs := mfix). unfold mfixAbs at 3.  
           assert (Habs : mfixAbs = mfix) by reflexivity. clearbody mfixAbs.
            induction a; destruct Habs;  econstructor; eauto; intuition. 
        - eapply X.
        - eapply X0.
        -  eapply X1; eauto. 
        - eapply X2; eauto.
        - eapply X3; eauto.
        - eapply X4; eauto.
        - eapply X5; eauto.
        - eapply X6; eauto.
        - eapply X7; eauto.
      Admitted.