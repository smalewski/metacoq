
(* Distributed under the terms of the MIT license. *)
From Coq Require Import ProofIrrelevance.
From MetaCoq.Template Require Import config utils uGraph.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICReflect PCUICTyping PCUICGlobalEnv.
     
From MetaCoq.SafeChecker Require Import PCUICEqualityDec.
(* We pack up all the information required on the global environment and graph in a 
   single record. *)

Class wf_env_struct {cf:checker_flags} (wf_env_impl : Type) := {
  wf_env_lookup : wf_env_impl -> kername -> option global_decl;
  wf_env_eq : wf_env_impl -> Universe.t -> Universe.t -> bool;
  wf_env_leq : wf_env_impl -> Universe.t -> Universe.t -> bool;
  wf_env_compare_global_instance : wf_env_impl -> (Universe.t -> Universe.t -> bool) -> global_reference -> nat -> list Level.t -> list Level.t -> bool;
  (* This part of the structure is here to state the correctness properties *)
  wf_env_env : wf_env_impl -> global_env_ext ;
  wf_env_graph : wf_env_impl -> universes_graph;
}.

Class wf_env_prop {cf:checker_flags} (wf_env_impl : Type) (X : wf_env_struct wf_env_impl) : Prop := {
  wf_env_wf X : ∥ wf_ext (wf_env_env X) ∥;
  wf_env_lookup_correct X c : 
    lookup_env (wf_env_env X) c = wf_env_lookup X c ;
  wf_env_eq_correct X : check_eqb_universe (wf_env_graph X) = wf_env_eq X;
  wf_env_leq_correct X : check_leqb_universe (wf_env_graph X) = wf_env_leq X;
  wf_env_compare_global_instance_correct X : 
    compare_global_instance (wf_env_env X) (check_eqb_universe (wf_env_graph X)) = 
    wf_env_compare_global_instance X;
  wf_env_graph_wf X : 
      is_graph_of_uctx (wf_env_graph X) (global_ext_uctx (wf_env_env X))
   }.

Definition wf_env_impl {cf:checker_flags} := ∑ X Y, wf_env_prop X Y. 

Global Instance wf_env_impl_wf_env_struct {cf:checker_flags} (Σ : wf_env_impl) : wf_env_struct Σ.π1.
  exact (Σ.π2.π1).
Defined. 

Global Instance wf_env_impl_wf_env_prop {cf:checker_flags} (Σ : wf_env_impl) : wf_env_prop Σ.π1 _.
  exact (Σ.π2.π2).
Defined. 

Definition wf_env_ext_sq_wf {cf:checker_flags} (Σ : wf_env_impl) (x : Σ.π1) : ∥ wf (wf_env_env x) ∥.
  destruct (wf_env_wf x).
  sq. auto. 
Qed.

Lemma wf_ext_gc_of_uctx {cf:checker_flags} {Σ : global_env_ext} (HΣ : ∥ wf_ext Σ ∥)
  : ∑ uctx', gc_of_uctx (global_ext_uctx Σ) = Some uctx'.
Proof.
  assert (consistent (global_ext_uctx Σ).2) as HC.
  { sq; apply (global_ext_uctx_consistent _ HΣ). }
  destruct Σ as [Σ φ].
  simpl in HC.
  unfold gc_of_uctx; simpl in *.
  apply gc_consistent_iff in HC.
  destruct (gc_of_constraints (global_ext_constraints (Σ, φ))).
  eexists; reflexivity.
  contradiction HC.
Defined.

Lemma graph_of_wf_ext {cf:checker_flags} {Σ : global_env_ext} (HΣ : ∥ wf_ext Σ ∥)
  : ∑ G, is_graph_of_uctx G (global_ext_uctx Σ).
Proof.
  destruct (wf_ext_gc_of_uctx HΣ) as [uctx Huctx].
  exists (make_graph uctx). unfold is_graph_of_uctx. now rewrite Huctx.
Defined.

Section GraphSpec.
  Context {cf:checker_flags} {Σ : global_env_ext} (HΣ : ∥ wf Σ ∥)
      (Hφ : ∥ on_udecl Σ.1 Σ.2 ∥)
      (G : universes_graph) (HG : is_graph_of_uctx G (global_ext_uctx Σ)).

  Local Definition HΣ' : ∥ wf_ext Σ ∥.
  Proof.
    destruct HΣ, Hφ; now constructor.
  Defined.
    
  Lemma check_constraints_spec ctrs
    : check_constraints G ctrs -> valid_constraints (global_ext_constraints Σ) ctrs.
  Proof.
    pose proof HΣ'.
    intros HH.
    refine (check_constraints_spec G (global_ext_uctx Σ) _ _ HG _ HH).
    sq; now eapply wf_ext_global_uctx_invariants.
    sq; now eapply global_ext_uctx_consistent.
  Qed.

  Lemma is_graph_of_uctx_levels (l : Level.t) :
    LevelSet.mem l (uGraph.wGraph.V G) <->
    LevelSet.mem l (global_ext_levels Σ).
  Proof.
    unfold is_graph_of_uctx in HG.
    case_eq (gc_of_uctx (global_ext_uctx Σ)); [intros [lvs cts] XX|intro XX];
      rewrite -> XX in *; simpl in *; [|contradiction].
    unfold gc_of_uctx in XX; simpl in XX.
    destruct (gc_of_constraints Σ); [|discriminate].
    inversion XX; subst. generalize (global_ext_levels Σ); intros lvs; cbn.
    reflexivity.
  Qed.

End GraphSpec.