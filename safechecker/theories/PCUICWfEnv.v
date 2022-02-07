
(* Distributed under the terms of the MIT license. *)
From Coq Require Import ProofIrrelevance.
From MetaCoq.Template Require Import config utils uGraph.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICReduction
PCUICSafeLemmata PCUICReflect PCUICTyping PCUICGlobalEnv PCUICWfUniverses.
     
From MetaCoq.SafeChecker Require Import PCUICEqualityDec.
(* We pack up all the information required on the global environment and graph in a 
   single record. *)

Lemma wf_gc_of_uctx {cf:checker_flags} {Σ : global_env} (HΣ : ∥ wf Σ ∥)
  : ∑ uctx', gc_of_uctx (global_uctx Σ) = Some uctx'.
Proof.
  assert (consistent (global_uctx Σ).2) as HC. 
  { sq; apply (wf_consistent _ HΣ). }
  unfold gc_of_uctx; simpl in *.
  apply gc_consistent_iff in HC.
  destruct (gc_of_constraints (global_constraints Σ)).
  eexists; reflexivity.
  contradiction HC.
Defined.

Lemma graph_of_wf {cf:checker_flags} {Σ : global_env} (HΣ : ∥ wf Σ ∥)
  : ∑ G, is_graph_of_uctx G (global_uctx Σ).
Proof.
  destruct (wf_gc_of_uctx HΣ) as [uctx Huctx].
  exists (make_graph uctx). unfold is_graph_of_uctx. now rewrite Huctx.
Defined.

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

Class abstract_env_struct {cf:checker_flags} (abstract_env_impl : Type) := {
  abstract_env_lookup : abstract_env_impl -> kername -> option global_decl;
  abstract_env_eq : abstract_env_impl -> Universe.t -> Universe.t -> bool;
  abstract_env_leq : abstract_env_impl -> Universe.t -> Universe.t -> bool;
  abstract_env_compare_global_instance : abstract_env_impl -> (Universe.t -> Universe.t -> bool) -> global_reference -> nat -> list Level.t -> list Level.t -> bool;
  abstract_env_universe : abstract_env_impl -> Universe.t -> bool;
  (* This part of the structure is here to state the correctness properties *)
  abstract_env_rel : abstract_env_impl -> global_env_ext -> Prop;
}.

Class abstract_env_prop {cf:checker_flags} (abstract_env_impl : Type) (X : abstract_env_struct abstract_env_impl) : Prop := {

  abstract_env_exists X : ∥ ∑ Σ , abstract_env_rel X Σ ∥;
  abstract_env_irr {X Σ Σ'} : 
    abstract_env_rel X Σ -> abstract_env_rel X Σ' ->  Σ = Σ';
  abstract_env_wf {X Σ} : abstract_env_rel X Σ -> ∥ wf_ext Σ ∥;
  abstract_env_graph X {Σ} wfΣ: universes_graph := projT1 (graph_of_wf_ext (abstract_env_wf wfΣ)) ;
  abstract_env_graph_wf X {Σ} wfΣ : is_graph_of_uctx (abstract_env_graph X wfΣ) (global_ext_uctx Σ)
    := projT2 (graph_of_wf_ext (abstract_env_wf wfΣ));
  abstract_env_lookup_correct X {Σ} c : abstract_env_rel X Σ -> 
    lookup_env Σ c = abstract_env_lookup X c ;
  abstract_env_eq_correct X {Σ} (wfΣ : abstract_env_rel X Σ) : check_eqb_universe (abstract_env_graph X wfΣ) = abstract_env_eq X;
  abstract_env_leq_correct X {Σ} (wfΣ : abstract_env_rel X Σ) : check_leqb_universe (abstract_env_graph X wfΣ) = abstract_env_leq X;
  abstract_env_compare_global_instance_correct X {Σ} (wfΣ : abstract_env_rel X Σ) : 
    compare_global_instance Σ (check_eqb_universe (abstract_env_graph X wfΣ)) = 
    abstract_env_compare_global_instance X;
  abstract_env_universe_correct X {Σ} (wfΣ : abstract_env_rel X Σ) u : wf_universeb Σ u = abstract_env_universe X u;
   }.



Definition abstract_env_impl {cf:checker_flags} := ∑ X Y, abstract_env_prop X Y. 

Global Instance abstract_env_impl_abstract_env_struct {cf:checker_flags} (Σ : abstract_env_impl) : abstract_env_struct Σ.π1.
  exact (Σ.π2.π1).
Defined. 

Global Instance abstract_env_impl_abstract_env_prop {cf:checker_flags} (Σ : abstract_env_impl) : abstract_env_prop Σ.π1 _.
  exact (Σ.π2.π2).
Defined. 

Definition abstract_env_cored {cf:checker_flags} (_X : abstract_env_impl) (X : _X.π1) {Σ Σ' Γ u v} : abstract_env_rel X Σ -> abstract_env_rel X Σ' 
-> cored Σ Γ u v -> cored Σ' Γ u v.
Proof.
  intros HΣ HΣ' Hred. erewrite abstract_env_irr; eauto.
Defined.           

Definition abstract_env_ext_sq_wf {cf:checker_flags} (X : abstract_env_impl) (x : X.π1) 
  Σ (wfΣ : abstract_env_rel x Σ) : ∥ wf Σ∥.
  destruct (abstract_env_wf wfΣ).
  sq. auto. 
Qed.

Record abstract_env_ext {cf:checker_flags} := { 
      abstract_env_ext_env :> global_env_ext;
      abstract_env_ext_wf :> ∥ wf_ext abstract_env_ext_env ∥;
      abstract_env_ext_graph := projT1 (graph_of_wf_ext abstract_env_ext_wf);
      abstract_env_ext_graph_wf := projT2 (graph_of_wf_ext abstract_env_ext_wf)
  }.

Program Definition canonincal_abstract_env_struct {cf:checker_flags} : 
  abstract_env_struct abstract_env_ext :=
  {| abstract_env_lookup := fun Σ => lookup_env (abstract_env_ext_env Σ) ;
     abstract_env_eq := fun Σ => check_eqb_universe (abstract_env_ext_graph Σ);
     abstract_env_leq := fun Σ => check_leqb_universe (abstract_env_ext_graph Σ) ;
     abstract_env_compare_global_instance := fun Σ => 
      compare_global_instance (abstract_env_ext_env Σ) 
                              (check_eqb_universe (abstract_env_ext_graph Σ));
     abstract_env_universe := fun Σ => wf_universeb (abstract_env_ext_env Σ);


     abstract_env_rel := fun X Σ => Σ = abstract_env_ext_env X;
  |}.

Program Definition canonincal_abstract_env_prop {cf:checker_flags} :
  abstract_env_prop _ canonincal_abstract_env_struct := 
     {| abstract_env_exists := fun Σ => sq (abstract_env_ext_env Σ ; eq_refl); |}.
Next Obligation. apply abstract_env_ext_wf. Defined. 

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