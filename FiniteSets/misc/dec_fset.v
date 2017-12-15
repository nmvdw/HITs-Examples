Require Import HoTT HitTactics.
Require Export FSets lattice_examples k_finite.

Section quantifiers.
  Context {A : Type} `{Univalence}.
  Variable (P : A -> hProp).
 
  Definition all : FSet A -> hProp.
  Proof.
    hinduction.
    - apply Unit_hp.
    - apply P.
    - intros X Y.
      apply (BuildhProp (X * Y)).
    - eauto with lattice_hints typeclass_instances.
    (* TODO eauto hints *)
      apply associativity.
    - eauto with lattice_hints typeclass_instances.
      apply commutativity.
    - intros.
      apply path_trunctype ; apply prod_unit_l.
    - intros.
      apply path_trunctype ; apply prod_unit_r.
    - eauto with lattice_hints typeclass_instances.
      intros. apply binary_idempotent.
  Defined.

  Lemma all_intro X : forall (HX : forall x, x ∈ X -> P x), all X.
  Proof.
    hinduction X ; try (intros ; apply path_ishprop).
    - intros.
      apply tt.
    - intros.
      apply (HX a (tr idpath)).
    - intros X1 X2 HX1 HX2 Hmem.
      split.
      * apply HX1.
        intros a Ha.
        refine (Hmem a (tr _)).
        apply (inl Ha).
      * apply HX2.
        intros a Ha.
        refine (Hmem a (tr _)).
        apply (inr Ha).
  Defined.

  Lemma all_elim X a : all X -> (a ∈ X) -> P a.
  Proof.
    hinduction X ; try (intros ; apply path_ishprop).
    - contradiction.
    - intros b Hmem Heq.
      strip_truncations.
      rewrite Heq.
      apply Hmem.
    - intros X1 X2 HX1 HX2 [Hall1 Hall2] Hmem.
      strip_truncations.
      destruct Hmem as [t | t].
      * apply (HX1 Hall1 t).
      * apply (HX2 Hall2 t). 
  Defined.      

  Definition exist : FSet A -> hProp.
  Proof.
    hinduction.
    - apply False_hp.
    - apply P.
    - apply (⊔).
    - eauto with lattice_hints typeclass_instances.
    (* TODO eauto with .. *)
      apply associativity.
    - eauto with lattice_hints typeclass_instances.
      apply commutativity.
    - eauto with lattice_hints typeclass_instances.
      apply left_identity.
    - eauto with lattice_hints typeclass_instances. 
      apply right_identity.
    - eauto with lattice_hints typeclass_instances.
      intros. apply binary_idempotent.
  Defined.

  Lemma exist_intro X a : a ∈ X -> P a -> exist X.
  Proof.
    hinduction X ; try (intros ; apply path_ishprop).
    - contradiction.
    - intros b Hin Pb.
      strip_truncations.
      rewrite <- Hin.
      apply Pb.
    - intros X1 X2 HX1 HX2 Hin Pa.
      strip_truncations.
      apply tr.
      destruct Hin as [t | t].
      * apply (inl (HX1 t Pa)).
      * apply (inr (HX2 t Pa)).
  Defined.

  Lemma exist_elim X : exist X -> hexists (fun a => a ∈ X * P a)%type.
  Proof.
    hinduction X ; try (intros ; apply path_ishprop).
    - contradiction.
    - intros a Pa.
      apply (tr(a;(tr idpath,Pa))).
    - intros X1 X2 HX1 HX2 Hex.
      strip_truncations.
      destruct Hex.
      * specialize (HX1 t).
        strip_truncations.
        destruct HX1 as [a [Hin Pa]].
        refine (tr(a;(_,Pa))).
        apply (tr(inl Hin)).
      * specialize (HX2 t).
        strip_truncations.
        destruct HX2 as [a [Hin Pa]].
        refine (tr(a;(_,Pa))).
        apply (tr(inr Hin)).
  Defined.  

  Context `{forall a, Decidable (P a)}.

  Global Instance all_decidable : (forall X, Decidable (all X)).
  Proof.
    hinduction ; try (apply _) ; try (intros ; apply path_ishprop).
  Defined.

  Global Instance exist_decidable : (forall X, Decidable (exist X)).
  Proof.
    hinduction ; try (apply _) ; try (intros ; apply path_ishprop).
  Defined.
End quantifiers.

Section exists_isIn.
  Context {A : Type} `{Univalence}.

  Theorem exist_isIn (a : A) (X : FSet A)
    : a ∈ X = exist (fun b => BuildhProp(Trunc (-1) (a = b))) X.
  Proof.
    hinduction X ; try (intros ; apply path_ishprop) ; cbn ; try reflexivity.
  Defined.
End exists_isIn.  

Section simple_example.
  Context `{Univalence}.

  Definition P : nat -> hProp := fun n => BuildhProp(n = n).
  Definition X : FSet nat := {|0%nat|} ∪ {|1%nat|}.

  Definition simple_example : all P X.
  Proof.
    refine (from_squash (all P X)).
    compute.
    apply tt.
  Defined.
End simple_example.

Section pauli.
  Context `{Univalence}.

  Inductive Pauli : Type :=
  | XP : Pauli
  | YP : Pauli
  | ZP : Pauli
  | IP : Pauli.

  Definition Pauli_mult (x y : Pauli) : Pauli :=
    match x, y with
    | XP, XP => IP
    | XP, YP => ZP
    | XP, ZP => YP
    | YP, XP => ZP
    | YP, YP => IP
    | YP, ZP => XP
    | ZP, XP => YP
    | ZP, YP => XP
    | ZP, ZP => IP
    | IP, x => x
    | x, IP => x
    end.

  Definition not_XP (x : Pauli) :=
    match x with
    | XP => Empty
    | x => Unit
    end.

  Definition not_YP (x : Pauli) :=
    match x with
    | YP => Empty
    | x => Unit
    end.

  Definition not_ZP (x : Pauli) :=
    match x with
    | ZP => Empty
    | x => Unit
    end.

  Definition not_IP (x : Pauli) :=
    match x with
    | IP => Empty
    | x => Unit
    end.
  
  Global Instance decidable_eq_pauli : DecidablePaths Pauli.
  Proof.
    intros [ | | |] [ | | | ] ; try (apply (inl idpath)) ; try (refine (inr (fun p => _)))
    ; (refine (transport not_XP p tt) || refine (transport not_YP p tt)
    || refine (transport not_ZP p tt) || refine (transport not_IP p tt)).
  Defined.

  Global Instance Pauli_set : IsHSet Pauli.
  Proof.
    apply _.
  Defined.  

  Definition Pauli_list : FSet Pauli := {|XP|} ∪ {|YP|} ∪ {|ZP|} ∪ {|IP|}.
  
  Ltac solve_in_list :=
    apply tr; try apply idpath;
    first [ apply inl ; solve_in_list | apply inr ; solve_in_list ].

  Theorem Pauli_finite : Kf Pauli.
  Proof.
    apply Kf_unfold.
    exists Pauli_list.
    unfold map.
    intros [ | | | ]; rewrite !union_isIn; solve_in_list.
  Defined.

  Theorem Pauli_all (P : Pauli -> hProp) : all P Pauli_list -> forall (x : Pauli), P x.
  Proof.
    intros HP x.
    refine (all_elim P Pauli_list x HP _).
    destruct x ; rewrite ?union_isIn; solve_in_list.
  Defined.

  Definition pauli_comm x y : hProp := BuildhProp(Pauli_mult x y = Pauli_mult y x).

  Theorem Pauli_mult_comm : all (fun x => all (fun y => pauli_comm x y) Pauli_list) Pauli_list.
  Proof.
    refine (from_squash (all _ _)).
    compute.
    apply tt.
  Defined.

  Definition pauli_id x y : hProp := BuildhProp(Pauli_mult x y = y).

  Theorem Pauli_mult_id : exist (fun x => all (fun y => pauli_id x y) Pauli_list) Pauli_list.
  Proof.
    refine (from_squash (exist _ _)).
    compute.
    apply tt.
  Defined.
End pauli.  
