(* Properties of the operations on [FSetC A] *)
Require Import HoTT HitTactics.
Require Import representations.cons_repr.
From fsets Require Import operations_cons_repr.

Section properties.
  Context {A : Type}.

  Lemma append_nl: 
    forall (x: FSetC A), append ∅ x = x. 
  Proof.
    intro. reflexivity.
  Defined.

  Lemma append_nr: 
    forall (x: FSetC A), append x ∅ = x.
  Proof.
    hinduction; try (intros; apply set_path2).
    -  reflexivity.
    -  intros. apply (ap (fun y => a ;; y) X).
  Defined.
  
  Lemma append_assoc {H: Funext}:  
    forall (x y z: FSetC A), append x (append y z) = append (append x y) z.
  Proof.
    intro x; hinduction x; try (intros; apply set_path2).
    - reflexivity.
    - intros a x HR y z. 
      specialize (HR y z).
      apply (ap (fun y => a ;; y) HR). 
    - intros. apply path_forall. 
      intro. apply path_forall. 
      intro. apply set_path2.
    - intros. apply path_forall.
      intro. apply path_forall. 
      intro. apply set_path2.
  Defined.
  
  Lemma append_singleton: forall (a: A) (x: FSetC A), 
      a ;; x = append x (a ;; ∅).
  Proof.
    intro a. hinduction; try (intros; apply set_path2).
    - reflexivity.
    - intros b x HR. refine (_ @ _).
      + apply comm.
      + apply (ap (fun y => b ;; y) HR).
  Defined.

  Lemma append_comm {H: Funext}: 
    forall (x1 x2: FSetC A), append x1 x2 = append x2 x1.
  Proof.
    intro x1. 
    hinduction x1;  try (intros; apply set_path2).
    - intros. symmetry. apply append_nr. 
    - intros a x1 HR x2.
      etransitivity.
      apply (ap (fun y => a;;y) (HR x2)).  
      transitivity  (append (append x2 x1) (a;;∅)).
      + apply append_singleton. 
      + etransitivity.
    	* symmetry. apply append_assoc.
    	* simple refine (ap (fun y => append x2 y) (append_singleton _ _)^).
    - intros. apply path_forall.
      intro. apply set_path2.
    - intros. apply path_forall.
      intro. apply set_path2.  
  Defined.

  Lemma singleton_idem: forall (a: A), 
      append (singleton a) (singleton a) = singleton a.
  Proof.
    unfold singleton. intro. cbn. apply dupl.
  Defined.

End properties.
