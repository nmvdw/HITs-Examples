Class HitRecursion (H : Type) := {
  indTy : Type;
  recTy : Type;
  H_inductor : indTy;
  H_recursor : recTy
}.

Definition hrecursion (H : Type) {HR : HitRecursion H} : @recTy H HR :=
  @H_recursor H HR.

Definition hinduction (H : Type) {HR : HitRecursion H} : @indTy H HR :=
  @H_inductor H HR.

Ltac hrecursion_ :=
  lazymatch goal with
  | [ |- ?T -> ?P ] => 
    let hrec1 := eval cbv[hrecursion H_recursor] in (hrecursion T) in
    let hrec := eval simpl in hrec1 in
    match type of hrec with
    | ?Q => 
      match (eval simpl in Q) with
      | forall Y, T -> Y =>
        simple refine (hrec P)
      | forall Y _, T -> Y  =>
        simple refine (hrec P _)
      | forall Y _ _, T -> Y =>
        simple refine (hrec P _ _)
      | forall Y _ _ _, T -> Y  =>
        simple refine (hrec P _ _ _)
      | forall Y _ _ _ _, T -> Y  =>
        simple refine (hrec P _ _ _ _)
      | forall Y _ _ _ _ _, T -> Y =>
        simple refine (hrec P _ _ _ _ _)
      | forall Y _ _ _ _ _ _, T -> Y =>
        simple refine (hrec P _ _ _ _ _ _)
      | forall Y _ _ _ _ _ _ _, T -> Y =>
        simple refine (hrec P _ _ _ _ _ _ _)
      | forall Y _ _ _ _ _ _ _ _, T -> Y =>
        simple refine (hrec P _ _ _ _ _ _ _ _)
      | forall Y _ _ _ _ _ _ _ _ _, T -> Y => 
        simple refine (hrec P _ _ _ _ _ _ _ _ _)
      | forall Y _ _ _ _ _ _ _ _ _ _, T -> Y =>
        simple refine (hrec P _ _ _ _ _ _ _ _ _ _) 
      | _ => fail "Cannot handle the recursion principle (too many parameters?) :("
      end
    end
  | [ |- forall (target:?T), ?P] => 
    let hind1 := eval cbv[hinduction H_inductor] in (hinduction T) in
    let hind := eval simpl in hind1 in
    match type of hind with
    | ?Q => 
      match (eval simpl in Q) with
      | forall Y , (forall x, Y x) =>
        simple refine (hind (fun target => P) _)
      | forall Y _, (forall x, Y x)  =>
        simple refine (hind (fun target => P) _)
      | forall Y _ _, (forall x, Y x)  =>
        simple refine (hind (fun target => P) _ _)
      | forall Y _ _ _, (forall x, Y x)  =>       
        simple refine (hind (fun target => P) _ _ _)
      | forall Y _ _ _ _, (forall x, Y x)  =>
        simple refine (hind (fun target => P) _ _ _ _)
      | forall Y _ _ _ _ _, (forall x, Y x)  =>
        simple refine (hind (fun target => P) _ _ _ _ _)
      | forall Y _ _ _ _ _ _, (forall x, Y x)  =>
        simple refine (hind (fun target => P) _ _ _ _ _ _)
      | forall Y _ _ _ _ _ _ _, (forall x, Y x)  =>
        simple refine (hind (fun target => P) _ _ _ _ _ _ _)
      | forall Y _ _ _ _ _ _ _, (forall x, Y x)  =>
        simple refine (hind (fun target => P) _ _ _ _ _ _ _)
      | forall Y _ _ _ _ _ _ _ _, (forall x, Y x)  =>
        simple refine (hind (fun target => P) _ _ _ _ _ _ _ _)
      | forall Y _ _ _ _ _ _ _ _ _, (forall x, Y x)  =>
        simple refine (hind (fun target => P) _ _ _ _ _ _ _ _ _)
      | _ => fail "Cannot handle the induction principle (too many parameters?) :("
     end
    end
  (*| _ => fail "I am sorry, but something went wrong!"*)
  end.

Tactic Notation "hrecursion" := hrecursion_; simpl.
Tactic Notation "hrecursion" ident(x) := revert x; hrecursion.
Tactic Notation "hinduction" := hrecursion_; simpl.
Tactic Notation "hinduction" ident(x) := revert x; hrecursion.

