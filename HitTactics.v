Module HitRec.
Record class (H : Type) (* The HIT type itself *)
             (recTy : H -> Type) (* The type of the recursion principle *)
             := Class { recursion_term : forall (x : H), recTy x }.
Structure type := Pack { obj : Type ; rec : obj -> Type ; class_of : class obj rec }.
Definition hrecursion (e : type) : forall x, rec e x :=
  let 'Pack _ _ (Class r) := e
  in r.
Arguments hrecursion {e} x : simpl never.
Arguments Class H {recTy} recursion_term.
End HitRec.

Ltac hrecursion_ target :=
  generalize dependent target;
  match goal with
  | [ |- forall target, ?P] => intro target;
    match type of (HitRec.hrecursion target) with
    | ?Q => 
      match (eval simpl in Q) with
      | forall Y , Y target =>
        simple refine (HitRec.hrecursion target (fun target => P) _)
      | forall Y _, Y target  =>
        simple refine (HitRec.hrecursion target (fun target => P) _)
      | forall Y _ _, Y target  =>
        simple refine (HitRec.hrecursion target (fun target => P) _ _)
      | forall Y _ _ _, Y target  =>
        let hrec:=(eval hnf in (HitRec.hrecursion target)) in
        simple refine (hrec (fun target => P) _ _ _)
      | forall Y _ _ _ _, Y target  =>
        simple refine (HitRec.hrecursion target (fun target => P) _ _ _ _)
      | forall Y _ _ _ _ _, Y target  =>
        simple refine (HitRec.hrecursion target (fun target => P) _ _ _ _ _)
      | forall Y _ _ _ _ _ _, Y target  =>
        simple refine (HitRec.hrecursion target (fun target => P) _ _ _ _ _ _)
      | forall Y _ _ _ _ _ _ _, Y target  =>
        simple refine (HitRec.hrecursion target (fun target => P) _ _ _ _ _ _ _)
      | forall Y _ _ _ _ _ _ _, Y target  =>
        simple refine (HitRec.hrecursion target (fun target => P) _ _ _ _ _ _ _)
      | forall Y _ _ _ _ _ _ _ _, Y target  =>
        simple refine (HitRec.hrecursion target (fun target => P) _ _ _ _ _ _ _ _)
      | forall Y _ _ _ _ _ _ _ _ _, Y target  =>
        simple refine (HitRec.hrecursion target (fun target => P) _ _ _ _ _ _ _ _ _)
      | forall Y, Y =>
        simple refine (HitRec.hrecursion target P)
      | forall Y _, Y  =>
        simple refine (HitRec.hrecursion target P _)
      | forall Y _ _, Y =>
        simple refine (HitRec.hrecursion target P _ _)
      | forall Y _ _ _, Y  =>
        simple refine (HitRec.hrecursion target P _ _ _)
      | forall Y _ _ _ _, Y  =>
        simple refine (HitRec.hrecursion target P _ _ _ _)
      | forall Y _ _ _ _ _, Y =>
        simple refine (HitRec.hrecursion target P _ _ _ _ _)
      | forall Y _ _ _ _ _ _, Y =>
        simple refine (HitRec.hrecursion target P _ _ _ _ _ _)
      | forall Y _ _ _ _ _ _ _, Y =>
        simple refine (HitRec.hrecursion target P _ _ _ _ _ _ _)
      | forall Y _ _ _ _ _ _ _ _, Y =>
        simple refine (HitRec.hrecursion target P _ _ _ _ _ _ _ _)
      | forall Y _ _ _ _ _ _ _ _ _, Y =>
        simple refine (HitRec.hrecursion target P _ _ _ _ _ _ _ _ _)
      | forall Y _ _ _ _ _ _ _ _ _ _, Y =>
        simple refine (HitRec.hrecursion target P _ _ _ _ _ _ _ _ _ _)
      | _ => fail "Cannot handle the recursion principle (too many parameters?) :("
     end
    end
  end.

Ltac hrecursion x := hrecursion_ x; simpl; try (clear x).


