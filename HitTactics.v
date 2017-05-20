Module HitRec.
Record class (H : Type) (* The HIT type itself *)
             (indTy : H -> Type) (* The type of the induciton principle *)
             (recTy : H -> Type) (* The type of the recursion principle *)
             := Class { 
    H_recursor : forall (x : H), recTy x;
    H_inductor : forall (x : H), indTy x  }.
Structure type := Pack { obj : Type ; ind : obj -> Type ; rec : obj -> Type ; class_of : class obj ind rec }.
Definition hrecursion (e : type) : forall x, rec e x :=
  let 'Pack _ _ _ (Class r _) := e
  in r.
Definition hinduction (e : type) : forall x, ind e x :=
  let 'Pack _ _ _ (Class _ i) := e
  in i.
Arguments hrecursion {e} x : simpl never.
Arguments hinduction {e} x : simpl never.
Arguments Class H {indTy recTy} H_recursor H_inductor.
End HitRec.

Ltac hrecursion_ target :=
  generalize dependent target;
  match goal with
  | [ |- _ -> ?P ] => intro target;
    match type of (HitRec.hrecursion target) with
    | ?Q => 
      match (eval simpl in Q) with
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
  | [ |- forall target, ?P] => intro target;
    match type of (HitRec.hinduction target) with
    | ?Q => 
      match (eval simpl in Q) with
      | forall Y , Y target =>
        simple refine (HitRec.hinduction target (fun target => P) _)
      | forall Y _, Y target  =>
        simple refine (HitRec.hinduction target (fun target => P) _)
      | forall Y _ _, Y target  =>
        simple refine (HitRec.hinduction target (fun target => P) _ _)
      | forall Y _ _ _, Y target  =>
        let hrec:=(eval hnf in (HitRec.hinduction target)) in
        simple refine (hrec (fun target => P) _ _ _)
      | forall Y _ _ _ _, Y target  =>
        simple refine (HitRec.hinduction target (fun target => P) _ _ _ _)
      | forall Y _ _ _ _ _, Y target  =>
        simple refine (HitRec.hinduction target (fun target => P) _ _ _ _ _)
      | forall Y _ _ _ _ _ _, Y target  =>
        simple refine (HitRec.hinduction target (fun target => P) _ _ _ _ _ _)
      | forall Y _ _ _ _ _ _ _, Y target  =>
        simple refine (HitRec.hinduction target (fun target => P) _ _ _ _ _ _ _)
      | forall Y _ _ _ _ _ _ _, Y target  =>
        simple refine (HitRec.hinduction target (fun target => P) _ _ _ _ _ _ _)
      | forall Y _ _ _ _ _ _ _ _, Y target  =>
        simple refine (HitRec.hinduction target (fun target => P) _ _ _ _ _ _ _ _)
      | forall Y _ _ _ _ _ _ _ _ _, Y target  =>
        simple refine (HitRec.hinduction target (fun target => P) _ _ _ _ _ _ _ _ _)
      | _ => fail "Cannot handle the induction principle (too many parameters?) :("
     end
    end
  (*| _ => fail "I am sorry, but something went wrong!"*)
  end.

Ltac hrecursion x := hrecursion_ x; simpl; try (clear x).
Ltac hinduction x := hrecursion x.
