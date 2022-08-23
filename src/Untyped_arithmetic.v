Require Import Coq.Strings.String.

Inductive result (a b : Type) : Type :=
| Ok : a -> result a b
| Error : b -> result a b.
Arguments Ok {_ _}.
Arguments Error {_ _}.


Definition return_result {a trace : Type} (x : a) : result a trace :=
  Ok x.

Definition bind_result {a b trace : Type}
  (x : result a trace) (f : a -> result b trace) :
  result b trace :=
  match x with
  | Ok x => f x
  | Error trace => Error trace
  end.

Notation "return? X" := (return_result X) (at level 20).

Notation "'let?' x ':=' X 'in' Y" :=
  (bind_result X (fun x => Y))
  (at level 200, X at level 100, Y at level 200).

Notation "'let?' ' x ':=' X 'in' Y" :=
  (bind_result X (fun x => Y))
  (at level 200, x pattern, X at level 100, Y at level 200).

Definition Info := string.
Definition dummyInfo : Info := 
  "Dummy info"%string.

Inductive Term : Type :=
  | TmTrue (info : Info)
  | TmFalse (info : Info)
  | TmIf (info : Info) (t1 t2 t3 : Term)
  | TmZero (info : Info)
  | TmSucc (info : Info) (t1 : Term)
  | TmPred (info : Info) (t1 : Term)
  | TmIsZero (info : Info) (t1 : Term).

Fixpoint isnumericalval t :=
  match t with
  | TmZero _ => true
  | TmSucc _ t1 => isnumericalval t1
  | _ => false
  end.

Fixpoint isval t :=
  match t with
  | TmTrue _ => true
  | TmFalse _ => true
  | t => isnumericalval t
  end.

Fixpoint eval1 t : result Term string :=
  match t with
  | TmIf _ (TmTrue _) t2 t3 => return? t2
  | TmIf _ (TmFalse _) t2 t3 => return? t3
  | TmIf fi t1 t2 t3 =>
    let t1' := eval1 t1 in
    match t1' with
    | Ok t1' => return? (TmIf fi t1' t2 t3)
    | _ => Error "No Case"%string
    end
  | TmSucc fi t1 =>
    let t1' := eval1 t1 in
    return? (TmSucc fi t1)
  | TmPred fi t1 => 
    match t1 with
    | TmZero _ => return? (TmZero dummyInfo)
    | TmSucc _ t1' =>
      if isnumericalval t1' then return? t1' else
      let? t1'' := eval1 t1' in
      return? t1''
      (* match t1'' with
      | return? t1'' => return? (TmPred fi t1'')
      | _ => Error "No Case"%string
      end *)
    | _ => Error "No Case"%string
    end
  | _ => Error "No Case"%string
  end.