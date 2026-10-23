(** * Field and method descriptors (JVMS 4.3). *)

From Stdlib Require Import ZArith String Ascii List.
Import ListNotations.

Inductive jtype : Type :=
| TBool | TByte | TChar | TShort | TInt | TLong | TFloat | TDouble
| TRef (cls : string)
| TArr (elt : jtype).

(** Category 2 types occupy two local-variable slots / count twice on the stack. *)
Definition jtype_size (t : jtype) : nat :=
  match t with TLong | TDouble => 2 | _ => 1 end.

(** Read a class name up to ';'. *)
Fixpoint read_class (s : string) (acc : string) : option (string * string) :=
  match s with
  | EmptyString => None
  | String c r =>
      if Ascii.eqb c ";"%char then Some (acc, r)
      else read_class r (acc ++ String c EmptyString)%string
  end.

(** One field type at the head of [s]; [fuel] bounds array nesting. *)
Fixpoint parse_ftype (fuel : nat) (s : string) : option (jtype * string) :=
  match fuel with
  | O => None
  | S n =>
    match s with
    | EmptyString => None
    | String c r =>
      if Ascii.eqb c "Z"%char then Some (TBool, r)
      else if Ascii.eqb c "B"%char then Some (TByte, r)
      else if Ascii.eqb c "C"%char then Some (TChar, r)
      else if Ascii.eqb c "S"%char then Some (TShort, r)
      else if Ascii.eqb c "I"%char then Some (TInt, r)
      else if Ascii.eqb c "J"%char then Some (TLong, r)
      else if Ascii.eqb c "F"%char then Some (TFloat, r)
      else if Ascii.eqb c "D"%char then Some (TDouble, r)
      else if Ascii.eqb c "L"%char then
        match read_class r EmptyString with
        | Some (cn, r') => Some (TRef cn, r')
        | None => None
        end
      else if Ascii.eqb c "["%char then
        match parse_ftype n r with
        | Some (t, r') => Some (TArr t, r')
        | None => None
        end
      else None
    end
  end.

Fixpoint parse_params (fuel : nat) (s : string) : option (list jtype * string) :=
  match fuel with
  | O => None
  | S n =>
    match s with
    | String c r =>
      if Ascii.eqb c ")"%char then Some ([], r)
      else match parse_ftype 256 s with
           | Some (t, r') =>
               match parse_params n r' with
               | Some (ts, r'') => Some (t :: ts, r'')
               | None => None
               end
           | None => None
           end
    | EmptyString => None
    end
  end.

(** A method descriptor: parameter types and return type ([None] = void). *)
Definition parse_mdesc (s : string) : option (list jtype * option jtype) :=
  match s with
  | String c r =>
    if Ascii.eqb c "("%char then
      match parse_params 256 r with
      | Some (ps, String v EmptyString) =>
          if Ascii.eqb v "V"%char then Some (ps, None)
          else match parse_ftype 256 (String v EmptyString) with
               | Some (t, EmptyString) => Some (ps, Some t)
               | _ => None
               end
      | Some (ps, rest) =>
          match parse_ftype 256 rest with
          | Some (t, EmptyString) => Some (ps, Some t)
          | _ => None
          end
      | None => None
      end
    else None
  | EmptyString => None
  end.

Example parse_canUpdate : parse_mdesc "(IIII)Z" = Some ([TInt; TInt; TInt; TInt], Some TBool).
Proof. reflexivity. Qed.
Example parse_obj : parse_mdesc "(J[Ljava/lang/String;)V"
  = Some ([TLong; TArr (TRef "java/lang/String")], None).
Proof. reflexivity. Qed.
