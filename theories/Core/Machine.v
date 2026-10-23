(** * Phase 2/3: the multi-frame machine with heap, arrays, exceptions, calls
    and class initialisation (single thread).

    The Phase 1 interpreter ([Semantics.step]) is reused unchanged for every
    instruction that only touches the current frame; this file adds the
    instructions that touch the heap, the static fields, other frames or the
    class hierarchy (JVMS SE 21 chapter 6, and 5.4.3 resolution / 5.5
    initialisation):
    - objects: new, getfield, putfield, getstatic, putstatic (with
      boolean/byte/char/short narrowing on store, JVMS 6.5 putfield);
    - arrays: newarray, anewarray, arraylength, all xaload/xastore with the
      exception order null -> index (JVMS 6.5 iaload) and baload/bastore
      boolean/byte handling; aastore's ArrayStoreException check;
    - exceptions as heap objects: athrow, VM-created exceptions, handler search
      through the exception tables of all frames (JVMS 2.10);
    - calls: invokestatic/special/virtual/interface with method resolution up
      the superclass chain, virtual dispatch on the receiver's runtime class,
      null receiver -> NullPointerException; return values flow back;
    - class initialisation: before new / getstatic / putstatic / invokestatic
      on a loaded class, its superclasses and then the class run [<clinit>]
      once (JVMS 5.5 steps for a single thread);
    - checkcast / instanceof over the loaded hierarchy plus a table of
      java.lang classes; monitorenter/monitorexit with per-object counts.
    Methods of classes that are not loaded (the JDK) run only through
    [model]s: each is an explicit specification and is listed in TRUST.md.
    Anything else is [Stuck], so it can never make a false theorem provable.

    Not yet (later phases): float/double, invokedynamic, String constants,
    multianewarray, interface default-method resolution, threads,
    ExceptionInInitializerError wrapping (an exception escaping <clinit> is
    [Stuck]), stack overflow, out of memory. *)

From Stdlib Require Import ZArith String Ascii List Bool Lia.
From JVM.Core Require Import Int Instr Desc Semantics.
From JVM.Loader Require Import ClassFile.
Import ListNotations.
Open Scope string_scope.
Open Scope bool_scope.
Open Scope Z_scope.

(** Decimal digits of an integer as UTF-16 units (Integer/Long.toString). *)
Fixpoint z_digits_rev (fuel : nat) (n : Z) : list Z :=
  match fuel with
  | O => nil
  | S k => (48 + n mod 10) :: (if n <? 10 then nil else z_digits_rev k (n / 10))
  end.
Definition z_units (z : Z) : list Z :=
  if z <? 0 then 45 :: rev (z_digits_rev 25 (- z)) else rev (z_digits_rev 25 z).

(** ** Heap *)
Inductive object : Type :=
| OObj (cls : string) (fields : list (string * value))   (** field name -> value *)
| OArr (elt : jtype) (elems : list value)
| OStr (u : list Z)          (** java.lang.String: its UTF-16 code units (immutable) *)
| OSb (u : list Z)           (** java.lang.StringBuilder: its current code units *)
| OCls (name : string)       (** java.lang.Class object of a class (internal name or descriptor) *)
| OLam (iface sam : string) (kind : Z) (impl : methodref) (cap : list value).
   (** object made by LambdaMetafactory: functional interface, its method name,
       the implementation method handle (kind, method) and the captured values *)

Definition heap := Z -> option object.
Definition upd {A} (h : Z -> option A) (l : Z) (o : A) : Z -> option A :=
  fun x => if Z.eqb x l then Some o else h x.

Fixpoint assoc {A} (k : string) (l : list (string * A)) : option A :=
  match l with
  | nil => None
  | (k', v) :: r => if String.eqb k k' then Some v else assoc k r
  end.

Fixpoint set_assoc {A} (k : string) (v : A) (l : list (string * A)) : option (list (string * A)) :=
  match l with
  | nil => None
  | (k', w) :: r => if String.eqb k k' then Some ((k', v) :: r)
                    else option_map (cons (k', w)) (set_assoc k v r)
  end.

Fixpoint set_nth_z {A} (l : list A) (i : Z) (v : A) : list A :=
  match l with
  | nil => nil
  | x :: r => if Z.eqb i 0 then v :: r else x :: set_nth_z r (i - 1) v
  end.

(** ** Program: the loaded classes *)
Definition program := list classfile.

Fixpoint find_class (p : program) (n : string) : option classfile :=
  match p with
  | nil => None
  | c :: r => if String.eqb (cf_this c) n then Some c else find_class r n
  end.

(** Superclasses of the JDK classes the VM itself needs (exceptions it throws,
    [Object]).  [None] = unknown class. *)
Definition builtin_interfaces : list string :=
  ["java/io/Serializable"; "java/lang/Comparable"; "java/lang/CharSequence"; "java/lang/Cloneable";
   "java/lang/Appendable"; "java/lang/constant/Constable"; "java/lang/constant/ConstantDesc";
   "java/lang/Runnable"; "java/lang/AutoCloseable"; "java/lang/Iterable"].

Definition builtin_super (c : string) : option (option string) :=
  let RE := Some (Some "java/lang/RuntimeException") in
  if String.eqb c "java/lang/Object" then Some None
  else if String.eqb c "java/lang/Throwable" then Some (Some "java/lang/Object")
  else if String.eqb c "java/lang/Exception" then Some (Some "java/lang/Throwable")
  else if String.eqb c "java/lang/Error" then Some (Some "java/lang/Throwable")
  else if String.eqb c "java/lang/RuntimeException" then Some (Some "java/lang/Exception")
  else if String.eqb c "java/lang/ArithmeticException" then RE
  else if String.eqb c "java/lang/NullPointerException" then RE
  else if String.eqb c "java/lang/IndexOutOfBoundsException" then RE
  else if String.eqb c "java/lang/ArrayIndexOutOfBoundsException" then Some (Some "java/lang/IndexOutOfBoundsException")
  else if String.eqb c "java/lang/NegativeArraySizeException" then RE
  else if String.eqb c "java/lang/ClassCastException" then RE
  else if String.eqb c "java/lang/ArrayStoreException" then RE
  else if String.eqb c "java/lang/IllegalMonitorStateException" then RE
  else if String.eqb c "java/lang/IllegalArgumentException" then RE
  else if String.eqb c "java/lang/IllegalStateException" then RE
  else if String.eqb c "java/lang/UnsupportedOperationException" then RE
  else if String.eqb c "java/lang/StringIndexOutOfBoundsException" then Some (Some "java/lang/IndexOutOfBoundsException")
  else if String.eqb c "java/lang/NumberFormatException" then Some (Some "java/lang/IllegalArgumentException")
  else if String.eqb c "java/util/NoSuchElementException" then RE
  else if String.eqb c "java/util/ConcurrentModificationException" then RE
  else if String.eqb c "java/lang/CloneNotSupportedException" then Some (Some "java/lang/Exception")
  else if String.eqb c "java/lang/LinkageError" then Some (Some "java/lang/Error")
  else if String.eqb c "java/lang/ExceptionInInitializerError" then Some (Some "java/lang/LinkageError")
  else if String.eqb c "java/lang/NoClassDefFoundError" then Some (Some "java/lang/LinkageError")
  else if String.eqb c "java/lang/VirtualMachineError" then Some (Some "java/lang/Error")
  else if String.eqb c "java/lang/StackOverflowError" then Some (Some "java/lang/VirtualMachineError")
  else if String.eqb c "java/lang/OutOfMemoryError" then Some (Some "java/lang/VirtualMachineError")
  else if String.eqb c "java/lang/AssertionError" then Some (Some "java/lang/Error")
  else if String.eqb c "java/lang/Number" then Some (Some "java/lang/Object")
  else if String.eqb c "java/lang/Integer" || String.eqb c "java/lang/Long" || String.eqb c "java/lang/Short"
          || String.eqb c "java/lang/Byte" then Some (Some "java/lang/Number")
  else if String.eqb c "java/lang/Boolean" || String.eqb c "java/lang/Character" then Some (Some "java/lang/Object")
  else if String.eqb c "java/lang/String" then Some (Some "java/lang/Object")
  else if String.eqb c "java/lang/AbstractStringBuilder" then Some (Some "java/lang/Object")
  else if String.eqb c "java/lang/StringBuilder" then Some (Some "java/lang/AbstractStringBuilder")
  else if String.eqb c "java/lang/Class" then Some (Some "java/lang/Object")
  else if String.eqb c "java/lang/Enum" then Some (Some "java/lang/Object")
  else if existsb (String.eqb c) builtin_interfaces then Some (Some "java/lang/Object")
  else None.

Definition super_of (p : program) (c : string) : option (option string) :=
  match find_class p c with
  | Some cf => Some (cf_super cf)
  | None => builtin_super c
  end.

Definition interfaces_of (p : program) (c : string) : list string :=
  match find_class p c with
  | Some cf => cf_interfaces cf
  | None =>
    if String.eqb c "java/lang/String" then
      ["java/io/Serializable"; "java/lang/Comparable"; "java/lang/CharSequence";
       "java/lang/constant/Constable"; "java/lang/constant/ConstantDesc"]
    else if String.eqb c "java/lang/AbstractStringBuilder" then ["java/lang/Appendable"; "java/lang/CharSequence"]
    else if String.eqb c "java/lang/StringBuilder" then
      ["java/io/Serializable"; "java/lang/Comparable"; "java/lang/CharSequence"]
    else if String.eqb c "java/lang/Enum" then
      ["java/lang/constant/Constable"; "java/lang/Comparable"; "java/io/Serializable"]
    else if String.eqb c "java/lang/Throwable" then ["java/io/Serializable"]
    else if String.eqb c "java/lang/Class" then ["java/io/Serializable"]
    else nil
  end.

(** [subclass p fuel c d]: is class/interface [c] a subtype of class/interface [d]?
    [None] when the hierarchy is not known well enough to decide. *)
Fixpoint subclass (p : program) (fuel : nat) (c d : string) : option bool :=
  if String.eqb c d then Some true else
  match fuel with
  | O => None
  | S k =>
    let via_ifaces :=
      fold_left (fun acc i => match acc with
                              | Some true => Some true
                              | None => None
                              | Some false => subclass p k i d
                              end) (interfaces_of p c) (Some false) in
    match via_ifaces with
    | Some true => Some true
    | None => None
    | Some false =>
      match super_of p c with
      | Some (Some s) => subclass p k s d
      | Some None => Some false
      | None => None
      end
    end
  end.

(** Runtime type names: classes by internal name, arrays by descriptor. *)
Fixpoint type_desc (t : jtype) : string :=
  match t with
  | TBool => "Z" | TByte => "B" | TChar => "C" | TShort => "S" | TInt => "I"
  | TLong => "J" | TFloat => "F" | TDouble => "D"
  | TRef c => "L" ++ c ++ ";"
  | TArr e => "[" ++ type_desc e
  end.

(** Assignability of a runtime object to a class/array type named as in a
    constant-pool class entry (JVMS 6.5 checkcast). *)
Fixpoint assignable (p : program) (fuel : nat) (src : jtype) (dst : string) : option bool :=
  match fuel with
  | O => None
  | S k =>
    match src with
    | TRef c => subclass p 64 c dst
    | TArr e =>
        if String.eqb dst "java/lang/Object" || String.eqb dst "java/lang/Cloneable"
           || String.eqb dst "java/io/Serializable" then Some true
        else match dst with
             | String "["%char rest =>
                 match parse_ftype 256 rest, e with
                 | Some (TRef d, EmptyString), (TRef _ | TArr _) => assignable p k e d
                 | Some (TArr d', EmptyString), (TRef _ | TArr _) => assignable p k e (type_desc (TArr d'))
                 | Some (d, EmptyString), _ => Some (String.eqb (type_desc d) (type_desc e))
                 | _, _ => None
                 end
             | _ => Some false
             end
    | _ => None
    end
  end.

Definition runtime_type (o : object) : jtype :=
  match o with
  | OObj c _ => TRef c | OArr e _ => TArr e
  | OStr _ => TRef "java/lang/String" | OSb _ => TRef "java/lang/StringBuilder"
  | OCls _ => TRef "java/lang/Class"
  | OLam i _ _ _ _ => TRef i
  end.

(** ** Defaults and field declarations *)
Definition default_of (t : jtype) : value :=
  match t with
  | TLong => VLong 0 | TFloat => VFloat 0 | TDouble => VDouble 0
  | TRef _ | TArr _ => VNull
  | _ => VInt 0
  end.

Definition field_type (desc : string) : option jtype :=
  match parse_ftype 256 desc with Some (t, EmptyString) => Some t | _ => None end.

Definition is_static_member (m : member) : bool := Z.testbit (mb_access m) 3.

(** Instance fields of [c] and its loaded superclasses with default values. *)
Fixpoint instance_fields (p : program) (fuel : nat) (c : string) : option (list (string * value)) :=
  match fuel with
  | O => None
  | S k =>
    match find_class p c with
    | None =>
        if String.eqb c "java/lang/Enum" then Some [("name", VNull); ("ordinal", VInt 0)]
        else match builtin_super c with Some _ => Some nil | None => None end
    | Some cf =>
      let own := fold_right (fun m acc =>
                   match acc with
                   | None => None
                   | Some l => if is_static_member m then Some l else
                               match field_type (mb_desc m) with
                               | Some t => Some ((mb_name m, default_of t) :: l)
                               | None => None
                               end
                   end) (Some nil) (cf_fields cf) in
      match own, cf_super cf with
      | Some l, Some s => option_map (fun l' => app l l') (instance_fields p k s)
      | Some l, None => Some l
      | None, _ => None
      end
    end
  end.

(** Narrowing of a stored int by the declared type (putfield/putstatic, bastore...). *)
Definition narrow_store (t : jtype) (v : value) : value :=
  match t, v with
  | TBool, VInt z => VInt (Z.land z 1)
  | TByte, VInt z => VInt (i2b z)
  | TChar, VInt z => VInt (i2c z)
  | TShort, VInt z => VInt (i2s z)
  | _, _ => v
  end.

Definition value_fits (t : jtype) (v : value) : bool :=
  match t, v with
  | (TBool | TByte | TChar | TShort | TInt), VInt _ => true
  | TLong, VLong _ | TFloat, VFloat _ | TDouble, VDouble _ => true
  | (TRef _ | TArr _), (VNull | VRef _) => true
  | _, _ => false
  end.

(** ** Machine state *)
Record cframe := mkcf {
  cf_class : string;
  cf_method : method;
  cf_code : code;
  cf_rt : option jtype;
  cf_frame : frame;
  cf_resume : option pc;    (** set while a callee runs: [Some next] after an invoke,
                                [None] while a <clinit> triggered by this instruction runs *)
  cf_clinit : bool;         (** this frame runs a class initialiser *)
}.

Record mstate := mkms {
  ms_heap : heap;
  ms_next : Z;
  ms_statics : list (string * value);   (** key "Class.name" *)
  ms_inited : list string;              (** classes whose initialisation has started *)
  ms_locks : list (Z * Z);              (** monitor entry counts *)
  ms_frames : list cframe;
}.

Definition static_key (c n : string) : string := c ++ "." ++ n.

(** ** Models of methods outside the loaded classes (JDK, natives).
    A model gets the arguments (receiver first) and the heap. *)
Inductive model_result : Type :=
| MOk (ret : option value) (s : mstate)   (** the model may change heap/statics, never frames *)
| MThrow (cls : string)
| MStuckModel (why : string)
| MNoModel.

Definition model := string -> string -> string -> list value -> mstate -> model_result.

(** The models of this phase (see TRUST.md, "Axiomatised natives"):
    the no-argument constructors of [Object] and of the java.lang exception
    classes in [builtin_super] do nothing observable in the modelled state
    (messages, stack traces and causes are not modelled). *)
Definition base_model : model :=
  fun cls name desc args s =>
    if String.eqb name "<init>" && String.eqb desc "()V" then
      match builtin_super cls with
      | Some _ => MOk None s
      | None => MNoModel
      end
    else MNoModel.

(** ** Step outcome *)
Inductive mstep : Type :=
| MNext (s : mstate)
| MReturn (v : option value) (s : mstate)    (** the bottom frame returned *)
| MUncaught (exn : Z) (s : mstate)            (** exception left the bottom frame *)
| MStuck (why : string).

Definition alloc (s : mstate) (o : object) : Z * mstate :=
  (ms_next s, {| ms_heap := upd (ms_heap s) (ms_next s) o; ms_next := ms_next s + 1;
                 ms_statics := ms_statics s; ms_inited := ms_inited s; ms_locks := ms_locks s;
                 ms_frames := ms_frames s |}).

Definition with_frames (s : mstate) (fs : list cframe) : mstate :=
  {| ms_heap := ms_heap s; ms_next := ms_next s; ms_statics := ms_statics s;
     ms_inited := ms_inited s; ms_locks := ms_locks s; ms_frames := fs |}.

(** ** String/Class interning (JVMS 5.1: equal literals denote the same object). *)
Definition hexd (d : Z) : Ascii.ascii := Ascii.ascii_of_nat (Z.to_nat (if d <? 10 then 48 + d else 87 + d)).
Definition unit_key (u : Z) : string :=
  String (hexd (u / 4096 mod 16)) (String (hexd (u / 256 mod 16))
    (String (hexd (u / 16 mod 16)) (String (hexd (u mod 16)) EmptyString))).
Definition intern_key (o : object) : string :=
  match o with
  | OStr u => "#s:" ++ fold_right (fun c acc => unit_key c ++ acc) "" u
  | OCls n => "#c:" ++ n
  | _ => "#other"
  end.

Definition intern (s : mstate) (o : object) : Z * mstate :=
  let k := intern_key o in
  match assoc k (ms_statics s) with
  | Some (VRef l) => (l, s)
  | _ => let (l, s1) := alloc s o in
         (l, {| ms_heap := ms_heap s1; ms_next := ms_next s1; ms_statics := (k, VRef l) :: ms_statics s1;
                ms_inited := ms_inited s1; ms_locks := ms_locks s1; ms_frames := ms_frames s1 |})
  end.

Definition set_frame (c : cframe) (f : frame) : cframe :=
  {| cf_class := cf_class c; cf_method := cf_method c; cf_code := cf_code c; cf_rt := cf_rt c;
     cf_frame := f; cf_resume := cf_resume c; cf_clinit := cf_clinit c |}.

Definition set_resume (c : cframe) (r : option pc) : cframe :=
  {| cf_class := cf_class c; cf_method := cf_method c; cf_code := cf_code c; cf_rt := cf_rt c;
     cf_frame := cf_frame c; cf_resume := r; cf_clinit := cf_clinit c |}.

(** ** Exception dispatch (JVMS 2.10): search handlers frame by frame. *)
Fixpoint find_handler (p : program) (hs : list handler) (at_pc : pc) (t : jtype) : option (option pc) :=
  match hs with
  | nil => Some None
  | h :: r =>
    if (h_start h <=? at_pc) && (at_pc <? h_end h) then
      match h_catch h with
      | None => Some (Some (h_pc h))
      | Some c =>
        match assignable p 64 t c with
        | Some true => Some (Some (h_pc h))
        | Some false => find_handler p r at_pc t
        | None => None
        end
      end
    else find_handler p r at_pc t
  end.

Fixpoint unwind (p : program) (s : mstate) (exn : Z) (t : jtype) (fs : list cframe) : mstep :=
  match fs with
  | nil => MUncaught exn (with_frames s nil)
  | c :: rest =>
    let f := cf_frame c in
    match find_handler p (c_handlers (cf_code c)) (f_pc f) t with
    | None => MStuck "handler: cannot decide the exception's type"
    | Some (Some hpc) =>
        MNext (with_frames s (set_resume (set_frame c (mkframe hpc [VRef exn] (f_locals f))) None :: rest))
    | Some None =>
        if cf_clinit c then
          (* JVMS 5.5 step 11: the class becomes erroneous; an Error propagates as is,
             any other exception is wrapped in ExceptionInInitializerError and thrown
             at the instruction that triggered the initialisation. *)
          let s1 := {| ms_heap := ms_heap s; ms_next := ms_next s;
                       ms_statics := ("#err:" ++ cf_class c, VInt 1) :: ms_statics s;
                       ms_inited := ms_inited s; ms_locks := ms_locks s; ms_frames := ms_frames s |} in
          match subclass p 64 (match t with TRef n => n | _ => "" end) "java/lang/Error" with
          | Some true => unwind p s1 exn t rest
          | Some false =>
              let l := ms_next s1 in
              let s2 := {| ms_heap := upd (ms_heap s1) l (OObj "java/lang/ExceptionInInitializerError" nil);
                           ms_next := l + 1; ms_statics := ms_statics s1; ms_inited := ms_inited s1;
                           ms_locks := ms_locks s1; ms_frames := ms_frames s1 |} in
              unwind p s2 l (TRef "java/lang/ExceptionInInitializerError") rest
          | None => MStuck "exception in <clinit>: cannot decide whether it is an Error"
          end
        else unwind p s exn t rest
    end
  end.

Definition throw_obj (p : program) (s : mstate) (exn : Z) : mstep :=
  match ms_heap s exn with
  | Some o => unwind p s exn (runtime_type o) (ms_frames s)
  | None => MStuck "athrow: dangling reference"
  end.

(** A VM-created exception of class [cls] (no message / stack trace modelled). *)
Definition throw_new (p : program) (s : mstate) (cls : string) : mstep :=
  let (l, s') := alloc s (OObj cls nil) in throw_obj p s' l.

Definition NPE := "java/lang/NullPointerException".
Definition AIOOBE := "java/lang/ArrayIndexOutOfBoundsException".

(** ** Class initialisation (JVMS 5.5, single thread). *)
(** A class whose <clinit> failed is erroneous: later uses throw NoClassDefFoundError. *)
Fixpoint erroneous (p : program) (fuel : nat) (statics : list (string * value)) (c : string) : bool :=
  match fuel with
  | O => false
  | S k => match find_class p c with
           | None => false          (* JDK classes are never initialised by the machine *)
           | Some cf => match assoc ("#err:" ++ c) statics with
                        | Some _ => true
                        | None => match cf_super cf with Some sup => erroneous p k statics sup | None => false end
                        end
           end
  end.

(** The outermost loaded superclass of [c] (or [c] itself) whose
    initialisation has not started; [None] if none (all started or not loaded). *)
Fixpoint init_needed (p : program) (fuel : nat) (inited : list string) (c : string) : option classfile :=
  match fuel with
  | O => None
  | S k =>
    match find_class p c with
    | None => None
    | Some cf =>
      if existsb (String.eqb c) inited then None else
      match cf_super cf with
      | Some sup => match init_needed p k inited sup with
                    | Some x => Some x
                    | None => Some cf
                    end
      | None => Some cf
      end
    end
  end.

Definition cp_constant_value (cf : classfile) (m : member) (t : jtype) : option (value + list Z) :=
  match find_attr "ConstantValue" (mb_attrs m) with
  | None => Some (inl (default_of t))
  | Some (hi :: lo :: _) =>
      match cp_get (cf_cp cf) (hi * 256 + lo), t with
      | Some (CPInt z), (TBool | TByte | TChar | TShort | TInt) => Some (inl (VInt z))
      | Some (CPLong z), TLong => Some (inl (VLong z))
      | Some (CPFloat b), TFloat => Some (inl (VFloat b))
      | Some (CPDouble b), TDouble => Some (inl (VDouble b))
      | Some (CPString u), TRef _ => let* raw := cp_utf8 (cf_cp cf) u in
                                     let* units := utf8_units raw in Some (inr units)
      | _, _ => None
      end
  | Some _ => None
  end.

Definition static_inits (cf : classfile) : option (list (string * (value + list Z))) :=
  fold_right (fun m acc =>
    match acc with
    | None => None
    | Some l =>
      if is_static_member m then
        match field_type (mb_desc m) with
        | Some t => option_map (fun v => (static_key (cf_this cf) (mb_name m), v) :: l)
                               (cp_constant_value cf m t)
        | None => None
        end
      else Some l
    end) (Some nil) (cf_fields cf).

(** Set the static fields; String constants are interned (JVMS 5.5 step 6 / 4.7.2). *)
Fixpoint put_statics (s : mstate) (l : list (string * (value + list Z))) : mstate :=
  match l with
  | nil => s
  | (k, inl v) :: r => let s' := put_statics s r in
                       {| ms_heap := ms_heap s'; ms_next := ms_next s'; ms_statics := (k, v) :: ms_statics s';
                          ms_inited := ms_inited s'; ms_locks := ms_locks s'; ms_frames := ms_frames s' |}
  | (k, inr u) :: r => let s' := put_statics s r in
                       let (loc, s'') := intern s' (OStr u) in
                       {| ms_heap := ms_heap s''; ms_next := ms_next s''; ms_statics := (k, VRef loc) :: ms_statics s'';
                          ms_inited := ms_inited s''; ms_locks := ms_locks s''; ms_frames := ms_frames s'' |}
  end.

(** Start initialising [cf]: mark it, set its static fields, and push its
    <clinit> (if any) on top of the current frames; the triggering
    instruction is re-executed when it returns. *)
Definition start_init (s : mstate) (cf : classfile) : mstep :=
  match static_inits cf with
  | None => MStuck "static field initial value not supported yet"
  | Some sts =>
    let s0 := put_statics s sts in
    let s1 := {| ms_heap := ms_heap s0; ms_next := ms_next s0; ms_statics := ms_statics s0;
                 ms_inited := cf_this cf :: ms_inited s0; ms_locks := ms_locks s0;
                 ms_frames := ms_frames s0 |} in
    match find_method cf "<clinit>" "()V" with
    | None => MNext s1
    | Some m =>
      match m_code m with
      | None => MStuck "<clinit> without code"
      | Some c =>
        match ms_frames s with
        | top :: rest =>
            MNext (with_frames s1
              ({| cf_class := cf_this cf; cf_method := m; cf_code := c; cf_rt := None;
                  cf_frame := mkframe 0 nil (repeat VTop (Z.to_nat (c_max_locals c)));
                  cf_resume := None; cf_clinit := true |} :: set_resume top None :: rest))
        | nil => MStuck "no frame"
        end
      end
    end
  end.

(** ** Method resolution: [c] or its loaded superclasses. *)
Fixpoint resolve (p : program) (fuel : nat) (c name desc : string) : option (string * method) :=
  match fuel with
  | O => None
  | S k =>
    match find_class p c with
    | None => None
    | Some cf =>
      match find_method cf name desc with
      | Some m => Some (c, m)
      | None => match cf_super cf with Some s => resolve p k s name desc | None => None end
      end
    end
  end.

(** Default methods (JVMS 5.4.3.3 step 3, simplified): if the superclass chain
    has no method, search the superinterfaces of the chain, depth first, for a
    method with code.  The "maximally specific" rule is not checked: when two
    unrelated interfaces both supply a default, the first one found is taken
    (javac rejects such classes unless the class overrides the method).
    LIMITATION recorded in STATUS.md. *)
Fixpoint iface_lookup (p : program) (fuel : nat) (ifs : list string) (name desc : string)
  : option (string * method) :=
  match fuel with
  | O => None
  | S k =>
    match ifs with
    | nil => None
    | i :: r =>
      match find_class p i with
      | Some cf =>
        match find_method cf name desc with
        | Some m => match m_code m with
                    | Some _ => Some (i, m)
                    | None => match iface_lookup p k (cf_interfaces cf) name desc with
                              | Some x => Some x
                              | None => iface_lookup p k r name desc
                              end
                    end
        | None => match iface_lookup p k (cf_interfaces cf) name desc with
                  | Some x => Some x
                  | None => iface_lookup p k r name desc
                  end
        end
      | None => iface_lookup p k r name desc
      end
    end
  end.

Fixpoint chain_interfaces (p : program) (fuel : nat) (c : string) : list string :=
  match fuel with
  | O => nil
  | S k => match find_class p c with
           | Some cf => app (cf_interfaces cf)
                            (match cf_super cf with Some s => chain_interfaces p k s | None => nil end)
           | None => nil
           end
  end.

Definition resolve_full (p : program) (c name desc : string) : option (string * method) :=
  match resolve p 64 c name desc with
  | Some x => Some x
  | None => iface_lookup p 256 (match find_class p c with
                                | Some cf => if Z.testbit (cf_access cf) 9 then [c] else chain_interfaces p 64 c
                                | None => nil end) name desc
  end.

Definition ACC_NATIVE : Z := 256.

(** The first class on the superclass chain of [c] (including [c]) that is not loaded. *)
Fixpoint first_unloaded (p : program) (fuel : nat) (c : string) : string :=
  match fuel with
  | O => c
  | S k => match find_class p c with
           | Some cf => match cf_super cf with Some sup => first_unloaded p k sup | None => c end
           | None => c
           end
  end.

(** Pop [n] values (top first) and return them in argument order. *)
Fixpoint pop_n (n : nat) (st : list value) : option (list value * list value) :=
  match n with
  | O => Some (nil, st)
  | S k => match st with
           | v :: r => match pop_n k r with
                       | Some (args, rest) => Some (app args [v], rest)
                       | None => None
                       end
           | nil => None
           end
  end.

(** Enter a resolved method: push a frame for it ([caller] resumes at [nx]). *)
Definition enter (s : mstate) (caller : cframe) (rest : list cframe) (callee_cls : string) (m : method)
                 (args : list value) (nx : pc) : mstep :=
  match m_code m, parse_mdesc (m_desc m) with
  | Some c, Some (_, rt) =>
      match init_frame c args with
      | Some f =>
          MNext (with_frames s ({| cf_class := callee_cls; cf_method := m; cf_code := c; cf_rt := rt;
                                   cf_frame := f; cf_resume := None; cf_clinit := false |}
                                :: set_resume caller (Some nx) :: rest))
      | None => MStuck "max_locals too small for the arguments"
      end
  | None, _ => MStuck "call of a method without code (native/abstract) and without model"
  | _, None => MStuck "bad descriptor"
  end.

(** Push a returned value on the caller and continue after the invoke. *)
Definition return_to (s : mstate) (v : option value) (rest : list cframe) : mstep :=
  match rest with
  | nil => MReturn v (with_frames s nil)
  | caller :: rest' =>
    let f := cf_frame caller in
    match cf_resume caller with
    | Some nx =>
        let st := match v with Some w => w :: f_stack f | None => f_stack f end in
        MNext (with_frames s (set_resume (set_frame caller (mkframe nx st (f_locals f))) None :: rest'))
    | None => (* a <clinit> finished: re-execute the triggering instruction *)
        MNext (with_frames s (caller :: rest'))
    end
  end.

(** Array allocation bound of the model.  The JVMS lets any allocation throw
    OutOfMemoryError when memory is exhausted, which depends on the heap size
    and cannot be predicted from the bytecode.  Allocations above this bound
    are [Stuck] (no claim), so no theorem depends on how big the real heap is. *)
Definition MAX_ARRAY : Z := 2 ^ 20.

Definition elem_of_atype (t : Z) : option jtype :=
  if t =? 4 then Some TBool else if t =? 5 then Some TChar else if t =? 6 then Some TFloat
  else if t =? 7 then Some TDouble else if t =? 8 then Some TByte else if t =? 9 then Some TShort
  else if t =? 10 then Some TInt else if t =? 11 then Some TLong else None.

Definition class_type (n : string) : jtype :=
  match n with
  | String "["%char rest => match parse_ftype 256 n with Some (t, EmptyString) => t | _ => TRef n end
  | _ => TRef n
  end.

(** Does an array element kind accept a stored value (and which element types)? *)
Definition akind_ok (k : akind) (e : jtype) (v : value) : bool :=
  match k, e, v with
  | AI, TInt, VInt _ | AL, TLong, VLong _ | AF, TFloat, VFloat _ | AD, TDouble, VDouble _ => true
  | AB, (TByte | TBool), VInt _ | AC, TChar, VInt _ | AS, TShort, VInt _ => true
  | AA, (TRef _ | TArr _), (VNull | VRef _) => true
  | _, _, _ => false
  end.

Definition akind_load_ok (k : akind) (e : jtype) : bool :=
  match k, e with
  | AI, TInt | AL, TLong | AF, TFloat | AD, TDouble | AB, (TByte | TBool) | AC, TChar | AS, TShort => true
  | AA, (TRef _ | TArr _) => true
  | _, _ => false
  end.

Fixpoint lock_count (ls : list (Z * Z)) (l : Z) : Z :=
  match ls with nil => 0 | (k, n) :: r => if Z.eqb k l then n else lock_count r l end.

(** The recipe and constants of a StringConcatFactory.makeConcatWithConstants call site. *)
Definition concat_recipe (cf : classfile) (bi : Z) : option (list Z * list (list Z)) :=
  let* bms := bootstrap_methods cf in
  let* (mh, args) := nth_z bms bi in
  match cp_get (cf_cp cf) mh with
  | Some (CPMethodHandle _ ref) =>
      let* m := cp_methodref (cf_cp cf) ref in
      if String.eqb (mr_class m) "java/lang/invoke/StringConcatFactory"
         && String.eqb (mr_name m) "makeConcatWithConstants" then
        match args with
        | a0 :: rest =>
            match cp_get (cf_cp cf) a0 with
            | Some (CPString ui) =>
                let* raw := cp_utf8 (cf_cp cf) ui in
                let* recipe := utf8_units raw in
                let* consts := map_opt (fun i => match cp_get (cf_cp cf) i with
                                                 | Some (CPString u) => let* r := cp_utf8 (cf_cp cf) u in utf8_units r
                                                 | Some (CPInt z) => Some (z_units z)
                                                 | _ => None
                                                 end) rest in
                Some (recipe, consts)
            | _ => None
            end
        | nil => None
        end
      else None
  | _ => None
  end.

(** String conversion of one concatenation argument (String.valueOf rules for
    the primitive types, String and null; anything that needs a toString()
    call back into bytecode, or float/double, is not modelled yet). *)
Definition concat_arg (h : heap) (t : jtype) (v : value) : string + list Z :=
  match t, v with
  | (TInt | TByte | TShort), VInt z => inr (z_units z)
  | TLong, VLong z => inr (z_units z)
  | TChar, VInt z => inr [z]
  | TBool, VInt z => inr (if z =? 0 then [102; 97; 108; 115; 101] else [116; 114; 117; 101])
  | (TRef _ | TArr _), VNull => inr [110; 117; 108; 108]
  | (TRef _ | TArr _), VRef l =>
      match h l with
      | Some (OStr u) => inr u
      | _ => inl "string concat: argument needs toString() (callback not modelled yet)"
      end
  | _, _ => inl "string concat: float/double argument (Phase 5) or type mismatch"
  end.

Fixpoint concat_go (fuel : nat) (h : heap) (recipe : list Z) (consts : list (list Z))
         (ps : list jtype) (args : list value) : string + list Z :=
  match fuel with
  | O => inl "string concat: fuel"
  | S k =>
    match recipe with
    | nil => inr nil
    | 1 :: r => match ps, args with
                | t :: ps', v :: args' =>
                    match concat_arg h t v, concat_go k h r consts ps' args' with
                    | inr a, inr b => inr (app a b)
                    | inl e, _ | _, inl e => inl e
                    end
                | _, _ => inl "string concat: too few arguments"
                end
    | 2 :: r => match consts with
                | c :: cs => match concat_go k h r cs ps args with
                             | inr b => inr (app c b)
                             | inl e => inl e
                             end
                | nil => inl "string concat: too few constants"
                end
    | c :: r => match concat_go k h r consts ps args with
                | inr b => inr (c :: b)
                | inl e => inl e
                end
    end
  end.

Definition concat_units (h : heap) (recipe : list Z) (consts : list (list Z)) (ps : list jtype)
           (args : list value) : string + list Z :=
  concat_go (S (length recipe)) h recipe consts ps args.

(** Instructions executed by the frame-local interpreter [Semantics.step]. *)
Definition is_local_instr (i : instr) : bool :=
  match i with
  | New _ | Getfield _ | Putfield _ | Getstatic _ | Putstatic _ | Newarray _ | Anewarray _
  | Arraylength | ALoadArr _ | AStoreArr _ | Athrow | Checkcast _ | Instanceof _
  | Monitorenter | Monitorexit | Invoke _ _ | Ldc (LdcString _) | Ldc (LdcClass _)
  | Invokedynamic _ _ _ | Multianewarray _ _ => false
  | _ => true
  end.

(** ** Method invocation (shared by invoke* and by calls through lambda objects).
    [args] are the popped arguments (receiver first), [r] the rest of the
    caller's operand stack, [nx] the pc after the invoke. *)
Definition invoke_kind_of_ref (kind : Z) : option invoke_kind :=
  if kind =? 6 then Some InvStatic        (* REF_invokeStatic *)
  else if kind =? 5 then Some InvVirtual  (* REF_invokeVirtual *)
  else if kind =? 9 then Some InvInterface
  else if kind =? 7 then Some InvSpecial  (* REF_invokeSpecial: private instance methods *)
  else None.                              (* REF_newInvokeSpecial (Foo::new): not yet *)

Definition invoke_frame_go (top : cframe) (rest : list cframe) (nx : pc) (st' : list value) (s' : mstate) : mstep :=
  if stack_slots st' <=? c_max_stack (cf_code top)
  then MNext (with_frames s' (set_frame top (mkframe nx st' (f_locals (cf_frame top))) :: rest))
  else MStuck "operand stack overflow (max_stack)".

Definition invoke_run_model (p : program) (mdl : model) (s : mstate) (top : cframe) (rest : list cframe)
           (mr : methodref) (args r : list value) (nx : pc) (cls : string) : mstep :=
  match mdl cls (mr_name mr) (mr_desc mr) args s with
  | MOk v s' => invoke_frame_go top rest nx (match v with Some w => w :: r | None => r end)
                                 (with_frames s' (ms_frames s))
  | MThrow cn => throw_new p s cn
  | MStuckModel why => MStuck why
  | MNoModel => MStuck ("no model for " ++ cls ++ "." ++ mr_name mr ++ mr_desc mr)
  end.

(** Virtual / interface / special call on the object [ho] found at the receiver.
    [recur] performs a call through a lambda object (with less fuel). *)
Definition invoke_obj (recur : invoke_kind -> methodref -> list value -> mstep)
           (p : program) (mdl : model) (s : mstate) (top : cframe) (rest : list cframe)
           (k : invoke_kind) (mr : methodref) (l : Z) (more : list value) (ho : option object)
           (r : list value) (nx : pc) : mstep :=
  let f := cf_frame top in
  let caller := set_frame top (mkframe (f_pc f) r (f_locals f)) in
  let args := VRef l :: more in
  match ho with
  | Some (OLam iface sam kind impl cap) =>
      if negb (match k with InvSpecial => true | _ => false end) && String.eqb (mr_name mr) sam then
        match invoke_kind_of_ref kind with
        | Some k' => recur k' impl (app cap more)
        | None => MStuck "lambda: constructor references are not modelled yet"
        end
      else
        match resolve_full p iface (mr_name mr) (mr_desc mr) with
        | Some (cn, m) => enter s caller rest cn m args nx
        | None => MStuck ("method " ++ mr_name mr ++ " on a lambda object is not modelled")
        end
  | _ =>
    let start := match k with
                 | InvSpecial => Some (mr_class mr)
                 | _ => match ho with
                        | Some (OObj cn _) => Some cn
                        | Some (OArr _ _) => Some "java/lang/Object"
                        | Some (OStr _) => Some "java/lang/String"
                        | Some (OSb _) => Some "java/lang/StringBuilder"
                        | Some (OCls _) => Some "java/lang/Class"
                        | Some (OLam i _ _ _ _) => Some i
                        | None => None
                        end
                 end in
    match start with
    | None => MStuck "invoke: dangling receiver"
    | Some cn0 =>
      match resolve_full p cn0 (mr_name mr) (mr_desc mr) with
      | Some (cn, m) =>
          if Z.testbit (m_access m) 8 then invoke_run_model p mdl s top rest mr args r nx cn
          else enter s caller rest cn m args nx
      | None =>
          (* not in a loaded class: the model of the first JDK class on the
             receiver's superclass chain (e.g. java/lang/Enum for an enum), else
             the model of the method as declared *)
          let jc := first_unloaded p 64 cn0 in
          match mdl jc (mr_name mr) (mr_desc mr) args s with
          | MNoModel => invoke_run_model p mdl s top rest mr args r nx (mr_class mr)
          | _ => invoke_run_model p mdl s top rest mr args r nx jc
          end
      end
    end
  end.

Fixpoint do_invoke (fuel : nat) (p : program) (mdl : model) (s : mstate) (top : cframe) (rest : list cframe)
         (k : invoke_kind) (mr : methodref) (args r : list value) (nx : pc) : mstep :=
  let f := cf_frame top in
  let caller := set_frame top (mkframe (f_pc f) r (f_locals f)) in
  match k with
  | InvStatic =>
      if erroneous p 64 (ms_statics s) (mr_class mr) then throw_new p s "java/lang/NoClassDefFoundError" else
      match init_needed p 64 (ms_inited s) (mr_class mr) with
      | Some cf => start_init s cf
      | None =>
        match resolve_full p (mr_class mr) (mr_name mr) (mr_desc mr) with
        | Some (cn, m) =>
            if Z.testbit (m_access m) 8 then invoke_run_model p mdl s top rest mr args r nx cn
            else enter s caller rest cn m args nx
        | None => invoke_run_model p mdl s top rest mr args r nx (mr_class mr)
        end
      end
  | InvSpecial | InvVirtual | InvInterface =>
      match args with
      | VNull :: _ => throw_new p s NPE
      | VRef l :: more =>
          let recur k' impl args' :=
              match fuel with
              | S fu => do_invoke fu p mdl s top rest k' impl args' r nx
              | O => MStuck "lambda: nesting"
              end in
          invoke_obj recur p mdl s top rest k mr l more (ms_heap s l) r nx
      | _ => MStuck "invoke: receiver is not a reference"
      end
  end.

(** The implementation method of a LambdaMetafactory.metafactory call site. *)
Definition lambda_site (cf : classfile) (bi : Z) : option (Z * methodref) :=
  let* bms := bootstrap_methods cf in
  let* (mh, args) := nth_z bms bi in
  match cp_get (cf_cp cf) mh with
  | Some (CPMethodHandle _ ref) =>
      let* m := cp_methodref (cf_cp cf) ref in
      if String.eqb (mr_class m) "java/lang/invoke/LambdaMetafactory" && String.eqb (mr_name m) "metafactory" then
        match args with
        | _ :: impl :: _ :: nil =>
            match cp_get (cf_cp cf) impl with
            | Some (CPMethodHandle kind iref) => let* im := cp_methodref (cf_cp cf) iref in Some (kind, im)
            | _ => None
            end
        | _ => None
        end
      else None
  | _ => None
  end.

(** multianewarray: nested arrays for the given counts (outermost first). *)
Fixpoint multi_alloc (fuel : nat) (s : mstate) (t : jtype) (counts : list Z) : option (Z * mstate) :=
  match fuel with
  | O => None
  | S k =>
    match t, counts with
    | TArr e, [n] =>
        Some (alloc s (OArr e (repeat (default_of e) (Z.to_nat n))))
    | TArr e, n :: more =>
        let fix kids (m : nat) (s : mstate) : option (list value * mstate) :=
          match m with
          | O => Some (nil, s)
          | S m' => match multi_alloc k s e more with
                    | Some (l, s1) => match kids m' s1 with
                                      | Some (ls, s2) => Some (VRef l :: ls, s2)
                                      | None => None
                                      end
                    | None => None
                    end
          end in
        match kids (Z.to_nat n) s with
        | Some (ls, s1) => Some (alloc s1 (OArr e ls))
        | None => None
        end
    | _, _ => None
    end
  end.

(** ** One machine step *)
Definition mstep_of (p : program) (mdl : model) (s : mstate) : mstep :=
  match ms_frames s with
  | nil => MStuck "no frame"
  | top :: rest =>
  let c := cf_code top in
  let f := cf_frame top in
  let st := f_stack f in
  let lv := f_locals f in
  let h := ms_heap s in
  let put_top (f' : frame) (s' : mstate) : mstep :=
      if stack_slots (f_stack f') <=? c_max_stack c
      then MNext (with_frames s' (set_frame top f' :: rest))
      else MStuck "operand stack overflow (max_stack)" in
  match fetch (c_instrs c) (f_pc f) (c_length c) with
  | None => MStuck "no instruction at pc"
  | Some (i, nx) =>
    let go st' s' := put_top (mkframe nx st' lv) s' in
    if is_local_instr i then
      (* ---- the Phase 1 frame-local semantics ---- *)
      match step c (cf_rt top) f with
      | Normal f' => put_top f' s
      | Done v => if cf_clinit top then return_to s None rest else return_to s v rest
      | Throw cn => throw_new p s cn
      | Stuck why => MStuck why
      end
    else
    match i with
    (* ---- objects ---- *)
    | New cn =>
        if erroneous p 64 (ms_statics s) cn then throw_new p s "java/lang/NoClassDefFoundError" else
        match init_needed p 64 (ms_inited s) cn with
        | Some cf => start_init s cf
        | None =>
          match instance_fields p 64 cn with
          | Some fs => let (l, s') := alloc s (OObj cn fs) in go (VRef l :: st) s'
          | None => MStuck "new: class not loaded and not modelled"
          end
        end
    | Getfield fr =>
        match st with
        | VNull :: _ => throw_new p s NPE
        | VRef l :: r =>
            match h l with
            | Some (OObj _ fs) =>
                match assoc (fr_name fr) fs with
                | Some v => go (v :: r) s
                | None => MStuck "getfield: no such field"
                end
            | _ => MStuck "getfield: not an object"
            end
        | _ => MStuck "getfield: operand"
        end
    | Putfield fr =>
        match st, field_type (fr_desc fr) with
        | v :: VNull :: _, _ => throw_new p s NPE
        | v :: VRef l :: r, Some t =>
            if negb (value_fits t v) then MStuck "putfield: value type" else
            match h l with
            | Some (OObj cn fs) =>
                match set_assoc (fr_name fr) (narrow_store t v) fs with
                | Some fs' =>
                    go r {| ms_heap := upd h l (OObj cn fs'); ms_next := ms_next s;
                            ms_statics := ms_statics s; ms_inited := ms_inited s;
                            ms_locks := ms_locks s; ms_frames := ms_frames s |}
                | None => MStuck "putfield: no such field"
                end
            | _ => MStuck "putfield: not an object"
            end
        | _, _ => MStuck "putfield: operand"
        end
    | Getstatic fr =>
        if erroneous p 64 (ms_statics s) (fr_class fr) then throw_new p s "java/lang/NoClassDefFoundError" else
        match init_needed p 64 (ms_inited s) (fr_class fr) with
        | Some cf => start_init s cf
        | None =>
          match assoc (static_key (fr_class fr) (fr_name fr)) (ms_statics s) with
          | Some v => go (v :: st) s
          | None =>
              (* a static field of a JDK class: its model, as a pseudo-method "<get>name" *)
              match find_class p (fr_class fr) with
              | None => match mdl (fr_class fr) ("<get>" ++ fr_name fr) (fr_desc fr) nil s with
                        | MOk (Some v) s' => go (v :: st) (with_frames s' (ms_frames s))
                        | MThrow cn => throw_new p s cn
                        | MStuckModel why => MStuck why
                        | _ => MStuck ("no model for the static field " ++ fr_class fr ++ "." ++ fr_name fr)
                        end
              | Some _ => MStuck "getstatic: inherited static field (resolution through superclasses not modelled yet)"
              end
          end
        end
    | Putstatic fr =>
        if erroneous p 64 (ms_statics s) (fr_class fr) then throw_new p s "java/lang/NoClassDefFoundError" else
        match init_needed p 64 (ms_inited s) (fr_class fr) with
        | Some cf => start_init s cf
        | None =>
          match st, field_type (fr_desc fr) with
          | v :: r, Some t =>
              if negb (value_fits t v) then MStuck "putstatic: value type" else
              match set_assoc (static_key (fr_class fr) (fr_name fr)) (narrow_store t v) (ms_statics s) with
              | Some sts =>
                  go r {| ms_heap := h; ms_next := ms_next s; ms_statics := sts;
                          ms_inited := ms_inited s; ms_locks := ms_locks s; ms_frames := ms_frames s |}
              | None => MStuck "putstatic: field of a class that is not loaded"
              end
          | _, _ => MStuck "putstatic: operand"
          end
        end
    (* ---- arrays ---- *)
    | Newarray t =>
        match st, elem_of_atype t with
        | VInt n :: r, Some e =>
            if n <? 0 then throw_new p s "java/lang/NegativeArraySizeException"
            else if MAX_ARRAY <? n then MStuck "array larger than the model bound (OutOfMemoryError possible)"
            else let (l, s') := alloc s (OArr e (repeat (default_of e) (Z.to_nat n))) in go (VRef l :: r) s'
        | _, _ => MStuck "newarray: operand"
        end
    | Anewarray cn =>
        match st with
        | VInt n :: r =>
            if n <? 0 then throw_new p s "java/lang/NegativeArraySizeException"
            else if MAX_ARRAY <? n then MStuck "array larger than the model bound (OutOfMemoryError possible)"
            else let (l, s') := alloc s (OArr (class_type cn) (repeat VNull (Z.to_nat n))) in go (VRef l :: r) s'
        | _ => MStuck "anewarray: operand"
        end
    | Arraylength =>
        match st with
        | VNull :: _ => throw_new p s NPE
        | VRef l :: r =>
            match h l with
            | Some (OArr _ es) => go (VInt (Z.of_nat (length es)) :: r) s
            | _ => MStuck "arraylength: not an array"
            end
        | _ => MStuck "arraylength: operand"
        end
    | ALoadArr k =>
        match st with
        | VInt _ :: VNull :: _ => throw_new p s NPE
        | VInt idx :: VRef l :: r =>
            match h l with
            | Some (OArr e es) =>
                if negb (akind_load_ok k e) then MStuck "xaload: array kind" else
                if (idx <? 0) || (Z.of_nat (length es) <=? idx) then throw_new p s AIOOBE
                else match nth_z es idx with Some v => go (v :: r) s | None => MStuck "xaload" end
            | _ => MStuck "xaload: not an array"
            end
        | _ => MStuck "xaload: operand"
        end
    | AStoreArr k =>
        match st with
        | v :: VInt _ :: VNull :: _ => throw_new p s NPE
        | v :: VInt idx :: VRef l :: r =>
            match h l with
            | Some (OArr e es) =>
                if negb (akind_ok k e v) then MStuck "xastore: array kind" else
                if (idx <? 0) || (Z.of_nat (length es) <=? idx) then throw_new p s AIOOBE
                else
                  let store s := go r {| ms_heap := upd h l (OArr e (set_nth_z es idx (narrow_store e v)));
                                         ms_next := ms_next s; ms_statics := ms_statics s;
                                         ms_inited := ms_inited s; ms_locks := ms_locks s;
                                         ms_frames := ms_frames s |} in
                  match v with
                  | VRef vl =>
                      match h vl with
                      | Some o =>
                          match assignable p 64 (runtime_type o) (match e with TArr _ => type_desc e
                                                                         | TRef c => c | _ => "" end) with
                          | Some true => store s
                          | Some false => throw_new p s "java/lang/ArrayStoreException"
                          | None => MStuck "aastore: cannot decide the element type"
                          end
                      | None => MStuck "aastore: dangling reference"
                      end
                  | _ => store s
                  end
            | _ => MStuck "xastore: not an array"
            end
        | _ => MStuck "xastore: operand"
        end
    (* ---- exceptions ---- *)
    | Athrow =>
        match st with
        | VNull :: _ => throw_new p s NPE
        | VRef l :: _ => throw_obj p s l
        | _ => MStuck "athrow: operand"
        end
    (* ---- types ---- *)
    | Checkcast cn =>
        match st with
        | VNull :: _ => go st s
        | VRef l :: _ =>
            match h l with
            | Some o => match assignable p 64 (runtime_type o) cn with
                        | Some true => go st s
                        | Some false => throw_new p s "java/lang/ClassCastException"
                        | None => MStuck "checkcast: cannot decide"
                        end
            | None => MStuck "checkcast: dangling reference"
            end
        | _ => MStuck "checkcast: operand"
        end
    | Instanceof cn =>
        match st with
        | VNull :: r => go (VInt 0 :: r) s
        | VRef l :: r =>
            match h l with
            | Some o => match assignable p 64 (runtime_type o) cn with
                        | Some b => go (VInt (if b then 1 else 0) :: r) s
                        | None => MStuck "instanceof: cannot decide"
                        end
            | None => MStuck "instanceof: dangling reference"
            end
        | _ => MStuck "instanceof: operand"
        end
    (* ---- monitors (single thread: counts only) ---- *)
    | Monitorenter =>
        match st with
        | VNull :: _ => throw_new p s NPE
        | VRef l :: r =>
            go r {| ms_heap := h; ms_next := ms_next s; ms_statics := ms_statics s;
                    ms_inited := ms_inited s; ms_locks := (l, lock_count (ms_locks s) l + 1) :: ms_locks s;
                    ms_frames := ms_frames s |}
        | _ => MStuck "monitorenter: operand"
        end
    | Monitorexit =>
        match st with
        | VNull :: _ => throw_new p s NPE
        | VRef l :: r =>
            let n := lock_count (ms_locks s) l in
            if n <=? 0 then throw_new p s "java/lang/IllegalMonitorStateException"
            else go r {| ms_heap := h; ms_next := ms_next s; ms_statics := ms_statics s;
                         ms_inited := ms_inited s; ms_locks := (l, n - 1) :: ms_locks s;
                         ms_frames := ms_frames s |}
        | _ => MStuck "monitorexit: operand"
        end
    (* ---- calls ---- *)
    | Invoke k mr =>
        match parse_mdesc (mr_desc mr) with
        | None => MStuck "invoke: bad descriptor"
        | Some (ps, rt) =>
          let nargs := (length ps + (match k with InvStatic => 0 | _ => 1 end))%nat in
          match pop_n nargs st with
          | None => MStuck "invoke: operand stack"
          | Some (args, r) => do_invoke 8 p mdl s top rest k mr args r nx
          end
        end
    (* ---- String and Class constants (interned: one object per value) ---- *)
    | Ldc (LdcString raw) =>
        match utf8_units raw with
        | Some u => let (l, s') := intern s (OStr u) in go (VRef l :: st) s'
        | None => MStuck "ldc: malformed modified UTF-8"
        end
    | Ldc (LdcClass n) => let (l, s') := intern s (OCls n) in go (VRef l :: st) s'
    (* ---- invokedynamic: only javac's string concatenation (StringConcatFactory) ---- *)
    | Invokedynamic bi name desc =>
        match find_class p (cf_class top) with
        | None => MStuck "invokedynamic: class not loaded"
        | Some cf =>
          match concat_recipe cf bi, parse_mdesc desc with
          | Some (recipe, consts), Some (ps, _) =>
              match pop_n (length ps) st with
              | Some (args, r) =>
                  match concat_units h recipe consts ps args with
                  | inr u => let (l, s') := alloc s (OStr u) in go (VRef l :: r) s'
                  | inl why => MStuck why
                  end
              | None => MStuck "invokedynamic: operand stack"
              end
          | _, Some (ps, Some (TRef iface)) =>
              match lambda_site cf bi with
              | Some (kind, impl) =>
                  match pop_n (length ps) st with
                  | Some (cap, r) =>
                      let o := OLam iface name kind impl cap in
                      (* non-capturing lambdas are one object per call site *)
                      let (l, s') := match cap with
                                     | nil => let key := "#lam:" ++ cf_class top ++ "#" ++ intern_key (OStr (z_units bi)) in
                                              match assoc key (ms_statics s) with
                                              | Some (VRef l0) => (l0, s)
                                              | _ => let (l0, s0) := alloc s o in
                                                     (l0, {| ms_heap := ms_heap s0; ms_next := ms_next s0;
                                                             ms_statics := (key, VRef l0) :: ms_statics s0;
                                                             ms_inited := ms_inited s0; ms_locks := ms_locks s0;
                                                             ms_frames := ms_frames s0 |})
                                              end
                                     | _ => alloc s o
                                     end in
                      go (VRef l :: r) s'
                  | None => MStuck "invokedynamic: operand stack"
                  end
              | None => MStuck "invokedynamic: bootstrap method not modelled (only string concatenation and LambdaMetafactory.metafactory)"
              end
          | _, _ => MStuck "invokedynamic: bootstrap method not modelled"
          end
        end
    | Multianewarray cn dims =>
        match pop_n (Z.to_nat dims) st with
        | Some (counts, r) =>
            if negb (forallb (fun v => match v with VInt _ => true | _ => false end) counts)
            then MStuck "multianewarray: operand" else
            let ns := map (fun v => match v with VInt n => n | _ => 0 end) counts in
            if existsb (fun n => n <? 0) ns then throw_new p s "java/lang/NegativeArraySizeException"
            else if existsb (fun n => MAX_ARRAY <? n) ns || (MAX_ARRAY <? fold_left Z.mul ns 1)
            then MStuck "array larger than the model bound (OutOfMemoryError possible)"
            else match multi_alloc 256 s (class_type cn) ns with
                 | Some (l, s') => go (VRef l :: r) s'
                 | None => MStuck "multianewarray: type"
                 end
        | None => MStuck "multianewarray: operand stack"
        end
    | _ => MStuck "unreachable: frame-local instruction"
    end
  end
  end.

(** ** Runs *)
Inductive mresult : Type :=
| MRValue (v : option value) (s : mstate)
| MRExc (exn : Z) (s : mstate)
| MRStuck (why : string)
| MROutOfFuel.

Fixpoint mrun (p : program) (mdl : model) (fuel : nat) (s : mstate) : mresult :=
  match fuel with
  | O => MROutOfFuel
  | S n =>
    match mstep_of p mdl s with
    | MNext s' => mrun p mdl n s'
    | MReturn v s' => MRValue v s'
    | MUncaught e s' => MRExc e s'
    | MStuck w => MRStuck w
    end
  end.

Lemma mrun_mono : forall p mdl n s r,
  mrun p mdl n s = r -> r <> MROutOfFuel -> forall m, (n <= m)%nat -> mrun p mdl m s = r.
Proof.
  induction n as [|n IH]; intros s r H Hr m Hm.
  - simpl in H. subst. congruence.
  - destruct m as [|m]; [lia|]. simpl in *.
    destruct (mstep_of p mdl s); auto. eapply IH; eauto; lia.
Qed.

(** ** Entry: call a static method of a loaded class from "outside", as
    [Method.invoke] does: a synthetic caller frame loads the arguments and
    executes [invokestatic], so class initialisation happens exactly as for a
    call from bytecode. *)
Definition kind_of_jtype (t : jtype) : tkind :=
  match t with
  | TLong => KL | TFloat => KF | TDouble => KD | TRef _ | TArr _ => KA | _ => KI
  end.

Fixpoint load_args (ps : list jtype) (slot : Z) (p : pc) : list (pc * instr) * pc :=
  match ps with
  | nil => (nil, p)
  | t :: r => let (ins, p') := load_args r (slot + Z.of_nat (jtype_size t)) (p + 1) in
              ((p, Load (kind_of_jtype t) slot) :: ins, p')
  end.

Definition entry_state (cls name desc : string) (args : list value) : option mstate :=
  match parse_mdesc desc with
  | None => None
  | Some (ps, rt) =>
    let (loads, p1) := load_args ps 0 0 in
    let ret := match rt with None => Return None | Some t => Return (Some (kind_of_jtype t)) end in
    let instrs := app loads [(p1, Invoke InvStatic {| mr_class := cls; mr_name := name; mr_desc := desc;
                                                     mr_interface := false |});
                            (p1 + 3, ret)] in
    let nslots := Z.of_nat (length (layout args)) in
    let c := {| c_max_stack := nslots + 2; c_max_locals := nslots; c_length := p1 + 4;
                c_instrs := instrs; c_handlers := nil |} in
    let m := {| m_name := "<entry>"; m_desc := desc; m_access := 8; m_code := Some c |} in
    match init_frame c args with
    | None => None
    | Some f =>
      Some {| ms_heap := fun _ => None; ms_next := 1; ms_statics := nil; ms_inited := nil;
              ms_locks := nil;
              ms_frames := [{| cf_class := "<entry>"; cf_method := m; cf_code := c; cf_rt := rt;
                               cf_frame := f; cf_resume := None; cf_clinit := false |}] |}
    end
  end.

Definition call_static (p : program) (mdl : model) (fuel : nat) (cls name desc : string)
                       (args : list value) : mresult :=
  match entry_state cls name desc args with
  | Some s => mrun p mdl fuel s
  | None => MRStuck "entry: bad descriptor or arguments"
  end.

(** Class name of an uncaught exception (for the differential harness). *)
Definition exn_class (s : mstate) (l : Z) : string :=
  match ms_heap s l with
  | Some (OObj c _) => c | Some (OArr _ _) => "<array>" | Some (OStr _) => "java/lang/String"
  | Some (OSb _) => "java/lang/StringBuilder" | Some (OCls _) => "java/lang/Class"
  | Some (OLam i _ _ _ _) => i | None => "<dangling>"
  end.

Definition load_program (files : list (list Z)) : option program :=
  map_opt parse_class files.
