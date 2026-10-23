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
From JVM.Core Require Import Int Instr Desc Semantics JdkTables.
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
  else if String.eqb c "java/lang/IncompatibleClassChangeError" then Some (Some "java/lang/LinkageError")
  else if String.eqb c "java/lang/AbstractMethodError" || String.eqb c "java/lang/NoSuchFieldError"
          || String.eqb c "java/lang/NoSuchMethodError" || String.eqb c "java/lang/IllegalAccessError"
       then Some (Some "java/lang/IncompatibleClassChangeError")
  else if String.eqb c "java/lang/MatchException" then RE
  else if String.eqb c "java/lang/Record" then Some (Some "java/lang/Object")
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

(** ** Access flags, packages, and a uniform view of loaded and JDK classes *)
Definition acc_public (a : Z) : bool := Z.testbit a 0.
Definition acc_private (a : Z) : bool := Z.testbit a 1.
Definition acc_protected (a : Z) : bool := Z.testbit a 2.
Definition acc_static (a : Z) : bool := Z.testbit a 3.
Definition acc_native (a : Z) : bool := Z.testbit a 8.
Definition acc_interface (a : Z) : bool := Z.testbit a 9.
Definition acc_abstract (a : Z) : bool := Z.testbit a 10.

Fixpoint last_slash (s : string) (i : nat) (best : option nat) : option nat :=
  match s with
  | EmptyString => best
  | String ch r => last_slash r (S i) (if Ascii.eqb ch "/"%char then Some i else best)
  end.
(** The run-time package of a class (one class loader: the package name). *)
Definition package_of (c : string) : string :=
  match last_slash c 0 None with Some n => substring 0 n c | None => "" end.

(** What the machine knows about a class: a loaded class file, an entry of the
    generated JDK table ([JdkTables.v]), or nothing. *)
Inductive cinfo : Type := CILoaded (cf : classfile) | CIJdk (j : jinfo) | CIUnknown.

Definition class_info (p : program) (c : string) : cinfo :=
  match find_class p c with
  | Some cf => CILoaded cf
  | None => match jdk_info c with Some j => CIJdk j | None => CIUnknown end
  end.

Definition ci_iface (ci : cinfo) : bool :=
  match ci with CILoaded cf => acc_interface (cf_access cf) | CIJdk j => acc_interface (ji_access j) | CIUnknown => false end.
Definition ci_super (ci : cinfo) : option string :=
  match ci with CILoaded cf => cf_super cf | CIJdk j => ji_super j | CIUnknown => None end.
Definition ci_ifaces (ci : cinfo) : list string :=
  match ci with CILoaded cf => cf_interfaces cf | CIJdk j => ji_ifaces j | CIUnknown => nil end.

Fixpoint jfind (name desc : string) (l : list (string * string * Z)) : option Z :=
  match l with
  | nil => None
  | (n, d, a) :: r => if String.eqb n name && String.eqb d desc then Some a else jfind name desc r
  end.

(** The method [name desc] declared by a class: its access flags and, for a
    loaded class, the method itself. *)
Definition ci_method (ci : cinfo) (name desc : string) : option (Z * option method) :=
  match ci with
  | CILoaded cf => option_map (fun m => (m_access m, Some m)) (find_method cf name desc)
  | CIJdk j => option_map (fun a => (a, None)) (jfind name desc (ji_methods j))
  | CIUnknown => None
  end.

Fixpoint mb_find (name desc : string) (l : list member) : option Z :=
  match l with
  | nil => None
  | m :: r => if String.eqb (mb_name m) name && String.eqb (mb_desc m) desc then Some (mb_access m)
              else mb_find name desc r
  end.

Definition ci_field (ci : cinfo) (name desc : string) : option Z :=
  match ci with
  | CILoaded cf => mb_find name desc (cf_fields cf)
  | CIJdk j => jfind name desc (ji_fields j)
  | CIUnknown => None
  end.

(** No two fields of a class share a name (javac never emits that; the field
    store is keyed by name, so such a class is not supported). *)
Fixpoint names_distinct (l : list string) : bool :=
  match l with nil => true | x :: r => negb (existsb (String.eqb x) r) && names_distinct r end.
Definition fields_ok (cf : classfile) : bool := names_distinct (map mb_name (cf_fields cf)).

(** ** Instance fields.
    An object stores its fields in one list, most derived class first.  A field
    is keyed by its plain name, except a field that is shadowed in the object's
    class by a field of the same name declared in a subclass: that one is keyed
    "<DeclaringClass>.<name>" (field names cannot contain '.', JVMS 4.2.2). *)
Fixpoint raw_fields (p : program) (fuel : nat) (c : string) : option (list (string * string * value)) :=
  match fuel with
  | O => None
  | S k =>
    match find_class p c with
    | None =>
        if String.eqb c "java/lang/Enum" then Some [(c, "name", VNull); (c, "ordinal", VInt 0)]
        else match builtin_super c with Some _ => Some nil | None => None end
    | Some cf =>
      if negb (fields_ok cf) then None else
      let own := fold_right (fun m acc =>
                   match acc with
                   | None => None
                   | Some l => if is_static_member m then Some l else
                               match field_type (mb_desc m) with
                               | Some t => Some ((c, mb_name m, default_of t) :: l)
                               | None => None
                               end
                   end) (Some nil) (cf_fields cf) in
      match own, cf_super cf with
      | Some l, Some s => option_map (fun l' => app l l') (raw_fields p k s)
      | Some l, None => Some l
      | None, _ => None
      end
    end
  end.

Fixpoint key_fields (seen : list string) (l : list (string * string * value)) : list (string * value) :=
  match l with
  | nil => nil
  | (d, x, v) :: r =>
      ((if existsb (String.eqb x) seen then d ++ "." ++ x else x), v) :: key_fields (x :: seen) r
  end.

(** Instance fields of [c] and its superclasses with default values. *)
Definition instance_fields (p : program) (fuel : nat) (c : string) : option (list (string * value)) :=
  option_map (key_fields nil) (raw_fields p fuel c).

(** The key of the field [x] declared by [d] in an object with fields [fs]. *)
Definition own_key (d x : string) (fs : list (string * value)) : string :=
  let q := d ++ "." ++ x in
  if existsb (fun kv => String.eqb q (fst kv)) fs then q else x.

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

(** Initialisation of a class or interface [c] (JVMS 5.5, single thread).
    Step 6 marks [c] as being initialised and sets its ConstantValue fields;
    step 7 then initialises the superclass (recursively: its steps 6 and 7
    happen at once, before any code runs), then the superinterfaces that
    declare a non-abstract, non-static method, then step 9 runs <clinit>.
    So all classes of the superclass chain whose initialisation has not
    started are marked first, and their <clinit> frames are pushed outermost
    on top.  A frame at pc -1 has not started yet: before its <clinit> runs it
    initialises its superinterfaces ([clinit_prepare]); an exception passing
    through it marks its class erroneous (step 7) and is rethrown as is (it is
    an Error: ExceptionInInitializerError or NoClassDefFoundError). *)
Fixpoint uninit_chain (p : program) (fuel : nat) (inited : list string) (c : string) : list classfile :=
  match fuel with
  | O => nil
  | S k =>
    match find_class p c with
    | None => nil
    | Some cf => if existsb (String.eqb c) inited then nil
                 else cf :: match cf_super cf with Some s => uninit_chain p k inited s | None => nil end
    end
  end.

(** Superinterfaces in the order of JVMS 5.5 step 7: for each direct
    superinterface, its own superinterfaces first, then itself. *)
Fixpoint iface_init_order (p : program) (fuel : nat) (ifs : list string) : list string :=
  match fuel with
  | O => nil
  | S k =>
    match ifs with
    | nil => nil
    | i :: r => app (match find_class p i with
                     | Some cf => app (iface_init_order p k (cf_interfaces cf)) [i]
                     | None => nil
                     end) (iface_init_order p k r)
    end
  end.

Definition has_instance_body (cf : classfile) : bool :=
  existsb (fun m => negb (acc_abstract (m_access m)) && negb (acc_static (m_access m))) (cf_methods cf).

(** Loaded superinterfaces that step 7 initialises (JDK interfaces are never
    initialised by the machine, like JDK classes). *)
Definition init_ifaces (p : program) (cf : classfile) : list string :=
  if acc_interface (cf_access cf) then nil else
  filter (fun i => match find_class p i with Some icf => has_instance_body icf | None => false end)
         (iface_init_order p 64 (cf_interfaces cf)).

Definition empty_clinit_code : code :=
  {| c_max_stack := 0; c_max_locals := 0; c_length := 1; c_instrs := [(0, Return None)]; c_handlers := nil |}.
Definition empty_clinit : method :=
  {| m_name := "<clinit>"; m_desc := "()V"; m_access := 8; m_code := Some empty_clinit_code |}.

Definition mark_inited (s : mstate) (c : string) : mstate :=
  {| ms_heap := ms_heap s; ms_next := ms_next s; ms_statics := ms_statics s;
     ms_inited := c :: ms_inited s; ms_locks := ms_locks s; ms_frames := ms_frames s |}.

Definition clinit_of (cf : classfile) : option (option (method * code)) :=
  match find_method cf "<clinit>" "()V" with
  | Some m => match m_code m with Some c => Some (Some (m, c)) | None => None end
  | None => Some None
  end.

Definition pending_frame (cf : classfile) (m : method) (c : code) (at_pc : Z) : cframe :=
  {| cf_class := cf_this cf; cf_method := m; cf_code := c; cf_rt := None;
     cf_frame := mkframe at_pc nil (repeat VTop (Z.to_nat (c_max_locals c)));
     cf_resume := None; cf_clinit := true |}.

(** Steps 6 for each class of the chain (outermost first) and the frames to
    push (outermost first).  A class without <clinit> and without
    superinterfaces to initialise needs no frame; the outermost frame starts
    at pc 0 when it has no superinterfaces to initialise. *)
Fixpoint start_chain (p : program) (s : mstate) (outermost : bool) (cfs : list classfile)
  : option (mstate * list cframe) :=
  match cfs with
  | nil => Some (s, nil)
  | cf :: r =>
    match static_inits cf, clinit_of cf, fields_ok cf with
    | Some sts, Some cl, true =>
      let s1 := mark_inited (put_statics s sts) (cf_this cf) in
      let prep := match init_ifaces p cf with nil => false | _ => true end in
      let fr := match cl with
                | Some (m, c) => Some (pending_frame cf m c (if outermost && negb prep then 0 else -1))
                | None => if prep then Some (pending_frame cf empty_clinit empty_clinit_code (-1)) else None
                end in
      match start_chain p s1 false r with
      | Some (s2, frs) => Some (s2, match fr with Some f => f :: frs | None => frs end)
      | None => None
      end
    | _, _, _ => None
    end
  end.

Definition init_class (p : program) (s : mstate) (c : string) : mstep :=
  match ms_frames s with
  | nil => MStuck "no frame"
  | top :: rest =>
    match start_chain p s true (rev (uninit_chain p 64 (ms_inited s) c)) with
    | Some (s1, frs) => MNext (with_frames s1 (app frs (set_resume top None :: rest)))
    | None => MStuck "class initialisation: static field initial value, <clinit> without code, or two fields with one name"
    end
  end.

(** A pending <clinit> frame (pc -1) of a class: initialise the next
    superinterface of step 7 that has not been initialised (an erroneous one
    throws NoClassDefFoundError), else start the <clinit> code at pc 0. *)
Definition clinit_prepare (p : program) (s : mstate) (top : cframe) (rest : list cframe) : mstep :=
  match find_class p (cf_class top) with
  | None => MStuck "pending <clinit> of a class that is not loaded"
  | Some cf =>
    let todo := filter (fun i => negb (existsb (String.eqb i) (ms_inited s)) || erroneous p 64 (ms_statics s) i)
                       (init_ifaces p cf) in
    match todo with
    | nil => MNext (with_frames s (set_frame top (mkframe 0 nil (f_locals (cf_frame top))) :: rest))
    | i :: _ => if erroneous p 64 (ms_statics s) i then throw_new p s "java/lang/NoClassDefFoundError"
                else init_class p s i
    end
  end.

(** ** Hierarchy walks over loaded classes and the JDK table *)

(** [c] and its superclasses; [None] if a class is unknown. *)
Fixpoint class_chain (p : program) (fuel : nat) (c : string) : option (list string) :=
  match fuel with
  | O => None
  | S k =>
    match class_info p c with
    | CIUnknown => None
    | ci => match ci_super ci with
            | Some s => option_map (cons c) (class_chain p k s)
            | None => Some [c]
            end
    end
  end.

(** All interfaces reachable from [todo] (each once); [None] if one is unknown. *)
Fixpoint iface_closure (p : program) (fuel : nat) (todo acc : list string) : option (list string) :=
  match fuel with
  | O => None
  | S k =>
    match todo with
    | nil => Some (rev acc)
    | i :: r =>
      if existsb (String.eqb i) acc then iface_closure p k r acc else
      match class_info p i with
      | CIUnknown => None
      | ci => iface_closure p k (app (ci_ifaces ci) r) (i :: acc)
      end
    end
  end.

(** The superinterfaces (direct and indirect) of a class or interface. *)
Definition superifaces (p : program) (c : string) : option (list string) :=
  match class_chain p 64 c with
  | Some ch => iface_closure p 1024 (flat_map (fun x => ci_ifaces (class_info p x)) ch) nil
  | None => None
  end.

(** [j] is a proper subinterface of [i]. *)
Definition sub_iface (p : program) (j i : string) : bool :=
  match iface_closure p 1024 (ci_ifaces (class_info p j)) nil with
  | Some l => existsb (String.eqb i) l
  | None => false
  end.

Definition mdecl : Type := (string * Z * option method)%type.   (** declaring class, access, method *)
Definition md_class (d : mdecl) : string := match d with (c, _, _) => c end.
Definition md_acc (d : mdecl) : Z := match d with (_, a, _) => a end.

(** The maximally-specific superinterface methods of [c] for [name desc]
    (JVMS 5.4.3.3); [None] if the superinterfaces are not all known. *)
Definition max_specific (p : program) (c name desc : string) : option (list mdecl) :=
  match superifaces p c with
  | None => None
  | Some ifs =>
    let cands := flat_map (fun i => match ci_method (class_info p i) name desc with
                                    | Some (a, om) => if acc_private a || acc_static a then nil else [(i, a, om)]
                                    | None => nil
                                    end) ifs in
    Some (filter (fun d => negb (existsb (fun d' => negb (String.eqb (md_class d') (md_class d))
                                                    && sub_iface p (md_class d') (md_class d)) cands)) cands)
  end.

Definition non_abstract (l : list mdecl) : list mdecl := filter (fun d => negb (acc_abstract (md_acc d))) l.

(** Lookup of a declaration along the superclass chain. *)
Inductive clook : Type := CLFound (d : mdecl) | CLEnd | CLUnknown.

(** Method resolution step 2 (JVMS 5.4.3.3): the first declaration of
    [name desc] in [c] or a superclass (any access; [inst] = instance methods only). *)
Fixpoint chain_lookup (p : program) (fuel : nat) (c name desc : string) (inst : bool) : clook :=
  match fuel with
  | O => CLUnknown
  | S k =>
    match class_info p c with
    | CIUnknown => CLUnknown
    | ci =>
      let cont := match ci_super ci with Some s => chain_lookup p k s name desc inst | None => CLEnd end in
      match ci_method ci name desc with
      | Some (a, om) => if inst && acc_static a then cont else CLFound (c, a, om)
      | None => cont
      end
    end
  end.

(** Declarations of [name desc] in the loaded part of the hierarchy of [c]
    (superclasses and superinterfaces). *)
Fixpoint loaded_chain (p : program) (fuel : nat) (c : string) : list classfile :=
  match fuel with
  | O => nil
  | S k => match find_class p c with
           | Some cf => cf :: match cf_super cf with Some s => loaded_chain p k s | None => nil end
           | None => nil
           end
  end.

Fixpoint loaded_ifaces (p : program) (fuel : nat) (todo acc : list string) : list string :=
  match fuel with
  | O => rev acc
  | S k =>
    match todo with
    | nil => rev acc
    | i :: r => if existsb (String.eqb i) acc then loaded_ifaces p k r acc else
                match find_class p i with
                | Some cf => loaded_ifaces p k (app (cf_interfaces cf) r) (i :: acc)
                | None => loaded_ifaces p k r acc
                end
    end
  end.

Definition hier_decls (p : program) (c name desc : string) : list mdecl :=
  let ch := loaded_chain p 64 c in
  let ifs := loaded_ifaces p 1024 (flat_map cf_interfaces ch) nil in
  flat_map (fun x => match find_class p x with
                     | Some cf => match find_method cf name desc with
                                  | Some m => [(x, m_access m, Some m)]
                                  | None => nil
                                  end
                     | None => nil
                     end) (app (map cf_this ch) ifs).

(** Package-private declarations of one name/descriptor in several packages
    make overriding depend on the resolved method (JVMS 5.4.5). *)
Definition package_ok (ds : list mdecl) : bool :=
  match filter (fun d => negb (acc_public (md_acc d) || acc_protected (md_acc d) || acc_private (md_acc d))) ds with
  | nil => true
  | d0 :: _ => forallb (fun d => String.eqb (package_of (md_class d)) (package_of (md_class d0))) ds
  end.

(** ** [resolve_full p c name desc]: the method a call of [name desc] on an
    object of class [c] (invokevirtual / invokeinterface, JVMS 5.4.6), or a
    call through [c] by invokestatic / invokespecial, enters, when that method
    does not depend on more than [c], [name] and [desc]:
    - constructors: the one declared by [c];
    - if the hierarchy declares a private [name desc] (private methods are
      selected only as the resolved method, JVMS 5.4.6 step 1), only when it
      is the only declaration of [name desc] in the hierarchy;
    - otherwise the first declaration on the superclass chain (step 2), if it
      is not abstract and no package-private declaration in another package
      can change what overrides what (JVMS 5.4.5);
    - otherwise the only non-abstract maximally-specific superinterface
      method (step 3).
    [None] in every other case (JDK classes, abstract methods, conflicts): the
    caller then asks the JDK model, and else performs full resolution and
    selection ([select_virtual], [select_special], [resolve_method]).
    Assumption (javac output): the declaration found in the receiver's class
    hierarchy is an instance method when the instruction is invokevirtual or
    invokeinterface (resolution of a static method there would throw
    IncompatibleClassChangeError; javac never emits it). *)
Definition resolve_full (p : program) (c name desc : string) : option (string * method) :=
  match find_class p c with
  | None => None
  | Some cf =>
    if String.eqb name "<init>" then option_map (fun m => (c, m)) (find_method cf name desc) else
    let ds := hier_decls p c name desc in
    if existsb (fun d => acc_private (md_acc d)) ds then
      match ds with
      | [(d, _, Some m)] => Some (d, m)
      | _ => None
      end
    else
      match chain_lookup p 64 c name desc false with
      | CLFound (d, a, Some m) => if acc_abstract a || negb (package_ok ds) then None else Some (d, m)
      | CLFound (_, _, None) | CLUnknown => None
      | CLEnd =>
          match max_specific p c name desc with
          | Some ms => match non_abstract ms with
                       | [(d, _, Some m)] => Some (d, m)
                       | _ => None
                       end
          | None => None
          end
      end
  end.

(** ** Full method resolution (JVMS 5.4.3.3 for Methodref, 5.4.3.4 for InterfaceMethodref). *)
Inductive rres : Type := RFound (d : mdecl) | RThrow (exc : string) | RUnknown.

Definition ICCE := "java/lang/IncompatibleClassChangeError".
Definition AME := "java/lang/AbstractMethodError".
Definition NSME := "java/lang/NoSuchMethodError".
Definition NSFE := "java/lang/NoSuchFieldError".
Definition IAE := "java/lang/IllegalAccessError".

Definition resolve_method (p : program) (imr : bool) (c name desc : string) : rres :=
  match class_info p c with
  | CIUnknown => RUnknown
  | ci =>
    if negb (Bool.eqb (ci_iface ci) imr) then RThrow ICCE else
    let step2 :=
      if imr then
        match ci_method ci name desc with
        | Some (a, om) => CLFound (c, a, om)
        | None => match ci_method (class_info p "java/lang/Object") name desc with
                  | Some (a, om) => if acc_public a && negb (acc_static a)
                                    then CLFound ("java/lang/Object", a, om) else CLEnd
                  | None => CLEnd
                  end
        end
      else chain_lookup p 64 c name desc false in
    match step2 with
    | CLFound d => RFound d
    | CLUnknown => RUnknown
    | CLEnd =>
        match max_specific p c name desc with
        | None => RUnknown
        | Some ms => match non_abstract ms with
                     | [d] => RFound d
                     | _ => match ms with d :: _ => RFound d | nil => RThrow NSME end
                     end
        end
    end
  end.

(** [mC] declared in [dC] can override [mA] declared in [dA] (JVMS 5.4.5),
    [dC] a subclass of [dA]; [between] = the classes strictly between them. *)
Fixpoint can_override_go (p : program) (fuel : nat) (name desc : string) (between : list string)
         (dC : string) (aC : Z) (dA : string) (aA : Z) : bool :=
  negb (acc_private aC) &&
  (acc_public aA || acc_protected aA || String.eqb (package_of dC) (package_of dA) ||
   match fuel with
   | O => false
   | S k =>
     (fix tr (bs : list string) (before : list string) : bool :=
        match bs with
        | nil => false
        | b :: r =>
          match ci_method (class_info p b) name desc with
          | Some (aB, _) => (negb (acc_static aB) && can_override_go p k name desc (rev before) dC aC b aB
                             && can_override_go p k name desc r b aB dA aA) || tr r (b :: before)
          | None => tr r (b :: before)
          end
        end) between nil
   end).

Fixpoint take_until (x : string) (l : list string) : list string :=
  match l with nil => nil | y :: r => if String.eqb x y then nil else y :: take_until x r end.

(** Selection (JVMS 5.4.6) of an instance method that can override the resolved method [mR] from the superclass chain [cs]. *)
Fixpoint select_chain (p : program) (cs : list string) (name desc : string) (dR : string) (aR : Z) : clook :=
  match cs with
  | nil => CLEnd
  | k :: r =>
    match class_info p k with
    | CIUnknown => CLUnknown
    | ci =>
      match ci_method ci name desc with
      | Some (a, om) =>
          if negb (acc_static a) && can_override_go p 8 name desc (take_until dR r) k a dR aR
          then CLFound (k, a, om) else select_chain p r name desc dR aR
      | None => select_chain p r name desc dR aR
      end
    end
  end.

(** Outcome of a full selection. *)
Inductive sel : Type := SelEnter (d : string) (m : method) | SelModel (d : string) | SelThrow (exc : string)
                      | SelStuck (why : string) | SelUnknown.

Definition sel_of (d : mdecl) : sel :=
  match d with (c, _, Some m) => SelEnter c m | (c, _, None) => SelModel c end.

(** invokevirtual / invokeinterface: resolution of [mr], then selection on the receiver's class [rc]. *)
Definition select_virtual (p : program) (itf : bool) (mr : methodref) (rc : string) : sel :=
  match resolve_method p (mr_interface mr) (mr_class mr) (mr_name mr) (mr_desc mr) with
  | RUnknown => SelUnknown
  | RThrow e => SelThrow e
  | RFound (dR, aR, omR) =>
    if acc_static aR then SelThrow ICCE else
    match (if itf then subclass p 64 rc (mr_class mr) else Some true) with
    | None => SelUnknown
    | Some false => SelThrow ICCE
    | Some true =>
      let finish (d : mdecl) :=
        if acc_abstract (md_acc d) then SelThrow AME
        else if itf && negb (acc_public (md_acc d) || acc_private (md_acc d)) then SelThrow IAE
        else sel_of d in
      if acc_private aR then sel_of (dR, aR, omR) else
      match class_chain p 64 rc with
      | None => SelUnknown
      | Some cs =>
        match select_chain p cs (mr_name mr) (mr_desc mr) dR aR with
        | CLFound d => finish d
        | CLUnknown => SelUnknown
        | CLEnd =>
            match max_specific p rc (mr_name mr) (mr_desc mr) with
            | None => SelUnknown
            | Some ms => match non_abstract ms with
                         | [d] => finish d
                         | nil => SelThrow AME
                         | _ => if itf
                                then SelStuck "invokeinterface with several maximally-specific default methods: JVMS 6.5 says IncompatibleClassChangeError, HotSpot 21 throws AbstractMethodError"
                                else SelThrow ICCE
                         end
            end
        end
      end
    end
  end.

(** invokespecial (JVMS 6.5): resolution, then the lookup from the direct
    superclass of the current class [cur] (super calls) or from the referenced class. *)
Definition select_special (p : program) (cur : string) (mr : methodref) : sel :=
  let name := mr_name mr in
  let desc := mr_desc mr in
  match resolve_method p (mr_interface mr) (mr_class mr) name desc with
  | RUnknown => SelUnknown
  | RThrow e => SelThrow e
  | RFound (dR, aR, _) =>
    if String.eqb name "<init>" && negb (String.eqb dR (mr_class mr)) then SelThrow NSME else
    if acc_static aR then SelThrow ICCE else
    let cur_super := match class_info p cur with CILoaded cf => cf_super cf | _ => None end in
    let is_super := match class_chain p 64 cur with
                    | Some (_ :: sups) => existsb (String.eqb (mr_class mr)) sups
                    | _ => false
                    end in
    let c := match cur_super with
             | Some sc => if negb (String.eqb name "<init>") && negb (mr_interface mr) && is_super then sc
                          else mr_class mr
             | None => mr_class mr
             end in
    let ci := class_info p c in
    let found :=
      if ci_iface ci then
        match ci_method ci name desc with
        | Some (a, om) => if acc_static a then CLEnd else CLFound (c, a, om)
        | None => match ci_method (class_info p "java/lang/Object") name desc with
                  | Some (a, om) => if acc_public a && negb (acc_static a)
                                    then CLFound ("java/lang/Object", a, om) else CLEnd
                  | None => CLEnd
                  end
        end
      else chain_lookup p 64 c name desc true in
    match found with
    | CLFound d => if acc_abstract (md_acc d) then SelThrow AME else sel_of d
    | CLUnknown => SelUnknown
    | CLEnd =>
        match max_specific p c name desc with
        | None => SelUnknown
        | Some ms => match non_abstract ms with
                     | [d] => sel_of d
                     | nil => SelThrow AME
                     | _ => SelThrow ICCE
                     end
        end
    end
  end.

(** ** Field resolution (JVMS 5.4.3.2): [c], then its superinterfaces, then its superclass. *)
Inductive fres : Type := FFound (d : string) (acc : Z) | FNotFound | FUnknown.

Fixpoint field_lookup (p : program) (fuel : nat) (c name desc : string) : fres :=
  match fuel with
  | O => FUnknown
  | S k =>
    match class_info p c with
    | CIUnknown => FUnknown
    | ci =>
      match ci_field ci name desc with
      | Some a => FFound c a
      | None =>
        let fix ifs (l : list string) : fres :=
          match l with
          | nil => FNotFound
          | i :: r => match field_lookup p k i name desc with
                      | FNotFound => ifs r
                      | x => x
                      end
          end in
        match ifs (ci_ifaces ci) with
        | FNotFound => match ci_super ci with
                       | Some s => field_lookup p k s name desc
                       | None => FNotFound
                       end
        | x => x
        end
      end
    end
  end.

Definition resolve_field (p : program) (fr : fieldref) : fres :=
  field_lookup p 64 (fr_class fr) (fr_name fr) (fr_desc fr).

(** The key of the instance field [fr] in an object with fields [fs]: its plain
    name unless the object stores a shadowed field of that name, in which case
    the field is resolved (JVMS 5.4.3.2) and keyed by its declaring class
    (see [instance_fields]).  Assumption (javac output): a field whose name is
    stored once in the object is the field the reference resolves to. *)
Inductive fslot : Type := FSKey (k : string) | FSThrow (exc : string) | FSStuck (why : string).

Definition qual_of (x k : string) : bool :=
  let n := String.length x in
  let m := String.length k in
  (S n <? m)%nat && String.eqb (substring (m - S n) (S n) k) (String "."%char x).

Definition field_slot (p : program) (fr : fieldref) (fs : list (string * value)) : fslot :=
  if existsb (fun kv => qual_of (fr_name fr) (fst kv)) fs then
    match resolve_field p fr with
    | FFound d a => if acc_static a then FSThrow ICCE else FSKey (own_key d (fr_name fr) fs)
    | FNotFound => FSThrow NSFE
    | FUnknown => FSStuck "field resolution reaches a class the machine does not know"
    end
  else FSKey (fr_name fr).

Definition obj_get (p : program) (fr : fieldref) (fs : list (string * value)) : option value :=
  match field_slot p fr fs with FSKey k => assoc k fs | _ => None end.
Definition obj_set (p : program) (fr : fieldref) (v : value) (fs : list (string * value))
  : option (list (string * value)) :=
  match field_slot p fr fs with FSKey k => set_assoc k v fs | _ => None end.

(** Static field access: the key in [ms_statics] of the field, or what to do first. *)
Inductive starget : Type := STKey (k : string) | STInit (d : string) | STThrow (exc : string)
                          | STJdk (d : string) | STStuck (why : string).

(** Fast path: the referenced class declares the field (its key exists exactly
    when its initialisation has started and it declares a static field of that
    name) and is initialised and not erroneous.  Otherwise the field is
    resolved and its declaring class is initialised (JVMS 6.5 getstatic,
    5.5): a static field inherited from a superclass or superinterface does
    not initialise the referenced class. *)
Definition static_target (p : program) (s : mstate) (fr : fieldref) : starget :=
  let c := fr_class fr in
  let k0 := static_key c (fr_name fr) in
  if negb (erroneous p 64 (ms_statics s) c)
     && match init_needed p 64 (ms_inited s) c with None => true | Some _ => false end
     && match assoc k0 (ms_statics s) with Some _ => true | None => false end
  then STKey k0 else
  match resolve_field p fr with
  | FFound d a =>
      if negb (acc_static a) then STThrow ICCE
      else if erroneous p 64 (ms_statics s) d then STThrow "java/lang/NoClassDefFoundError"
      else match init_needed p 64 (ms_inited s) d with
           | Some _ => STInit d
           | None => match find_class p d with
                     | Some _ => STKey (static_key d (fr_name fr))
                     | None => STJdk d
                     end
           end
  | FNotFound => STThrow NSFE
  | FUnknown => match find_class p c with
                | None => STJdk c
                | Some _ => STStuck "static field resolution reaches a class the machine does not know"
                end
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
          (* the model of the first JDK class on the receiver's superclass chain
             (e.g. java/lang/Enum for an enum); else full resolution and
             selection (JVMS 5.4.3.3/5.4.3.4, 5.4.6, invokespecial 6.5); when
             that reaches classes the machine does not know, the model of the
             method as declared *)
          let jc := first_unloaded p 64 cn0 in
          match mdl jc (mr_name mr) (mr_desc mr) args s with
          | MNoModel =>
              let sl := match k with
                        | InvSpecial => select_special p (cf_class top) mr
                        | InvInterface => select_virtual p true mr cn0
                        | _ => select_virtual p false mr cn0
                        end in
              match sl with
              | SelEnter d m => if Z.testbit (m_access m) 8 then invoke_run_model p mdl s top rest mr args r nx d
                                else enter s caller rest d m args nx
              | SelModel d => invoke_run_model p mdl s top rest mr args r nx d
              | SelThrow e =>
                  (* a loaded model class of a JDK class may leave a method to the Rocq model *)
                  match mdl (mr_class mr) (mr_name mr) (mr_desc mr) args s with
                  | MNoModel => throw_new p s e
                  | _ => invoke_run_model p mdl s top rest mr args r nx (mr_class mr)
                  end
              | SelStuck why => MStuck why
              | SelUnknown => invoke_run_model p mdl s top rest mr args r nx (mr_class mr)
              end
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
      (* JVMS 6.5 invokestatic: resolve, then initialise the class that
         declares the resolved method.  Fast path: the referenced class is
         initialised (so are its superclasses, where a static method found by
         resolution is declared). *)
      let slow :=
        match resolve_method p (mr_interface mr) (mr_class mr) (mr_name mr) (mr_desc mr) with
        | RFound (d, a, om) =>
            if negb (acc_static a) then throw_new p s ICCE
            else if erroneous p 64 (ms_statics s) d then throw_new p s "java/lang/NoClassDefFoundError"
            else match init_needed p 64 (ms_inited s) d with
                 | Some _ => init_class p s d
                 | None => match om with
                           | Some m => if Z.testbit (m_access m) 8 then invoke_run_model p mdl s top rest mr args r nx d
                                       else enter s caller rest d m args nx
                           | None => invoke_run_model p mdl s top rest mr args r nx d
                           end
                 end
        | RThrow e =>
            (* a loaded model class of a JDK class (harness/jdkmodel) may leave a
               method to the Rocq model of that class *)
            match mdl (mr_class mr) (mr_name mr) (mr_desc mr) args s with
            | MNoModel => throw_new p s e
            | _ => if erroneous p 64 (ms_statics s) (mr_class mr) then throw_new p s "java/lang/NoClassDefFoundError"
                   else match init_needed p 64 (ms_inited s) (mr_class mr) with
                        | Some _ => init_class p s (mr_class mr)
                        | None => invoke_run_model p mdl s top rest mr args r nx (mr_class mr)
                        end
            end
        | RUnknown => invoke_run_model p mdl s top rest mr args r nx (mr_class mr)
        end in
      if negb (erroneous p 64 (ms_statics s) (mr_class mr))
         && match init_needed p 64 (ms_inited s) (mr_class mr) with None => true | Some _ => false end then
        match resolve_full p (mr_class mr) (mr_name mr) (mr_desc mr) with
        | Some (cn, m) =>
            if Z.testbit (m_access m) 8 then invoke_run_model p mdl s top rest mr args r nx cn
            else enter s caller rest cn m args nx
        | None => match mdl (mr_class mr) (mr_name mr) (mr_desc mr) args s with
                  | MNoModel => slow
                  | _ => invoke_run_model p mdl s top rest mr args r nx (mr_class mr)
                  end
        end
      else slow
  | InvSpecial | InvVirtual | InvInterface =>
      match args with
      | VNull :: _ =>
          (* the method is resolved before the receiver is checked (JVMS 6.5); a
             method of a class the machine does not know is assumed to resolve
             (the JDK the code was compiled against) *)
          match resolve_method p (mr_interface mr) (mr_class mr) (mr_name mr) (mr_desc mr) with
          | RThrow e => throw_new p s e
          | RFound (_, a, _) => if acc_static a then throw_new p s ICCE else throw_new p s NPE
          | RUnknown => throw_new p s NPE
          end
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

(** getfield/putfield when the receiver is null or the object has no field of
    that key: resolution comes first (JVMS 6.5), so NoSuchFieldError /
    IncompatibleClassChangeError take precedence; otherwise [otherwise] is
    thrown (NullPointerException) or, when it is not an exception class, the
    step is stuck.  A field of a class the machine does not know is assumed
    to resolve. *)
Definition instance_field_error (p : program) (s : mstate) (fr : fieldref) (otherwise : string) : mstep :=
  match resolve_field p fr with
  | FNotFound => throw_new p s NSFE
  | FFound _ a => if acc_static a then throw_new p s ICCE
                  else if String.eqb otherwise NPE then throw_new p s NPE else MStuck otherwise
  | FUnknown => if String.eqb otherwise NPE then throw_new p s NPE else MStuck otherwise
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
  | None => if cf_clinit top && Z.eqb (f_pc f) (-1) then clinit_prepare p s top rest
            else MStuck "no instruction at pc"
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
        | Some _ => init_class p s cn
        | None =>
          match instance_fields p 64 cn with
          | Some fs => let (l, s') := alloc s (OObj cn fs) in go (VRef l :: st) s'
          | None => MStuck "new: class not loaded and not modelled"
          end
        end
    | Getfield fr =>
        match st with
        | VNull :: _ => instance_field_error p s fr NPE
        | VRef l :: r =>
            match h l with
            | Some (OObj _ fs) =>
                match field_slot p fr fs with
                | FSKey key => match assoc key fs with
                               | Some v => go (v :: r) s
                               | None => instance_field_error p s fr "getfield: the object has no such field"
                               end
                | FSThrow e => throw_new p s e
                | FSStuck why => MStuck why
                end
            | _ => MStuck "getfield: not an object"
            end
        | _ => MStuck "getfield: operand"
        end
    | Putfield fr =>
        match st, field_type (fr_desc fr) with
        | v :: VNull :: _, _ => instance_field_error p s fr NPE
        | v :: VRef l :: r, Some t =>
            if negb (value_fits t v) then MStuck "putfield: value type" else
            match h l with
            | Some (OObj cn fs) =>
                match field_slot p fr fs with
                | FSKey key =>
                    match set_assoc key (narrow_store t v) fs with
                    | Some fs' =>
                        go r {| ms_heap := upd h l (OObj cn fs'); ms_next := ms_next s;
                                ms_statics := ms_statics s; ms_inited := ms_inited s;
                                ms_locks := ms_locks s; ms_frames := ms_frames s |}
                    | None => instance_field_error p s fr "putfield: the object has no such field"
                    end
                | FSThrow e => throw_new p s e
                | FSStuck why => MStuck why
                end
            | _ => MStuck "putfield: not an object"
            end
        | _, _ => MStuck "putfield: operand"
        end
    | Getstatic fr =>
        match static_target p s fr with
        | STKey key =>
            match assoc key (ms_statics s) with
            | Some v => go (v :: st) s
            | None => MStuck "getstatic: static field not set"
            end
        | STInit d => init_class p s d
        | STThrow e => throw_new p s e
        | STJdk d =>
            (* a static field of a JDK class: its model, as a pseudo-method "<get>name" *)
            match mdl d ("<get>" ++ fr_name fr) (fr_desc fr) nil s with
            | MOk (Some v) s' => go (v :: st) (with_frames s' (ms_frames s))
            | MThrow cn => throw_new p s cn
            | MStuckModel why => MStuck why
            | _ => MStuck ("no model for the static field " ++ d ++ "." ++ fr_name fr)
            end
        | STStuck why => MStuck why
        end
    | Putstatic fr =>
        match static_target p s fr with
        | STKey key =>
          match st, field_type (fr_desc fr) with
          | v :: r, Some t =>
              if negb (value_fits t v) then MStuck "putstatic: value type" else
              match set_assoc key (narrow_store t v) (ms_statics s) with
              | Some sts =>
                  go r {| ms_heap := h; ms_next := ms_next s; ms_statics := sts;
                          ms_inited := ms_inited s; ms_locks := ms_locks s; ms_frames := ms_frames s |}
              | None => MStuck "putstatic: static field not set"
              end
          | _, _ => MStuck "putstatic: operand"
          end
        | STInit d => init_class p s d
        | STThrow e => throw_new p s e
        | STJdk d => MStuck ("putstatic to a static field of a JDK class: " ++ d ++ "." ++ fr_name fr)
        | STStuck why => MStuck why
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
