Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.NArith.NArith.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.

Import MonadNotation.
Import ApplicativeNotation.
Import FunctorNotation.

Open Scope monad_scope.
Open Scope char_scope.

Module Char.
(* utility functions, some from clarus/coq-list-string *)

(** Test if the character is a white space (space, \t, \n, \v, \f or \r). *)
Definition is_white_space (c : ascii) : bool :=
  match c with
  | "009" | "010" | "011" | "012" | "013" | " " => true
  | _ => false
  end.

(** Replace uppercase letters by lowercase ones (only characters from a to z are affected). *)
Definition to_lower (c : ascii) : ascii :=
  let n := N_of_ascii c in
  let n_A := N_of_ascii "A" in
  let n_Z := N_of_ascii "Z" in
  let n_a := N_of_ascii "a" in
  if andb (N.leb n_A n) (N.leb n n_Z) then
    ascii_of_N ((n + n_a) - n_A)
  else c.

(** Replace lowercase letters by uppercase ones (only characters from a to z are affected). *)
Definition to_upper (c : ascii) : ascii :=
  let n := N_of_ascii c in
  let n_a := N_of_ascii "a" in
  let n_z := N_of_ascii "z" in
  let n_A := N_of_ascii "A" in
  if andb (N.leb n_a n) (N.leb n n_z) then
    ascii_of_N ((n + n_A) - n_a)
  else c.

Definition shift (c : ascii) : ascii := ascii_of_N (1 + N_of_ascii c).

End Char.

Module Editor.

Inductive edit : Type -> Type :=
| ret : forall {a}, a -> edit a
| bind : forall {a b}, edit a -> (a -> edit b) -> edit b
| message : string -> edit unit
| message_box : string -> edit unit
| input : edit string
| insert_char : ascii -> edit unit
| remove_char : edit unit
| get_char : edit ascii
| move_left : edit unit
| move_right : edit unit.

Instance Monad_edit : Monad edit := {ret a := @ret a ; bind a b := @bind a b}.

(* this may be overkill, I'm not sure which of these recursive calls are absolutely necessary *)
Fixpoint right_associator (n : nat) :=
  fix right_associator1 {a : Type} (e : edit a) : edit a :=
    match n, e with
    | S n', bind (bind m f) g =>
        @right_associator n' _
          (bind (right_associator1 m)
                (fun x => @right_associator n' _
                            (bind (@right_associator n' _ (f x))
                                  (fun y => @right_associator n' _ (g y)))))
    | _ , e => e
    end.

Definition right_assoc {a : Type} (e : edit a) : edit a := @right_associator 1000 a e.


Definition replace_char (c : ascii) : edit unit :=
  remove_char ;;
  insert_char c.

Fixpoint insert_string (s : string) : edit unit :=
  match s with
  | EmptyString => ret tt
  | String a s' => insert_char a ;;
                   insert_string s'
  end.

Fixpoint get_word' (n : nat) : edit string :=
match n with
| O => ret EmptyString
| S n' =>
    c <- get_char ;;
    move_right ;;
    if Char.is_white_space c
      then ret EmptyString
      else rest <- get_word' n' ;; ret (String c rest)
end.

Definition get_word : edit string := get_word' 5.

Fixpoint skip_word' (n : nat) : edit unit :=
match n with
| O => ret tt
| S n' =>
    c <- get_char ;;
    move_right ;;
    if Char.is_white_space c
      then ret tt
      else skip_word' n'
end.

Definition skip_word : edit unit := skip_word' 10.

Eval cbn in (Editor.right_assoc Editor.skip_word).

Definition make_upper : edit unit :=
  c <- get_char ;;
  replace_char (Char.to_upper c).

Definition insert_hello : edit unit :=
  insert_string "hello ".

Definition message_hello : edit unit :=
  message_box "hello there!".

Definition greet : edit unit :=
  make_upper ;;
  move_left ;;
  insert_hello.

Fixpoint get_chars (n : nat) : edit string :=
match n with
| O => ret EmptyString
| S n' =>
    c <- get_char ;;
    move_right ;;
    rest <- get_chars n' ;; ret (String c rest)
end.

Definition cond : edit unit :=
  s <- get_chars 1 ;;
  message_box s.

Definition shift_char : edit unit :=
  c <- get_char ;;
  replace_char (Char.shift c) ;;
  move_right.

Eval cbn in (Editor.shift_char).
Eval cbn in (Editor.right_assoc Editor.shift_char).

End Editor.