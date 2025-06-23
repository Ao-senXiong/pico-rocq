Require Import Syntax.

(* Viewpoint adaptation of mutability qualifiers *)
Definition vpa_mutabilty (q1 q2 : q) : q :=
  match q1, q2 with
    | Rd, RDM => Lost
    | q1, RDM => q1
    | _, q2 => q2
    end.

(* Build an adapted qualified type *)
Definition vpa_qualified_type (q1: q) (qt: qualified_type) : qualified_type :=
  match qt with
    | Build_qualified_type q2 c =>
        Build_qualified_type (vpa_mutabilty q1 q2) c
  end.

(* Viewpoint adaptation of assignability qualifiers *)
Definition vpa_assignability (q1: q) (a1: a) : a :=
  match q1, a1 with
    | Mut, RDA => Assignable
    | _, Assignable => Assignable
    | _, _ => Final
  end.