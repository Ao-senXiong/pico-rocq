Require Import Syntax.

(* Viewpoint adaptation of mutability qualifiers *)

Definition vpa_mutabilty_bound (q1: q)(q2 : q_c) : q :=
  match q1, q2 with
    | Rd, RDM_c => Lost
    | q1, RDM_c => q1
    | _, Imm_c => Imm
    | _, Mut_c => Mut
    end.

Definition vpa_mutabilty_fld_bound (q1: q_f)(q2 : q_c) : q_f :=
  match q1, q2 with
    (* | Rd_f, RDM_c => Lost *)
    | Imm_f, RDM_c => Imm_f
    | Mut_f, RDM_c => Mut_f
    | RDM_f, RDM_c => RDM_f
    | RD_f, RDM_c => RD_f (* This is not the rule used to check assignability, use it for wellformedness only*)
    | _, Imm_c => Imm_f
    | _, Mut_c => Mut_f
    end.    

Definition vpa_mutabilty_stype_fld (q1: q)(q2 : q_f) : q :=
  match (q1, q2) with
    | (Rd, RDM_f) => Lost
    | (Imm, RDM_f) => Imm
    | (Mut, RDM_f) => Mut
    | (Lost, RDM_f) => Lost
    | (Bot, RDM_f) => Bot
    | (_, Imm_f) => Imm
    | (_, Mut_f) => Mut
    | (_, Rd_f) => Rd
    end.    

Definition vpa_mutabilty_rec_fld (q1: q_r)(q2 : q_f) : q :=
  match (q1, q2) with
    | (Imm_r, RDM_f) => Imm
    | (Mut_r, RDM_f) => Mut
    | (_, Imm_f) => Imm
    | (_, Mut_f) => Mut
    | (_, Rd_f) => Rd
    end.

Definition vpa_mutabilty_constructor_fld (q1: q_c)(q2 : q_f) : q :=
  match (q1, q2) with
    | (Imm_c, RDM_f) => Imm
    | (Mut_c, RDM_f) => Mut
    | (RDM_c, RDM_f) => Bot (* AOSEN: unable to assign to RDM field in RDM constructor because of not support RDM constructor parameter*)
    | (_, Imm_f) => Imm
    | (_, Mut_f) => Mut
    | (_, Rd_f) => Rd
    end.

(* Viewpoint adaptation of assignability qualifiers *)
Definition vpa_assignability (q1: q) (a1: a) : a :=
  match q1, a1 with
    | Mut, RDA => Assignable
    | _, Assignable => Assignable
    | _, _ => Final
  end.