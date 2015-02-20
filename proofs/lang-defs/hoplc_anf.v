(*
 * File:    hoplc.v
 * Author:  Connor Adsit
 * Date:    2015-02-17
 *)

(* ===================================================================== *)
(* Helpers *)
Inductive id : Type :=
  Id : nat -> id.


(* ===================================================================== *)
(* Language definition *)

Definition var := id.
Definition tyvar := id.

Inductive type : Type :=
  | t_arrow : tyvar -> tyvar -> type
  | t_forall : tyvar -> type
.

Inductive exp : Type :=
  | e_vari : var -> exp
  | e_letx : var -> tyvar -> binding -> exp -> exp
  | e_leta : tyvar -> type -> exp -> exp

with binding : Type :=
  | b_val : value -> binding
  | b_vapp : var -> var -> binding
  | b_tapp : var -> tyvar -> binding

with value : Type :=
  | v_fun : var -> tyvar -> exp -> value
  | v_tyfun : tyvar -> exp -> value
  | v_recfun : var -> tyvar -> var -> tyvar -> exp -> value
  | v_rectyfun : var -> tyvar -> tyvar -> exp -> value
.

Notation "'letx' x ':-' αx '⟵' b '\in' e" := (e_letx x αx b e) (at level 99).
Notation "'leta' α '⟵' t '\in' e" := (e_leta α t e) (at level 99).
Notation "'λ' z ':-' αz '⟶' e" := (v_fun z αz e) (at level 90).
Notation "'μ' f ':-' αf '⟶' 'λ' z ':-' αz '⟶' e" := (v_recfun f αf z αz e) (at level 90).
Notation "'Λ' β '⟶' e" := (v_tyfun β e) (at level 90).
Notation "'μ' f ':-' αf '⟶' 'Λ' β '⟶' e" := (v_rectyfun f αf β e) (at level 90).

Scheme exp_xtra_ind := Induction for exp Sort Prop
  with binding_xtra_ind := Induction for binding Sort Prop
  with value_xtra_ind := Induction for value Sort Prop.
Combined Scheme exp_binder_value_recval_ind from exp_xtra_ind, binding_xtra_ind, value_xtra_ind.

(* ===================================================================== *)
(* Helpful language constructs *)

Inductive env (id_t: Type) (val_t: Type) : Type :=
  | env_empty : env id_t val_t
  | env_binding : id_t -> val_t -> env id_t val_t -> env id_t val_t
.
Notation "env ',' var '⟼' val" := (env_binding _ _ var val env) (at level 85).
Notation "•" := (env_empty _ _) (at level 85).

Reserved Notation "env '[' var ']' '⟶' val" (at level 85).
Inductive lookup_env (id_t: Type) (val_t: Type) : (env id_t val_t) -> id_t -> val_t -> Prop :=
  | env_hit : forall (x: id_t) (v: val_t) (env': env id_t val_t),
              (env', x ⟼ v)[x] ⟶ v
  | env_miss : forall (y: id_t) (w: val_t) (x: id_t) (v: val_t) env',
               x <> y ->
               env'[x] ⟶ v ->
               (env', y ⟼ w)[x] ⟶ v
where "env '[' var ']' '⟶' val" := (lookup_env _ _ env var val)
.

Definition value_env := env var value.
Definition type_env := env tyvar type.
