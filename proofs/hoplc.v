(*
 * File:    hoplc-anf.v
 * Author:  Connor Adsit
 * Date:    2015-01-29
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
  | b_vapp_rec : var -> var -> binding
  | b_tapp : var -> tyvar -> binding
  | b_tapp_rec : var -> tyvar -> binding

with value : Type :=
  | v_fun : var -> tyvar -> exp -> value
  | v_tyfun : tyvar -> exp -> value
  | v_recfun : var -> tyvar -> var -> tyvar -> exp -> value
  | v_rectyfun : var -> tyvar -> tyvar -> exp -> value
.

Notation "'letx' x ':-' ax '<--' b '\in' e" := (e_letx x ax b e) (at level 99).
Notation "'leta' a '<--' t '\in' e" := (e_leta a t e) (at level 99).
Notation "'lam' z ':-' az '-->' e" := (v_fun z az e) (at level 90).
Definition x := Id 0.
Definition evarx := e_vari x.
Definition id_fun := (lam (Id 0) :- (Id 1) --> evarx).
Definition test := letx (Id 0) :- (Id 1) <-- b_val id_fun \in evarx.
Notation "'fix' f ':-' af '-->' z ':-' az '-->' e" := (v_recfun f af z az e) (at level 90).
Notation "'tlam' a '-->' e" := (v_tyfun a e) (at level 90).
Notation "'tfix' f ':-' af '-->' a '-->' e" := (v_rectyfun f af a e) (at level 90).

Scheme exp_xtra_ind := Induction for exp Sort Prop
with binding_xtra_ind := Induction for binding Sort Prop
with value_xtra_ind := Induction for value Sort Prop.
Combined Scheme exp_binder_value_ind from exp_xtra_ind, binding_xtra_ind, value_xtra_ind.

(* ===================================================================== *)
(* Operational Semantics *)

Inductive var_env : Type :=
  | ve_empty : var_env
  | ve_binding : var -> value -> var_env -> var_env
.
Notation "rho ',' x '|->v' w" := (ve_binding x w rho) (at level 85).

Reserved Notation "rho '[' x ']v' '=' v" (at level 85).
Inductive lookup_var_env : var_env -> var -> value -> Prop :=
  | lve_hit : forall x v rho',
              (rho', x |->v v)[x]v = v
  | lve_miss : forall y w x v rho',
               x <> y ->
               rho'[x]v = v ->
               (rho', y |->v w)[x]v = v
where "rho '[' x ']v' '=' v" := (lookup_var_env rho x v)
.

Inductive tyvar_env : Type :=
  | te_empty : tyvar_env
  | te_binding : tyvar -> type -> tyvar_env -> tyvar_env
.
Notation "phi ',' a '|->t' t" := (te_binding a t phi) (at level 85).

Reserved Notation "phi '[' a ']t' '=' t" (at level 85).
Inductive lookup_tyvar_env : tyvar_env -> tyvar -> type -> Prop :=
  | lte_hit : forall phi' a t,
              (phi', a |->t t)[a]t = t
  | lte_miss: forall a b t p phi',
              a <> b ->
              phi'[a]t = t ->
              (phi', b |->t p)[a]t = t
where "phi '[' a ']t' '=' t" := (lookup_tyvar_env phi a t)
.

Inductive kont : Type :=
  | k_empty : kont
  | k_stack : exp -> var_env -> tyvar_env -> kont -> kont
.
Notation "'[[' e ';' rho ';' phi ']]::' k" := (k_stack e rho phi k) (at level 95).

Inductive state : Type :=
  | st_cons : exp -> var_env -> tyvar_env -> kont -> state.

Notation "'<<' e ';' rho ';' phi ';' k '>>'" := (st_cons e rho phi k).

Reserved Notation "st1 '~~>' st2" (at level 90).
Inductive step : state -> state -> Prop :=
  | st_leta : forall a t e' rho phi k, 
              << leta a <-- t \in e'; rho; phi; k >> ~~> << e'; rho; phi, a |->t t; k >>
  | st_letx_val : forall x ax v rho phi k e',
                  << letx x :- ax <-- b_val v \in e'; rho; phi; k >> ~~> << e'; rho, x |->v v; phi; k >>
  | st_letx_vapp : forall x ax xfun xarg e' rho phi k z az eb val,
                   rho[xfun]v = (lam z :- az --> eb) ->
                   rho[xarg]v = val ->
                   << letx x :- ax <-- b_vapp xfun xarg \in e'; rho; phi; k >> ~~>
                        << eb; rho, z |->v val; phi; [[ letx x :- ax <-- b_vapp xfun xarg \in e'; rho; phi ]]:: k>>
where "st1 '~~>' st2" := (step st1 st2)
.

(* ===================================================================== *)
(* Typing Rules *)


