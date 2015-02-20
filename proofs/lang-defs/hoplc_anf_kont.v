(*
 * File:    hoplc-kont.v
 * Author:  Connor Adsit
 * Date:    2015-02-16
 *)

Require Import hoplc.

Inductive kont : Type :=
  | k_empty : kont
  | k_frame : exp -> value_env -> type_env -> kont -> kont
.
Notation "'[[]]'" := k_empty (at level 95).
Notation "'[[' e ';' ρ ';' Φ ']]::' κ" := (k_frame e ρ Φ κ) (at level 95).

Inductive state : Type :=
  | st_cons : exp -> value_env -> type_env -> kont -> state.

Notation "'<<' e ';' ρ ';' Φ ';' κ '>>'" := (st_cons e ρ Φ κ).

Reserved Notation "st1 '⟿' st2" (at level 90).
Inductive step : state -> state -> Prop :=
  | st_leta : forall α t e' ρ Φ κ, 
              << leta α ⟵ t \in e'; ρ; Φ; κ >> ⟿ << e'; ρ; Φ, α ⟼ t; κ >>

  | st_letx_val : forall x αx v ρ Φ κ e',
              << letx x :- αx ⟵ b_val v \in e'; ρ; Φ; κ >> ⟿ << e'; ρ, x ⟼ v; Φ; κ >>

  | st_letx_vapp : forall x αx xfun xarg e' ρ Φ κ z αz eb val,
              ρ[xfun] ⟶ (λ z :- αz ⟶ eb) ->
              ρ[xarg] ⟶ val ->
              << letx x :- αx ⟵ b_vapp xfun xarg \in e'; ρ; Φ; κ >> ⟿
                 << eb; ρ, z ⟼ val; Φ; [[ letx x :- αx ⟵ b_vapp xfun xarg \in e'; ρ; Φ ]]::κ >>
  | st_letx_vapp_rec : forall x αx xfun xarg e' ρ Φ κ f αf z αz eb val,
              ρ[xfun] ⟶ (μ f :- αf ⟶ λ z :- αz ⟶ eb) ->
              ρ[xarg] ⟶ val ->
              << letx x :- αx ⟵ b_vapp xfun xarg \in e'; ρ; Φ; κ >> ⟿
                 << eb; ρ, z ⟼ val, f ⟼ (μ f :- αf ⟶ λ z :- αz ⟶ eb); Φ; 
                    [[ letx x :- αx ⟵ b_vapp xfun xarg \in e'; ρ; Φ ]]::κ >>

  | st_letx_tapp : forall x αx xfun targ e' ρ Φ κ β eb τ,
              ρ[xfun] ⟶ (Λ β ⟶ eb) ->
              Φ[targ] ⟶ τ ->
              << letx x :- αx ⟵ b_tapp xfun targ \in e'; ρ; Φ; κ >> ⟿
                 << eb; ρ; Φ, β ⟼ τ; [[ letx x :- αx ⟵ b_tapp xfun targ \in e'; ρ; Φ ]]::κ >>
  | st_letx_tapp_rec : forall x αx xfun targ e' ρ Φ κ f αf β eb τ,
              ρ[xfun] ⟶ (μ f :- αf ⟶ Λ β ⟶ eb) ->
              Φ[targ] ⟶ τ ->
              << letx x :- αx ⟵ b_tapp xfun targ \in e'; ρ; Φ; κ >> ⟿
                 << eb; ρ, f ⟼ (μ f :- αf ⟶ Λ β ⟶ eb); Φ, β ⟼ τ; 
                    [[ letx x :- αx ⟵ b_tapp xfun targ \in e'; ρ; Φ ]]::κ >>

  | st_ret_vapp : forall xret val ρ' Φ' ρ Φ x αx xfun xarg e' κ,
             ρ[xret] ⟶ val ->
             << e_vari xret; ρ'; Φ'; [[ letx x :- αx ⟵ b_vapp xfun xarg \in e'; ρ; Φ ]]::κ >> ⟿
                << e'; ρ, xret ⟼ val; Φ; κ >>
  | st_ret_tapp : forall xret val ρ' Φ' ρ Φ x αx xfun targ e' κ,
             ρ[xret] ⟶ val ->
             << e_vari xret; ρ'; Φ'; [[ letx x :- αx ⟵ b_tapp xfun targ \in e'; ρ; Φ ]]::κ >> ⟿
                << e'; ρ, xret ⟼ val; Φ; κ >>
where "st1 '⟿' st2" := (step st1 st2)
.

Reserved Notation "st1 '⟿*' st2" (at level 90).
Inductive multistep : state -> state -> Prop :=
  | mst_self : forall st, st ⟿* st
  | mst_step : forall st1 st2 st3,
             st1 ⟿ st2 ->
             st2 ⟿* st3 ->
             st1 ⟿* st3
where "st1 '⟿*' st2" := (multistep st1 st2)
.
