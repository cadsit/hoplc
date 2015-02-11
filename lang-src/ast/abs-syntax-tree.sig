(*
 * File:    abs-syntax-tree.sig
 * Author:  Connor Adsit
 * Date:    2015-01-28
 *)
signature ABS_SYNTAX_TREE =
sig
   structure Var : VAR
   structure TVar : VAR

   structure Type :
   sig
      datatype t = 
         T_Int
       | T_Var  
       | T_VAbs of {tparam: t, tres: t}
       | T_TVar of TVar.t
   end

   structure Exp :
   sig 
      datatype Exp =
         Letx of {var: Var.t, tvar: Type.t option, bind: Exp, exp: Exp}
       | Leta of {tvar: Var.t, bind: Type.t, exp: Exp}
       | Val of Value
       | Var of Var.t

      and Lam = 
         VAbs of {param: Var.t, tparam: Type.t option, exp: Exp, typ: Type.t option}
       | TAbs of {tparam: Var.t, exp: Exp, typ: Type.t option}
       | RecVAbs of {fvar: Var.t, typ: Type.t option, param: Var.t, tparam: Type.t option,
                     exp: Exp, typ: Type.t option}
       | RecTAbs of {fvar: Var.t, typ: Type.t option, tparam: Var.t, exp: Exp, typ: Type.t option}

      and Value =
       | Func of Lam
       | Int of int

      type t = Exp
   end
end
