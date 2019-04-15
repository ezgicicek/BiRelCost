module WEnv = Why3.Env
module WT   = Why3.Theory
module WP   = Why3.Pretty

module WC   = WhyCore

module I  = Why3.Ident
module T  = Why3.Term
module D  = Why3.Decl
module Ty = Why3.Ty


open Syntax
open IndexSyntax
open Constr
open Format
open Support.Error

module H  = Hashtbl


exception Why3_error of string


exception Elim_Solve_Fails

exception Elim_Solve_Leq_Fails
exception Elim_Switch
exception UnknownWhy3Term
 
let dp = Support.FileInfo.dummyinfo

let why_error   fi   = error_msg Support.Options.SMT fi

let why_debug   fi   = Format.fprintf Format.std_formatter  fi

let real_theory     : WT.theory = WEnv.read_theory WC.env ["real"] "Real"
let real_log_theory : WT.theory = WEnv.read_theory WC.env ["real"] "ExpLog"
let real_pow_theory : WT.theory = WEnv.read_theory WC.env ["real"] "PowerReal"
let real_min_theory : WT.theory = WEnv.read_theory WC.env ["real"] "MinMax"
let sum_theory      : WT.theory = WEnv.read_theory WC.env ["birel"] "Sum"
let birel_theory    : WT.theory = WEnv.read_theory WC.env ["birel"]   "Birel"


let get_why3_sym th name =
  try WT.ns_find_ls th.WT.th_export [name]
  with Not_found -> why_error dp "Primitive %s cannot be mapped to Why3" name



let why3_eq = get_why3_sym real_theory "infix ="
let why3_leq = get_why3_sym real_theory "infix <="

let why3_radd   = get_why3_sym real_theory "infix +"
let why3_rsub   = get_why3_sym real_theory "infix -"
let why3_rmult  = get_why3_sym real_theory "infix *"
let why3_rdiv   = get_why3_sym real_theory "infix /"
let why3_rlog   = get_why3_sym real_log_theory "log2"
let why3_rpow   =  get_why3_sym real_pow_theory "pow"
let why3_rmin   = get_why3_sym real_min_theory "min"
let why3_rceil  = get_why3_sym birel_theory "cl"
let why3_rfloor = get_why3_sym birel_theory "fl"
let why3_lin_f  = get_why3_sym birel_theory "lin_f"
let why3_con_f  = get_why3_sym birel_theory "con_f"
let why3_rmin_pow  = get_why3_sym birel_theory "min_pow"
let why3_rsum   = get_why3_sym sum_theory "sum"


(* We need to keep track of the Why3 variable mapping *)
let vmap : ((string, T.vsymbol) H.t) ref = ref (H.create 256)

(* We need to keep track of the Why3 index function mapping used in summations *)
let lmap : ((string, T.lsymbol) H.t) ref = ref (H.create 8)

let rec get_why3_var v =
   if H.mem !vmap v then
      H.find !vmap v
   else
    let vt = T.create_vsymbol (I.id_fresh v)  (Ty.ty_real)
    in H.add !vmap v  vt; get_why3_var v


let why3_int s   = T.t_const (Why3.Number.ConstInt (Why3.Number.int_const_dec (string_of_int s)))

let why3_float f =
  let (f,i) = modf f                                   in
  let is    = Printf.sprintf "%.0f" i                  in
  if i < 0.0 then
    let is_u  = String.sub is 1 (String.length is - 1) in
    let fs    = String.sub (Printf.sprintf "%.3f" f) 3 3 in
    let tzero = T.t_const (Why3.Number.ConstReal (Why3.Number.real_const_dec "0" "0" None)) in
    let tpos = T.t_const (Why3.Number.ConstReal (Why3.Number.real_const_dec is_u fs None)) in
    T.t_app_infer why3_rsub [tzero; tpos]
  else
  let fs    = String.sub (Printf.sprintf "%.3f" f) 2 3 in
  T.t_const (Why3.Number.ConstReal (Why3.Number.real_const_dec is fs None))


let why3_fin f = why3_float f


let rec why3_i_term s =
  match s with
  | IVar v         -> if H.mem !vmap v.v_name 
    then let w_v = T.t_var (H.find !vmap v.v_name) in w_v
    else why_error dp "Can't find var %a already declared" Print.pp_vinfo v
  | IConst c       -> why3_fin c
  | IZero          ->  why3_fin 0.0
  | ISucc s        ->  let w_s = why3_i_term s in
    T.t_app_infer why3_radd [why3_fin 1.0; w_s]
  | IAdd (s1,s2)   ->  
    let w_s1 = why3_i_term s1 in
    let w_s2 = why3_i_term s2 in
    T.t_app_infer why3_radd [w_s1; w_s2]
  | IMinus (s1,s2) ->  
    let w_s1 = why3_i_term s1 in
    let w_s2 = why3_i_term s2 in
    T.t_app_infer why3_rsub [w_s1; w_s2]
  | IMult (s1,s2)  ->  
    let w_s1 = why3_i_term s1 in
    let w_s2 = why3_i_term s2 in
    T.t_app_infer why3_rmult [w_s1; w_s2]
  | IDiv (s1,s2)  ->  
    let w_s1 = why3_i_term s1 in
    let w_s2 = why3_i_term s2 in
    T.t_app_infer why3_rdiv [w_s1; w_s2]
  | ILog s        ->  let w_s = why3_i_term s in
    T.t_app_infer why3_rlog [w_s]
  | ICeil s       ->  let w_s = why3_i_term s in
    T.t_app_infer why3_rceil [w_s]
  | IFloor s     ->  let w_s = why3_i_term s in
    T.t_app_infer why3_rfloor [w_s]
  | IPow (s1,s2)  ->  
    let w_s1 = why3_i_term s1 in
    let w_s2 = why3_i_term s2 in
    T.t_app_infer why3_rpow [w_s1; w_s2]
  | IMin (s1,s2)  ->  
    let w_s1 = why3_i_term s1 in
    let w_s2 = why3_i_term s2 in
    T.t_app_infer why3_rmin [w_s1; w_s2]
  | IMinPowLin (s1, s2) ->
    let w_s1 = why3_i_term s1 in
    let w_s2 = why3_i_term s2 in
    T.t_func_app 
      (T.t_func_app
         (T.t_func_app (T.t_app_infer  why3_rmin_pow []) w_s1) w_s2) 
      (T.t_app_infer why3_lin_f [])
  | IMinPowCon (s1, s2) ->
    let w_s1 = why3_i_term s1 in
    let w_s2 = why3_i_term s2 in
    T.t_func_app 
      (T.t_func_app
         (T.t_func_app (T.t_app_infer  why3_rmin_pow []) w_s1) w_s2) 
      (T.t_app_infer why3_con_f [])
  | ISum (s, s1,s2)  ->
    let w_s1 = why3_i_term s1 in
    let w_s2 = why3_i_term s2 in
    let w_s = why3_i_term s in
    T.t_app_infer why3_rsum [w_s1; w_s2; w_s]
  | _ -> why_error dp "Unknown why3 index term\n"

let why3_eq_cs (s1, s2) =
    let  w_s1 = why3_i_term s1 in
    let  w_s2 = why3_i_term s2 in
    T.ps_app why3_eq [w_s1; w_s2]

let why3_leq_cs (s1, s2) =
    let  w_s1 = why3_i_term s1 in
    let  w_s2 = why3_i_term s2 in
    T.ps_app why3_leq [w_s1; w_s2]


let rec cs_to_why3 cs  =
   match cs with
  | CTrue -> T.t_true
  | CFalse -> T.t_false
  | CEq (s1,s2) -> why3_eq_cs (s1,s2)
  | CLeq (s1,s2) -> why3_leq_cs (s1,s2)
  | CImpl (c1, c2) -> T.t_binary T.Timplies (cs_to_why3 c1) (cs_to_why3 c2)
  | CAnd (c1, c2) ->  T.t_binary T.Tand (cs_to_why3 c1) (cs_to_why3 c2)
  | COr (c1, c2) ->  T.t_binary T.Tor (cs_to_why3 c1) (cs_to_why3 c2)
  | CForall (v,i, s, c) -> let w_v = get_why3_var v.v_name in T.t_forall_close [w_v] []  ( cs_to_why3 c)
  | CExists (v, i, s, c) ->let w_v = get_why3_var v.v_name in
    T.t_exists_close [w_v] []  ( cs_to_why3 c)

let new_theory d t =
  let t' = WT.use_export (WT.create_theory (I.id_fresh "newT")) t in
  WT.close_theory (WT.add_param_decl t' d)


let why3_translate cs =
  H.clear !vmap;
  try
    (* why_debug "!*! Constraint to translate: @[%a@]" Print.pp_cs cs; *)

    cs_to_why3 cs
  with Ty.TypeMismatch(ty1, ty2) ->
    why_error  dp "Why3 type mismatch: @[%a@] vs @[%a@]" WP.print_ty ty1 WP.print_ty ty2

