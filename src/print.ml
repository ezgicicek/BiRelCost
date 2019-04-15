(* Pretty printing module. It uses the standard Format module. *)

open Format

open Ctx
open Syntax
open IndexSyntax
open Constr
open Support.Options
open Support.FileInfo

(**********************************************************************)
(* Unicode handling *)

module Symbols = struct
  type pp_symbols =
      Inf
    | Forall
    | Exists
    | Arrow
    | DblArrow
    | Times
    | Int
    | IntR
    | Size
    | Cost
    | Bool
    | BoolR
    | Unit
    | UnitR
    | Mu
    | Lambda
    | BigLambda
    | Vdash
    | Leq
    | Top
    | Bot
    | And
    | Or
    | Impl

  (* TODO: add summations etc. *)

  let pp_symbol_table s = match s with
      Inf      -> ("inf",     "∞")
    | Forall   -> ("forall ", "∀")
    | Exists   -> ("exits " , "∃")
    | Arrow    -> ("->",      "→")
    | DblArrow -> ("=>",      "⇒")
    | Times    -> ("x",       "⊗")
    | Int      -> ("int",     "ℤ")
    | IntR     -> ("intR",     "ℤᵣ")
    | Size     -> ("nat",     "ℕ")
    | Cost     -> ("num",     "ℝ")
    | Bool     -> ("bool",    "𝔹")
    | BoolR    -> ("boolR",    "𝔹ᵣ")
    | Unit     -> ("unit",    "unit")
    | UnitR    -> ("unitR",    "unitᵣ")
    | Mu       -> ("mu",      "μ")
    | Lambda   -> ("\\",      "λ")
    | BigLambda-> ("\\!",  "Λ")
    | Vdash    -> ("|-",      "⊢")
    | Leq      -> ("<=",      "≤")
    | Top      -> ("true",    "T")
    | Bot      -> ("false",   "⊥")
    | And      -> ("and",      "∧")
    | Or       -> ("or",      "∨")
    | Impl     -> ("-->",     "→")

  let string_of_symbol s =
    let select = if !debug_options.unicode then snd else fst in
    select (pp_symbol_table s)
end

let u_sym x = Symbols.string_of_symbol x

(**********************************************************************)
(* Helper functions for pretty printing *)

let rec pp_list pp fmt l = match l with
    []         -> fprintf fmt ""
  | csx :: []  -> fprintf fmt "%a" pp csx
  | csx :: csl -> fprintf fmt "%a,@ %a" pp csx (pp_list pp) csl


(* Study this concept *)

(* Limit a formatter: (limit_boxes 3 pp_type) *)
let limit_boxes ?(n=(!debug_options).pr_level) pp = fun fmt ->
  let mb      = Format.pp_get_max_boxes fmt () in
  let con fmt = Format.pp_set_max_boxes fmt mb in
  (* print_string "eo"; print_string (string_of_int n); print_newline (); *)
  Format.pp_set_max_boxes fmt n;
  kfprintf con fmt "%a" pp

(**********************************************************************)
(* Pretty printing for variables *)

let pp_name fmt (bt, n) =
  let pf = fprintf fmt in
  match bt with
    BiVar    -> pf  "%s" n
  | BiIVar  -> pf "'%s" n
  | BiEVar Size -> pf "_%s" n
  | BiEVar Cost -> pf ".%s" n

let pp_vinfo fmt v =
  let vi = (v.v_type, v.v_name) in
  fprintf fmt "%a" pp_name vi
    

(* Sorts *)
let pp_sort fmt s = match s with
    Size       -> fprintf fmt "%s" (u_sym Symbols.Size)
  | Cost       -> fprintf fmt "%s" (u_sym Symbols.Cost)

(**********************************************************************)
(* Pretty printing for sensitivities *)
exception NoTrans

let rec speano_to_int n =
match n with
| IZero ->  0
| ISucc n' ->  (speano_to_int n') + 1
| IAdd (s1,s2) -> (speano_to_int s1) + (speano_to_int s2)
| IMinus (s1,s2) -> (speano_to_int s1) - (speano_to_int s2)
| IMult (s1,s2) -> (speano_to_int s1) * (speano_to_int s2)
| _ -> raise NoTrans


let rec pp_iterm fmt it =
  match it with
    IVar   v              -> pp_vinfo fmt v
  | IZero                 -> fprintf fmt "0"
  | IConst flt            -> fprintf fmt "%.3f" flt
  | ISucc  x              -> 
    begin
      try let i_x = speano_to_int it in  
      	fprintf fmt "%d" i_x
      with		
      | NoTrans ->  fprintf fmt "S(%a)" pp_iterm x
    end
  | IAdd (i1, i2)         -> fprintf fmt "(%a + %a)" pp_iterm i1 pp_iterm i2
  | IMinus (i1, i2)       -> fprintf fmt "(%a - %a)" pp_iterm i1 pp_iterm i2
  | IMult(i1, i2)         -> fprintf fmt "(%a * %a)" pp_iterm i1 pp_iterm i2
  | IDiv(i1, i2)          -> fprintf fmt "(%a / %a)" pp_iterm i1 pp_iterm i2
  | IPow (i1, i2)         -> fprintf fmt "%a^ %a" pp_iterm i1 pp_iterm i2
  | IMin (i1, i2)         -> fprintf fmt "min(%a,%a)" pp_iterm i1 pp_iterm i2
  | IMinPowLin (i1, i2)   -> fprintf fmt "minpowlin(%a,%a)" pp_iterm i1 pp_iterm i2
  | IMinPowCon (i1, i2)   -> fprintf fmt "minpowcon(%a,%a)" pp_iterm i1 pp_iterm i2
  | ISum (i1,i2,i3)       -> fprintf fmt "sum(%a, {%a, %a})" pp_iterm i1 pp_iterm i2 pp_iterm i3
  | ILog  x               -> fprintf fmt "log(%a)" pp_iterm x
  | ICeil  x              -> fprintf fmt "ceil(%a)" pp_iterm x
  | IFloor  x             -> fprintf fmt "floor(%a)" pp_iterm x
  | IInfty                -> fprintf fmt "%s" (u_sym Symbols.Inf)


(**********************************************************************)
(* Pretty printing for constraints *)

let pp_ivar_ctx_elem ppf (v, s) =
  if !debug_options.full_context then
    fprintf ppf "%-10a : %a" pp_vinfo v pp_sort s
  else
    fprintf ppf "%-10a" pp_vinfo v

let pp_ivar_ctx = pp_list pp_ivar_ctx_elem


(**********************************************************************)
(* Pretty printing for constraints *)
let rec pp_cs ppf cs =
  match cs with
  | CTrue                -> fprintf ppf "%s" (u_sym Symbols.Top)
  | CFalse               -> fprintf ppf "%s" (u_sym Symbols.Bot)
  | CEq(i1, i2)          -> fprintf ppf "%a = %a" pp_iterm i1 pp_iterm i2
  | CLeq(i1, i2)         -> fprintf ppf "%a %s %a" pp_iterm i1 (u_sym Symbols.Leq) pp_iterm i2
  | CAnd(cs1, cs2)       -> fprintf ppf "%a %s %a" pp_cs cs1 (u_sym Symbols.And) pp_cs cs2
  | COr(cs1, cs2)        -> fprintf ppf "(%a) %s (%a)" pp_cs cs1 (u_sym Symbols.Or) pp_cs cs2
  | CImpl(cs1, cs2)      -> fprintf ppf "%a %s (%a)" pp_cs cs1 (u_sym Symbols.Impl) pp_cs cs2
  | CForall(bi_x, i, s, cs) -> fprintf ppf "@<1>%s%a %a :: %a.@;(@[%a@])" (u_sym Symbols.Forall) pp_vinfo bi_x pp_fileinfo i pp_sort s pp_cs cs
  | CExists(bi_x, i, s, cs) -> fprintf ppf "@<1>%s%a %a :: %a.@;(@[%a@])" (u_sym Symbols.Exists) pp_vinfo bi_x pp_fileinfo i pp_sort s pp_cs cs
                 

(**********************************************************************)
(* Pretty printing for types *)

(* Unary primitive types *)
let pp_primutype fmt ty = match ty with
    UPrimInt     -> fprintf fmt "@<1>%s" (u_sym Symbols.Int)
  | UPrimUnit    -> fprintf fmt "@<1>%sR" (u_sym Symbols.Unit)
  | UPrimBool    -> fprintf fmt "@<1>%s" (u_sym Symbols.Bool)

                            
(* Binary primitive types *)
let pp_primbtype fmt ty = match ty with
    BPrimInt     -> fprintf fmt "@<1>%s" (u_sym Symbols.IntR)
  | BPrimUnit    -> fprintf fmt "@<1>%s" (u_sym Symbols.UnitR)
  | BPrimBool    -> fprintf fmt "@<1>%s" (u_sym Symbols.BoolR)

                            
(* Print exec. mode *)
let rec pp_mode fmt mu = match mu with
  MaxEx  -> fprintf fmt "max"
| MinEx  -> fprintf fmt "min"

(* Unary type printer *)
let rec pp_utype ppf  = function
   UTyPrim tp                -> fprintf ppf "%a" pp_primutype tp
  (* List types *)
  | UTyList (n, ty)          -> fprintf ppf "list[%a](%a)" pp_iterm n pp_utype ty 
  (* ADT *)
  | UTySum(ty1, ty2)         -> fprintf ppf "(%a @<1> +  @[<h>%a@])" pp_utype ty1   pp_utype ty2
  | UTyProd(ty1, ty2)        -> fprintf ppf "(%a @<1>%s @[<h>%a@])" pp_utype ty1 (u_sym Symbols.Times) pp_utype ty2
  (* Funs *)
  | UTyArr(ty1, mu, t, ty2)  -> fprintf ppf "(@[<hov>%a [%a,%a]%s @ %a@])" pp_utype ty1 pp_mode mu pp_iterm t (u_sym Symbols.Arrow)  pp_utype ty2
  (* Quantified types *)
  | UTyForall(n, s, mu, t , ty)  -> fprintf ppf "@<1>%s %a [%a,%a] :: %a.@;(@[%a@])" (u_sym Symbols.Forall) pp_vinfo n pp_mode mu pp_iterm t pp_sort s pp_utype ty
  | UTyExists(n, s, ty)     -> fprintf ppf "@<1>%s %a :: %a.@;(@[%a@])" (u_sym Symbols.Exists) pp_vinfo n pp_sort s pp_utype ty
  | UTyCs(cs, ty)     -> fprintf ppf "%a@<1>%s @;(@[%a@])" pp_cs cs (u_sym Symbols.And) pp_utype ty

(* Binary type printer *)
let rec pp_btype ppf  = function
   BTyPrim tp                -> fprintf ppf "%a" pp_primbtype tp
  (* List types *)
  | BTyList (n, alpha, ty)          -> fprintf ppf "list[%a,%a] %a" pp_iterm n pp_iterm alpha pp_btype ty 
  (* ADT *)
  | BTySum(ty1, ty2)         -> fprintf ppf "(%a @<1> +  @[<h>%a@])" pp_btype ty1   pp_btype ty2
  | BTyProd(ty1, ty2)        -> fprintf ppf "(%a @<1>%s @[<h>%a@])" pp_btype ty1 (u_sym Symbols.Times) pp_btype ty2
  (* Funs *)
  | BTyArr(ty1, t, ty2)  -> fprintf ppf "(@[<hov>%a[diff, %a]%s @ %a@])" pp_btype ty1 pp_iterm t (u_sym Symbols.Arrow)  pp_btype ty2
  (* Quantified types *)
  | BTyForall(n, s, t , ty)  -> fprintf ppf "@<1>%s %a [diff, %a] :: %a.@;(@[%a@])" (u_sym Symbols.Forall) pp_vinfo n pp_iterm t  pp_sort s pp_btype ty
  | BTyExists(n, s, ty)     -> fprintf ppf "@<1>%s :: %a.@;(@[%a@])" (u_sym Symbols.Exists) pp_vinfo n pp_btype ty
  | BTyUnrel (uty1, uty2) -> if uty1 = uty2 then  fprintf ppf "U %a @<1>" pp_utype uty1  else  fprintf ppf "U (%a @<1>, @[<h>%a@])" pp_utype uty1   pp_utype uty2
  | BTyBox ty         -> fprintf ppf "box (%a)" pp_btype ty
  | BTyCs (c, ty)         -> fprintf ppf " (%a and %a)"pp_cs c  pp_btype ty
                                
let pp_utype_list = pp_list pp_utype 
let pp_btype_list = pp_list pp_btype 

(**********************************************************************)
(* Pretty printing for unary contexts *)

let pp_var_uctx_elem ppf (v, ty) =
  if !debug_options.full_context then
    fprintf ppf "%-10a : @[%a@]" pp_vinfo v pp_utype ty
  else
    fprintf ppf "%a" pp_vinfo v

let pp_var_uctx   = pp_list pp_var_uctx_elem

(* Primitives to drop *)
let n_prim = 37

let rec ldrop n l = if n = 0 then l else ldrop (n-1) (List.tl l)

let pp_ucontext ppf ctx =
  fprintf ppf "Index Context: [@[<v>%a@]]@\n Unary Type Context: [@[<v>%a@]@]"
    pp_ivar_ctx (List.rev ctx.ivar_ctx)
    pp_var_uctx   (ldrop n_prim (List.rev ctx.var_ctx))

(**********************************************************************)
(* Pretty printing for unary contexts *)

let pp_var_bctx_elem ppf (v, ty) =
  if !debug_options.full_context then
    fprintf ppf "%-10a : @[%a@]" pp_vinfo v pp_btype ty
  else
    fprintf ppf "%a" pp_vinfo v

let pp_var_bctx   = pp_list pp_var_bctx_elem


let pp_bcontext ppf ctx =
  fprintf ppf "Index Context: [@[<v>%a@]]@\n Binary Type Context: [@[<v>%a@]@]"
    pp_ivar_ctx (List.rev ctx.ivar_ctx)
    pp_var_uctx   (ldrop n_prim (List.rev ctx.var_ctx))

(**********************************************************************)
(* Pretty printing for terms *)

(* This will be useful in the future *)

(* Operators *)
let binary_op_table =
  [("op_lor", "||");
   ("op_land", "&&");
   ("op_eq",   "==");
   ("op_neq",  "!=");
   ("op_lt",   "<");
   ("op_gt",   ">");
   ("op_lte",  "<=");
   ("op_gte",  ">=");
   ("op_add",  "+");
   ("op_sub",  "-");
   ("op_mul",  "*");
   ("op_div",  "/")]

let is_binary_op s = List.mem_assoc s binary_op_table

let string_of_op s = List.assoc s binary_op_table

let string_of_prim t = match t with
    PrimTUnit         -> "()"
  | PrimTInt i        -> string_of_int i
  | PrimTBool b       -> string_of_bool b

let pp_colon ppf it = match it with
    IConst 1.0      -> fprintf ppf " :[]"
  | IInfty          -> fprintf ppf " :"
  | it               -> fprintf ppf " :[%a]" pp_iterm it


(* Term pretty printing *)
let rec pp_expr ppf t =
  match t with
    Var (_, v)                 -> fprintf ppf "%a" pp_vinfo v
  (* Primitive terms *)
  | Prim(_, pt)           -> fprintf ppf "%s" (string_of_prim pt)

  (* Fix and application *)
  | Fix(_, bi_f, bi_x, tm) ->
    fprintf ppf "fix %a (%a). @\n@[<hov 1> %a@]@\n"
       pp_vinfo bi_f pp_vinfo bi_x  pp_expr tm
  | App(_, tm1, tm2)       -> fprintf ppf "@[%a@] @[%a@]" pp_expr tm1 pp_expr tm2

  | Let(_, bi_x, tm1, tm2) ->
    fprintf ppf "@[<v>@[<hov> let %a =@;<1 1>@[%a@]@] in@ %a@]" pp_vinfo bi_x pp_expr tm1 pp_expr tm2
 
  (* Inl/inr and case expressions *)
  | Inl (_, tm)           -> fprintf ppf "inl %a" pp_expr tm
  | Inr (_, tm)           -> fprintf ppf "inr %a" pp_expr tm
  | Case(_, tm, bi_l, ltm, bi_r, rtm) ->
    (* Alternative using vertical boxes *)
    fprintf ppf "case @[%a@] of {@\n   inl(%a) @<1>%s @[%a@]@\n | inr(%a) @<1>%s @[%a@]@\n}"
      pp_expr tm
      pp_vinfo bi_l (u_sym Symbols.DblArrow) pp_expr ltm
      pp_vinfo bi_r (u_sym Symbols.DblArrow) pp_expr rtm

  (* Product expressions *)
  | Pair (_, tm1, tm2)    -> fprintf ppf "(%a,%a)" pp_expr tm1 pp_expr tm2
  | Fst (_, tm)           -> fprintf ppf "fst %a" pp_expr tm
  | Snd (_, tm)           -> fprintf ppf "snd %a" pp_expr tm

 (* If-then-else *)
  | IfThen (_, tm, tm1, tm2) ->  fprintf ppf "if %a then %a else %a"
      pp_expr tm  pp_expr tm1  pp_expr tm2

  (* List expressions *)
  | Nil _           -> fprintf ppf "nil"
  | Cons (_, tm1, tm2)           -> fprintf ppf "%a::%a" pp_expr tm1 pp_expr tm2
  | CaseL(_, tm, ltm, bi_h, bi_tl, rtm) ->
    fprintf ppf "caseL @[%a@] {@\n   [] @<1>%s @[%a@]@\n | (%a :: %a) @<1>%s @[%a@]@\n}"
      pp_expr tm  (u_sym Symbols.DblArrow) pp_expr ltm
      pp_vinfo bi_h pp_vinfo bi_tl (u_sym Symbols.DblArrow) pp_expr rtm

  (* Index abstraction and application *)
  | ILam (_, tm)  -> fprintf ppf "%s. %a@" (u_sym Symbols.BigLambda) pp_expr tm
  | IApp (_, tm)  -> fprintf ppf "%a []"  pp_expr tm
  (* Existential index intro and elim forms*)
  | Pack(_, tm)    -> fprintf ppf "pack %a " pp_expr tm
  | Unpack(_, tm1, bi_x, tm2) -> fprintf ppf "unpack %a as %a in %a" pp_expr tm1 pp_vinfo bi_x pp_expr tm2

  (* Annotated expressions *)
  | UAnno (_, tm, uty, t) -> fprintf ppf "(%a: %a, %a)" pp_expr tm pp_utype uty pp_iterm t
  | BAnno (_, tm, bty, t) -> fprintf ppf "(%a: %a, %a)" pp_expr tm pp_btype bty pp_iterm t

  (* Constrained expressions *)
  | CExpr(_, tm) -> fprintf ppf "c.%a" pp_expr tm
  | CLet(_, bi_x, tm1, tm2) ->
    fprintf ppf "@[<v>@[<hov> clet %a as %a @] in@ %a@]" pp_expr tm1 pp_vinfo bi_x  pp_expr tm2
  | Contra _ -> fprintf ppf "contra"


     

(* let rec constr_free_i_vars (cs: constr) : var_info list = *)
(* match cs with *)
(* | CTrue | CFalse -> [] *)
(* | CEq (it1, it2) | CLeq (it1, it2) -> List.sort_uniq var_cmp (iterm_free_i_vars it1 @ iterm_free_i_vars it2) *)
(* | CAnd (cs1, cs2) | COr (cs1, cs2) | CImpl (cs1, cs2) ->  List.sort_uniq var_cmp (constr_free_i_vars cs1 @ constr_free_i_vars cs2) *)
(* | CForall(x, s, cs) | CExists(x, s, cs) -> List.filter (fun y -> if y.v_name = x.v_name && y.v_type = x.v_type &&  x != y then Format.fprintf Format.std_formatter "MUST BE  x :%a  y: %a \n" pp_vinfo x pp_vinfo y else (); x.v_name != y.v_name) (constr_free_i_vars cs) *)
 
  
