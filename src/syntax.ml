(* ---------------------------------------------------------------------- *)
(* Abstract Syntax Tree for types and expressions                         *)
(* ---------------------------------------------------------------------- *)

open Format
open Support.FileInfo
open IndexSyntax
open Constr 


(* Execution modes  *)
type mode =
    MaxEx
  | MinEx

(* Types *)

(* Unary primitive types *)
type un_ty_prim =
    UPrimInt
  | UPrimUnit
  | UPrimBool

(* Binary primitive types *)
type bi_ty_prim =
    BPrimInt
  | BPrimUnit
  | BPrimBool

let proj_prim_bi_ty bprim = 
match bprim with
      BPrimInt  -> UPrimInt
    | BPrimUnit -> UPrimUnit
    | BPrimBool -> UPrimBool

let lift_prim_bi_ty uprim = 
match uprim with
      UPrimInt  -> BPrimInt
    | UPrimUnit -> BPrimUnit
    | UPrimBool -> BPrimBool

(* Unary types *)
type un_ty =
  (* Primitive types *)
  | UTyPrim  of un_ty_prim

  (* ADT *)
  | UTySum     of un_ty * un_ty
  | UTyProd    of un_ty * un_ty
  (* Functional type *)
  | UTyArr     of un_ty * mode * iterm * un_ty

  (* Quantified types *)
  | UTyForall of var_info * sort * mode * iterm * un_ty
  | UTyExists of var_info * sort * un_ty

  (* List types *)
  | UTyList    of iterm * un_ty

  (* Constrained types *)
  | UTyCs    of constr * un_ty



(* Substitution un_ty[I/i] for index vars *)
let rec un_ty_subst i it uty = 
  let f_it = (iterm_subst i it) in
  let utf = un_ty_subst i it in
  match uty with
  | UTyPrim tp            -> UTyPrim tp
  (* ADT *)
  | UTySum(uty1, uty2)    -> UTySum(utf uty1, utf uty2)
  | UTyProd(uty1, uty2)   -> UTyProd(utf uty1, utf uty2)

  (* Functional type *)
  | UTyArr(uty1, mo, k, uty2) -> UTyArr(utf uty1, mo, f_it k, utf uty2)
                                    
  (* Quantified types *)
  | UTyForall(b, s, mu, k, uty')-> UTyForall(b, s, mu, f_it k,  utf uty')
  | UTyExists(b, s, uty')  -> UTyExists(b, s, utf uty')

  (* Dependent types *)
  | UTyList (sz, uty')     -> UTyList(f_it sz, utf uty')

  (* Constrained types *)
  | UTyCs (cs, uty')      -> UTyCs(constr_subst i it cs, utf uty')


                         
(* Binary types*)
type bi_ty =
  (* Primitive types *)
  | BTyPrim  of bi_ty_prim

  (* ADT *)
  | BTySum     of bi_ty * bi_ty
  | BTyProd    of bi_ty * bi_ty

  (* Functional type *)
  | BTyArr     of bi_ty * iterm * bi_ty

  (* Quantified types *)
  | BTyForall of var_info * sort * iterm * bi_ty
  | BTyExists of var_info * sort * bi_ty

  (********************************************************************)
  (* Dependent types *)
  | BTyList    of iterm * iterm * bi_ty

  (********************************************************************)
  (* Unrelated types *)
  | BTyUnrel    of un_ty * un_ty

  (********************************************************************)
  (* Boxed types *)
  | BTyBox    of bi_ty

 (* Constrained types *)
  | BTyCs    of constr * bi_ty



(* Substitution un_ty[I/i] for index vars *)
let rec bi_ty_subst i it bty = 
  let f_it = (iterm_subst i it) in
  let btf = bi_ty_subst i it in
  match bty with
  | BTyPrim tp            -> BTyPrim tp
  (* ADT *)
  | BTySum(bty1, bty2)    -> BTySum(btf bty1, btf bty2)
  | BTyProd(bty1, bty2)   -> BTyProd(btf bty1, btf bty2)

  (* Functional type *)
  | BTyArr(bty1, k, bty2) -> BTyArr(btf bty1, f_it k, btf bty2)
                                    
  (* Quantified types *)
  | BTyForall(b, s, k, bty')-> BTyForall(b, s, f_it k,  btf bty')
  | BTyExists(b, s, bty')  -> BTyExists(b, s, btf bty')

  (* Dependent types *)
  | BTyList (sz, ch, bty') -> BTyList(f_it sz, f_it ch, btf bty')

  (* Unrelated types *)
  | BTyUnrel (uty1, uty2)  -> BTyUnrel (un_ty_subst i it uty1, un_ty_subst i it uty2)

  (* Boxed types *)
  | BTyBox bty'            -> BTyBox (btf bty')

  (* Constrained types *)
  | BTyCs (cs, bty')       -> BTyCs(constr_subst i it cs, btf bty')

(* Projection for binary types *)
let rec bi_ty_proj (isLeft: bool) (bty : bi_ty) : un_ty =
  let btp = bi_ty_proj isLeft in
  match bty with
  | BTyPrim tp            -> UTyPrim (proj_prim_bi_ty tp)
  (* ADT *)
  | BTySum(bty1, bty2)    -> UTySum (btp bty1, btp bty2)
  | BTyProd(bty1, bty2)   -> UTyProd(btp bty1, btp bty2)

  (* Functional type *)
  | BTyArr(bty1, k, bty2) -> if isLeft then UTyArr(btp bty1, MaxEx, IInfty, btp bty2) 
    				       else UTyArr(btp bty1, MinEx, IZero, btp bty2)
        
  (* Quantified types *)
  | BTyForall(b, s, k, bty')-> if isLeft then UTyForall(b, s, MaxEx, IInfty, btp bty') 
    				         else UTyForall(b, s, MinEx, IZero, btp bty')
  | BTyExists(b, s, bty')  -> UTyExists(b, s, btp bty')

  (* Dependent types *)
  | BTyList (sz, ch, bty') -> UTyList(sz, btp bty')

  (* Unrelated types *)
  | BTyUnrel (uty1, uty2)  -> if isLeft then uty1 else uty2

  (* Boxed types *)
  | BTyBox bty'            -> btp bty'

  (* Constrained types *)
  | BTyCs (cs, bty')       -> UTyCs(cs, btp bty')


(*********************************************************************)
(* Terms *)

(* Primitive Terms *)
type exp_prim =
    PrimTUnit
  | PrimTInt    of int
  | PrimTBool   of bool

let un_type_of_prim t = match t with
    PrimTUnit       -> UTyPrim UPrimUnit
  | PrimTInt _      -> UTyPrim UPrimInt
  | PrimTBool _     -> UTyPrim UPrimBool

let bi_type_of_prim t = match t with
    PrimTUnit       -> BTyPrim BPrimUnit
  | PrimTInt _      -> BTyPrim BPrimInt
  | PrimTBool _     -> BTyPrim BPrimBool

(*********************************************************************)
(* Expressions with information for error messages *)
type expr =
  (* Variable*)
  | Var of info * var_info
        
  (* Primitive exps *)
  | Prim of info * exp_prim
    
  (* Function definition and application *)
  | Fix of info * var_info * var_info * expr
  | App of info * expr * expr

  (* List constructors and pattern match *)
  | Nil of info                         		
  | Cons of info * expr * expr
  | CaseL of info * expr * expr *
            var_info * var_info * expr
            
  (* ADT: sum types  *)
  | Inl   of info * expr
  | Inr   of info * expr
  | Case  of info * expr * var_info * expr *
             var_info * expr
  
  (* ADT: product types  *)
  | Pair  of info * expr * expr
  | Fst   of info * expr
  | Snd   of info * expr

  (* If-then-else *)
  | IfThen of info * expr * expr * expr

  (* Annotated exprs *)
  | UAnno of info * expr * un_ty * iterm
  | BAnno of info * expr * bi_ty * iterm

  (* Let-binding *)
  | Let of info * var_info * expr * expr

  (* Index abstraction and application *)
  | ILam of info * expr
  | IApp of info * expr

  (* Existential index intro and elim forms*)
  | Pack of info * expr
  | Unpack of info * expr * var_info * expr

  (* Constrained expressions *)
  | CExpr of info * expr
  | CLet of info * var_info * expr * expr
  | Contra of info


let rec is_equal_exp eL eR : bool = 
  match eL, eR with
  | Var(_, v1), Var(_, v2) -> v1 = v2
  | Prim(_, p1), Prim(_, p2) -> p1 = p2
  | Fix(_,f1, x1, e1), Fix(_,f2, x2, e2) -> f1 = f2 && x1 = x2 && is_equal_exp e1 e2
  | Inl(_, e), Inl(_, e') | Inr(_, e), Inr(_, e') 
  | Fst(_, e), Fst(_, e') | Snd(_, e), Snd(_, e')
  | Pack(_, e), Pack (_, e') 
  | ILam(_, e), ILam (_, e') 
  | IApp(_, e), IApp (_, e') 
  | CExpr(_, e), CExpr(_, e') -> is_equal_exp e e'

  | App(_, e1, e2), App(_, e1', e2') 
  | Cons(_, e1, e2), Cons(_, e1', e2') 
  | Pair(_, e1, e2), Pair(_, e1', e2') -> is_equal_exp e1 e1' && is_equal_exp e2 e2'

  | Case(_, e, x, e1, y, e2), Case(_, e', x', e1', y', e2') ->  x = x' && y = y' && is_equal_exp e1 e1' && is_equal_exp e2 e2'

  | CaseL(_, e, e1, h, tl, e2), CaseL(_, e', e1', h', tl', e2') -> h = h' && tl = tl' && is_equal_exp e e' && is_equal_exp e1 e1' && is_equal_exp e2 e2'
  | Let (_, x, e1, e2), Let (_, x', e1', e2')  
  | Unpack(_, e1, x, e2), Unpack(_, e1', x', e2')  
  | CLet (_, x, e1, e2), CLet (_, x', e1', e2') -> x = x' && is_equal_exp e1 e1' && is_equal_exp e2 e2'
  | IfThen (_, e, e1, e2), IfThen (_, e', e1', e2') -> is_equal_exp e e' && is_equal_exp e1 e1' && is_equal_exp e2 e2'
  | Nil i, Nil i' -> true
  | Contra i, Contra i' -> true
  | UAnno(i, e, uty, k), UAnno(i', e', uty', k') -> is_equal_exp e e' && k = k' && uty = uty'
  | BAnno(i, e, bty, k), BAnno(i', e', bty', k') -> is_equal_exp e e' && k = k' && bty = bty'
  | _,_ -> eL = eR


let rec exp_free_vars (e: expr) = 
  match e with
  | Prim (_, _) 
  | Nil _  
  | Contra _   -> []
  | Var(_, x)  -> [x.v_name]

  | Inl(_, e) 
  | Fst(_, e)  
  | Snd(_, e)  
  | Inr(_, e)  
  | UAnno (_, e, _, _) 
  | BAnno (_, e, _, _) 
  | ILam(_, e)  
  | IApp(_, e) 
  | Pack(_, e)
  | CExpr(_, e)  -> exp_free_vars e
                    
  | App(_, e1, e2)                                                          
  | Pair(_, e1, e2) 
  | Cons(_, e1, e2) -> exp_free_vars e1 @ exp_free_vars e2

  | IfThen (_, e, e1, e2) -> exp_free_vars e1 @ exp_free_vars e2 @ exp_free_vars e
                                                               
  | Fix (_, f, x, e') ->
    List.filter (fun vi_x -> vi_x != f.v_name && vi_x != x.v_name) (exp_free_vars e')

  | CaseL(_, e', e1, h, tl, e2) -> 
    (exp_free_vars e') @  (exp_free_vars e1) @ 
    (List.filter (fun x -> x != h.v_name && x != tl.v_name) (exp_free_vars e2))

  | Case(_, e, x, e1, y, e2) ->(exp_free_vars e) @ 
    (List.filter (fun vi_x -> vi_x != x.v_name ) (exp_free_vars e1)) @ 
    (List.filter (fun vi_x -> vi_x != y.v_name ) (exp_free_vars e2))
  
  | Let (_, x, e1, e2)  
  | Unpack(_, e1, x, e2)  
  | CLet (_, x, e1, e2)   ->  
    (exp_free_vars e1) @ (List.filter (fun vi_x -> vi_x != x.v_name)  (exp_free_vars e2))


(************************************************************************)
(* Info extraction *)
let rec expInfo = function 
    Var(i, _) 
  | Prim(i, _)

  | Fix (i, _, _, _)

  | App(i, _, _)
  | Nil i  
  | Cons(i, _, _)
  | CaseL(i, _, _, _, _, _)

  | Inl(i, _)
  | Inr(i, _)
  | Case(i, _, _, _, _, _)

  | Pair(i, _, _)
  | Fst(i, _)
  | Snd(i, _)

  | IfThen (i, _, _, _)

  | UAnno (i, _, _, _)
  | BAnno (i, _, _, _)

  | Let (i, _, _, _)

  | ILam(i, _)
  | IApp(i, _) 

  | Pack(i, _)
  | Unpack(i, _, _, _)

  | CExpr(i, _)
  | CLet (i, _, _, _)
  | Contra i           -> i





