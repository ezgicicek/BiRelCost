(* ---------------------------------------------------------------------- *)
(* Existential Elimination Engine with backtracking                       *)
(* ---------------------------------------------------------------------- *)

open Constr
open Syntax
open IndexSyntax
open Ctx
open Support.Options
open Support.Error



let elim_debug   fi = message 4 General fi
let dp = Support.FileInfo.dummyinfo


let rec check_scope_ctx (in_ctx : 'a context ) (cs: constr) : bool =
  let fvars = constr_free_i_vars cs in
  let ctx = List.map fst (in_ctx.ivar_ctx @ in_ctx.evar_ctx) in
  List.fold_left (fun acc x ->  List.mem x ctx && acc) true fvars
             
          
let rec elim (in_ctx : 'a context) (c: constr) sc =
  match c with
  | CAnd(c1,c2) -> elim in_ctx c2 (fun x -> elim in_ctx c1 (fun y -> sc (CAnd(y,x))))
  | COr(c1,c2) ->  
    (* Order seems to matter here: "reverse" testcase finds the wrong
       substitution in cons boxed case when h is a boxed type *)
    elim in_ctx c1 (fun x -> elim in_ctx c2 (fun y -> sc (COr(y,x)) ))
    (* The following takes foreover to find the right side *)
    (* elim in_ctx c2 sc;  elim in_ctx c1 sc *)
  | CForall(bi_x, i, s, c') ->
    elim (extend_i_var bi_x.v_name  s in_ctx) c' (fun x -> sc (CForall(bi_x, i, s,x)) )
  | CExists(bi_x, i, s, c') ->
     let in_ctx' =  (extend_e_var bi_x.v_name s in_ctx) in
     elim in_ctx' c'
       (fun x ->
         elim_debug dp "Id:%a@ \n and x :%a@\n." Print.pp_vinfo bi_x Print.pp_cs x;
         if i = Support.FileInfo.NOCHANGE then  sc (CExists(bi_x, i, s, x)) else
           (solve_sc x bi_x
              (fun witness () ->
                 match witness with
                 | IConst c when c < 0.0 -> ()
                 | _ -> 
                   elim_debug dp "Witness %a :@\n@ " Print.pp_iterm witness;
                   let c_subst = constr_simpl (constr_subst bi_x witness x) in                        
                   if (check_scope_ctx (in_ctx') c_subst) then
                     (elim_debug dp "Subst for %a :@\n@[%a@]@." 
                        Print.pp_vinfo bi_x Print.pp_cs c_subst;
                      sc c_subst) else ())
           );
         sc (CExists(bi_x, i, s, x)))
           
  | CImpl(c1,c2) -> elim in_ctx c2 (fun x -> sc (CImpl(c1,x)) )
  | _ -> sc c
and
  solve_sc (c: constr) (ex_var : var_info) ssc =
  let rec rec_match c ssc  =
    match c with
    | COr(c1,c2) 
    | CAnd(c1,c2) ->
      rec_match c2 ssc; rec_match c1 ssc
 
    | CImpl(c1,c2) -> rec_match c2 ssc
    | CLeq(IVar x1, IVar x2) 
    | CEq(IVar x1, IVar x2) ->
       (* Make sure that we don't substitute the same variable for itself *)
       if x1 = x2 then ()
      (* We give priority to I <= ex_var *)
       else if x2 = ex_var then ssc (IVar x1) () 
       else if x1 = ex_var then ssc (IVar x2) ()else ()
 
    | CEq(IVar x, s) 
    | CEq(s, IVar x) 
    | CLeq(IVar x, s) 
    | CLeq(s, IVar x) -> if x = ex_var then ssc s () else ()

    | CLeq(IMinus(IVar x, s1), s2) 
    | CEq (IMinus(IVar x, s1), s2) 
    | CEq (s1, IMinus(IVar x, s2))
    | CLeq(s1, IMinus(IVar x, s2)) -> 
       if x = ex_var && not (List.mem ex_var (iterm_free_i_vars s1 @ iterm_free_i_vars s2)) 
       then ssc (IAdd(s1, s2)) () else ()
 
    | CEq(s, IMinus(IMinus(IVar x, s1), s2))
    | CLeq(s, IMinus(IMinus(IVar x, s1), s2)) when x = ex_var && not (List.mem ex_var (iterm_free_i_vars s1 @ iterm_free_i_vars s2)) -> ssc (IAdd(s, IAdd(s1, s2))) () 
 
   | CForall(x, i,s, c')   
   | CExists(x, i ,s, c') -> rec_match c' ssc

   | CEq(_,_) 
   | CLeq(_,_)
   | CTrue
   | CFalse -> ()
  
  in rec_match c ssc
