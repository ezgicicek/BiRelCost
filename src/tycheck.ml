(* ---------------------------------------------------------------------- *)
(* Core Typechecking Engine for BiRelCost                                 *)
(* ---------------------------------------------------------------------- *)

open Tycheck_sigs

module TyCheck (Ty : CH_TYPE) =
  struct
    open IndexSyntax
    open Fresh_var
    open Constr
    open Ctx
    open Syntax
    open Support.FileInfo
    open Core.Std

    module Opt = Support.Options

    let typing_err fi = Support.Error.error_msg  Opt.TypeChecker fi

    type 'a ty_error = 
          Right of 'a
        | Left  of Ty_error.ty_error_elem withinfo
    type ty = Ty.ty
   
    type cost = iterm option
    type ch_ctx = ty context * cost
    type inf_ctx = ty context

   (* Reader/Error monad for  type-checking *)
    type 'a checker = ch_ctx -> 'a ty_error

    let return_ch cs  = fun ch_ctx -> Right cs

    let (>>=) (m : 'a checker) (f : 'a -> 'b checker) : 'b checker =
      fun ch_ctx ->
      match m ch_ctx with
      | Right res -> f res ch_ctx
      | Left e    -> Left e

    (* Reader/Error monad for type-inference *)
    type 'a inferer =  inf_ctx -> ('a * constr * sort ctx * cost) ty_error

    let cost_cs ctx (k1, k2) =
      match ctx.exec_mode with
      | MaxEx -> CLeq(iterm_simpl k1,iterm_simpl k2)
      | MinEx -> CLeq(iterm_simpl k2,iterm_simpl k1)

    let if_cost k' = Option.map ~f:(fun _ -> k')
				
    let extend_if_cost v1 ctx k = 
      Option.value_map ~default:ctx 
		       ~f:(fun _ -> extend_e_var v1.v_name Cost ctx) k

    let (>>)  (m : constr checker) (m' : constr checker) : constr checker =
      fun (ctx, k) ->
      (* Generate two new cost meta variables *)
      let v1 = fresh_evar Cost in
      let v2 = fresh_evar Cost in
      let k1 =  (IVar v1) in
      let k2 =  (IVar v2) in
      (* Extend the existential ctx with the two generated vars *)
      let k1_ctx = extend_if_cost v1 ctx k in
      let k2_ctx = extend_if_cost v2 k1_ctx k in
      let k_cs = Option.value_map ~default:CTrue
      				  ~f:(fun k -> cost_cs ctx (add_costs(k1, k2), k)) k in
      (* Call the checker on the first premise with cost k1 *)
      begin
        match m (k1_ctx, if_cost k1 k) with
        | Right c1 ->
           begin
             (* Call the checker on the second premise with cost k2 *)
             match (m' (k2_ctx,if_cost k2 k)) with
             | Right c2 ->
                (* Combine the constraints of two checkers with the cost constraint k1+k2 <= k*)
                let base =  merge_cs c1 (merge_cs c2 k_cs) in
                (* Existentially quantify over the cosntraint with the new costs k1 and k2*)
		let c_quant = CExists(v1, UNKNOWN, Cost, CExists(v2, UNKNOWN, Cost, base)) in 
      		let cs_res = Option.value_map ~default:base
      					      ~f:(fun _ -> c_quant) k in
                Right cs_res
             | Left err' -> Left err'
           end
        | Left err  -> Left err
      end

      let (>>>=)  (m : 'a checker) (f : 'a -> 'b checker) : 'b checker =
        fun (ctx, k) ->
          match m (ctx, k) with
          | Right c -> f c (ctx,k)
          | Left err  -> Left err


     (* Monadic combination with conjunction of contraints; ignores function *)
      let (>&&>) m1 m2 = 
	m1 >>= (fun c1 -> m2 >>= fun c2 -> return_ch (merge_cs c1 c2))

      let handle_fail m1 m2 =
	fun ch_ctx ->
	match m1 ch_ctx with
	  | Right c -> Right c
	  | Left _ -> m2 ch_ctx

    (* Monadic combination with disjunction of constraints ; ignores function *)
      let (>||>) m1 m2 =
	(handle_fail m1 m2) >>=  
		 (fun c1 -> handle_fail m2 (return_ch c1) >>=
			      fun c2 -> return_ch (COr(c1,c2)))

      (* Type inference *)
      let (<<=) (m : 'a inferer) (f : 'a -> 'b inferer) : 'b inferer =
        fun ctx ->
          match m ctx with
          | Right (res, c, psi, k) ->
             begin
               match (f res ctx) with
               | Right (res',c', psi', k') -> 
                  Right (res', merge_cs c c', psi @ psi', (sum_costs k k'))
               | Left err' -> Left err'
             end
          | Left err  -> Left err


      (* Instead of generating an fresh cost variable, we simply subtract
         the inference cost from the checking cost. Otherwise, merge-min breaks
         due to complicated existential substitution *)
      let (<->=) (m : ty  inferer) (f : ty  -> constr checker) : constr checker =
        fun (ctx, k) ->
          match (m ctx) with
          | Right (ty, c, psi, k') ->
            begin
              match (f ty (ctx, option_combine k k' (fun (ik,k') -> IMinus(ik, k')))) with
              | Right c' -> Right (quantify_all_exist psi (merge_cs c c'))
              | Left err' -> Left err'
            end          
          | Left err -> Left err

      let (=<->) (m : ty inferer) (f: ty -> Ctx.heurMode -> (constr checker * ty * iterm) list ) : ty inferer =
        fun ctx ->
        match m ctx with
        | Right (ty, c, psi, k) ->
           (* Generate a new cost meta variable *)
           let v = fresh_evar Cost in
           let k' = (IVar v) in
           begin
             let fl = f ty ctx.heur_mode in
             let (m', ty_inf, k'') = List.hd_exn fl in
             let psi' = Option.value_map ~default:psi ~f:(fun _ -> (v, Cost) :: psi) k in
             let k_ctx = Option.value_map ~default:ctx ~f:(fun _-> extend_e_ctx ((v, Cost) :: psi) ctx) k in
             let k_res k'' = Option.map ~f:(fun k -> add_costs(k'', add_costs(k,k'))) k in
             match m' (k_ctx ,if_cost k' k) with
             | Right c' -> Right (ty_inf, merge_cs c c', psi', k_res k'')
             | Left err' -> if List.length fl = 1 then Left err'
                            else
                              begin
                                let (m', ty_inf, k'') = (List.nth_exn fl 1) in
                                match m' (extend_e_ctx psi' ctx , Some k') with
                                | Right c'  -> Right (ty_inf, merge_cs c c', psi', k_res k'')
                                | Left err' -> Left err'
                              end
           end
        | Left err -> Left err

      let when_cost ctx k =
	match ctx.cost_mode with
	  | WithCost -> Some k
	  | _ -> None

      let return_inf(x : 'a) : 'a inferer = 
	fun ctx -> Right (x, empty_constr, [], when_cost ctx IZero)

      let return_leaf_ch  = fun (ctx, k) -> 
        Right (Option.value_map ~default:CTrue ~f:(fun k' -> cost_cs ctx (IZero,k')) k)        


      let fail (i : info) (e : Ty_error.ty_error_elem) = fun _ ->
        Left { i = i; v = e }

      let get_infer_ctx : ty context inferer =
        fun ctx -> Right (ctx, empty_constr, [], None)

      let get_heur  : heurMode checker =
        fun (ctx,_) -> Right ctx.heur_mode

  
      let get_var_ty (i: info) (vi : var_info) : ty inferer =
        get_infer_ctx <<= fun ctx ->
          return_inf @@
            match (lookup_var vi.v_name ctx) with
              None ->  typing_err i "Identifier %s is unbound" vi.v_name
            | Some (v, uty) -> uty

 
     let with_new_ctx (f : ty context -> ty context) (m : 'a checker) : 'a checker =
        fun (ctx,k) -> m (f ctx, k)

      let with_mode (mu :mode) (m : 'a checker) : 'a checker =
        with_new_ctx (set_exec_mode mu) m

      let (|:|) (vi: var_info) (uty: ty) (m: constr checker) : constr checker =
        with_new_ctx (extend_var vi.v_name uty) m

      let (|:::|) (v: var_info) (s: sort) (i: info) (m: constr checker) : constr checker =
        with_new_ctx (extend_e_var v.v_name s) m
        >>= (fun cs -> return_ch @@ CExists(v, i, s, cs (* CAnd (CLeq(IZero, IVar v), cs) *)))

      let (|::|) (v: var_info) (s: sort) (i: info)(m: constr checker) : constr checker =
        with_new_ctx (extend_i_var v.v_name s) m
	>>=
	  (fun cs ->
	   let r_cs = 
	     match s with 
	     | Size -> CImpl(CAnd(CLeq(IZero, IVar v), CEq(IFloor(IVar v), ICeil (IVar v))),cs)
	     | _ -> cs 
	   in return_ch @@ CForall(v, i, s, r_cs))

	  
      let check_size_eq  (sl : iterm) (sr : iterm) (m: constr checker)  : constr checker =
	m >>= fun c -> return_ch @@ merge_cs c (CEq (sl,sr))

      let assume_size_eq  (sl : iterm) (sr : iterm) (m: constr checker)  : constr checker =
	m >>= fun c -> return_ch @@ CImpl (CEq (sl,sr), c)

      let assume_size_leq  (sl : iterm) (sr : iterm) (m: constr checker)  : constr checker =
        m >>= fun c -> return_ch @@ CImpl (CLeq (sl,sr), c)

      let check_size_leq  (sl : iterm) (sr : iterm) (m: constr checker)  : constr checker =
        m >>= fun c -> return_ch @@ merge_cs c (CLeq (sl,sr))


end


