(* ---------------------------------------------------------------------- *)
(* Unary typechecking engine for BiRRelCost                               *)
(* ---------------------------------------------------------------------- *)

open Tycheck
module UnaryTy =
struct
      type ty = Syntax.un_ty
    end
    
module AbstractUnary = TyCheck(UnaryTy)
     
open AbstractUnary
open Fresh_var
open Syntax
open IndexSyntax
open Constr
open Ctx
open Ty_error
open Support.FileInfo


module Opt = Support.Options
module Err = Support.Error


let typing_error fi = Err.error_msg    Opt.TypeChecker fi
let typing_error_pp = Err.error_msg_pp Opt.TypeChecker



(* Check whether uty1 is a subtype of uty2, generating the necessary constraints along the way. *)
let rec check_usubtype (i: info) (uty1 : un_ty) (uty2 : un_ty) : constr checker =
  let fail = fail i @@ NotUSubtype (uty1, uty2) in
  match uty1, uty2 with
  | UTyPrim pty1, UTyPrim pty2 ->
    if pty1 = pty2 then return_ch empty_constr else fail
  | UTyList (n, ty1), UTyList (n', ty2) -> check_size_eq n n' (check_usubtype i ty1 ty2)
  | UTySum (ty1, ty2), UTySum (ty1',ty2') -> check_usubtype i ty1 ty1' >> check_usubtype i ty2 ty2'
  | UTyProd (ty1, ty2), UTyProd (ty1',ty2') -> check_usubtype i ty1 ty1' >> check_usubtype i ty2 ty2'
  | UTyArr (ty1,mo, k, ty2), UTyArr (ty1',mo', k', ty2') ->
     if mo = mo' then check_size_leq k k' (check_usubtype i ty1' ty1 >> check_usubtype i ty2 ty2')
     else fail
  | UTyForall (x,s, mo, k, ty), UTyForall (x',s', mo', k', ty') ->
     if (mo = mo' && s = s') then
       let m = fresh_evar s in
       let x_m = IVar m in
       (m |::| s) i
          (check_size_leq (iterm_subst x x_m k) (iterm_subst x' x_m k')
              (check_usubtype i (un_ty_subst x x_m ty) (un_ty_subst x' x_m ty')))
     else fail
  | UTyExists (x,s, ty), UTyExists (x',s', ty') ->
     if  x = x' && s = s' then
        (x |::| s) i (check_usubtype i ty ty')
     else fail
  | _, _ -> fail



(** Check whether uty1 is a subtype of uty2, generating the necessary
    constraints along the way. **)
let rec check_usubtype (i: info) (uty1 : ty) (uty2 : ty) : constr checker =
  let fail = fail i @@ NotUSubtype (uty1, uty2) in
  match uty1, uty2 with
  | UTyPrim pty1, UTyPrim pty2 -> if pty1 = pty2 then return_ch empty_constr
                                  else fail
  | UTyList (n, ty1), UTyList (n', ty2) -> check_size_eq n n' (check_usubtype i ty1 ty2)
  | UTySum (ty1, ty2), UTySum (ty1',ty2') -> check_usubtype i ty1 ty1' >> check_usubtype i ty2 ty2'
  | UTyProd (ty1, ty2), UTyProd (ty1',ty2') -> check_usubtype i ty1 ty1' >> check_usubtype i ty2 ty2'
  | UTyArr (ty1,mo, k, ty2), UTyArr (ty1',mo', k', ty2') ->
     if mo = mo' then check_size_leq k k' (check_usubtype i ty1' ty1 >> check_usubtype i ty2 ty2')
     else fail
  | UTyForall (x,s, mo, k, ty), UTyForall (x',s', mo', k', ty') ->
     if (mo = mo' && s = s') then
       let m = fresh_evar s in
       let x_m = IVar m in
       (m |::| s) i
          (check_size_leq (iterm_subst x x_m k) (iterm_subst x' x_m k')
              (check_usubtype i (un_ty_subst x x_m ty) (un_ty_subst x' x_m ty')))
     else fail
  | UTyExists (x,s, ty), UTyExists (x',s', ty') ->
     if  x = x' && s = s' then
       (x |::| s) i (check_usubtype i ty ty')
     else fail
  | UTyCs(c1, ty1), UTyCs(c2, ty2) -> 
     check_usubtype i ty1 ty2 >>=
       fun cs_b -> return_ch (CAnd(CImpl(c1, c2), cs_b))

  | _, _ -> fail


                 
(** [inferType e] infers that expression [e] has type [un_ty] along
    with cost [k] in context [ctx]. If it does, it returns [un_ty
    inferer: (un_ty, k, psi)] where all the free existential variables
    occuring in un_ty and k are declared in psi, otherwise it raises
    an exception. *)
let rec inferUType (e: expr) : ty inferer  =
  match e with
  | Var (i, vi) -> (get_var_ty i vi <<= fun ty ->  (return_inf ty))
  | Prim (i, ep) -> return_inf(un_type_of_prim ep )
  | Fst(i, e) -> inferUType e <<= infer_proj i fst
  | Snd(i, e) -> inferUType e <<= infer_proj i snd
  | App (i, e1, e2) -> infer_app (inferUType e1) i e2
  | IApp (i, e) -> infer_iapp (inferUType e) i
  | UAnno (i, e, uty, k) -> infer_check_anno i e uty k
  |  _ -> fail (expInfo e) (Internal ("no inference rule, try annotating the expression please."))

and infer_check_anno i e uty k =
  fun ctx ->
    match checkUType e uty (ctx, Some k) with
    | Right c -> Right (uty, c, [], Some k)
    | Left err -> Left err

and infer_iapp m i =
  fun ctx ->
    match m ctx with
    | Right (uty, c, psi, k) ->
      begin
        match uty with
        | UTyForall(x, s, mu', k_e, ty) ->
          let v = fresh_evar s in
          let witn = IVar v in
          let mu = ctx.exec_mode in
          let k' = Core.Std.Option.map ~f:(fun k -> add_costs (k,iterm_subst x witn k_e)) k in 
          if mu = mu'
          then
            Right (un_ty_subst x witn ty, c, (v,s):: psi, k')
          else fail i (WrongMode (mu, mu')) ctx
        | _ -> fail i (WrongUShape (uty, "index quantified (forall) ")) ctx
      end
    | Left err -> Left err

and check_mode i mu (m : constr checker) : constr checker =
  fun(ctx, k) ->
    let mu' = ctx.exec_mode in
    if mu = mu'
    then m(ctx, k)
    else fail i (WrongMode (mu, mu')) (ctx,k)


and infer_app m i e2 =
  m =<-> (fun uty _ ->
      match uty with
      | UTyArr(ty1, mu', k'', ty2) ->
        [(check_mode i mu' (checkUType e2 ty1), ty2, ISucc k'')]
      | _ -> [(fail i (WrongUShape (uty, "function")), UTyPrim (UPrimInt), IZero)])

and infer_proj i f =
  fun uty ->
    match uty with
    | UTyProd (ty1, ty2) ->  return_inf(f (ty1, ty2))
    | _ -> fail i (WrongUShape (uty, "product"))

(** [checkUType e] verifies that expression [e] has unary type [uty]
    in the context [ctx] with the cost [k]. If
    it does, it returns unit, otherwise it raises an exception. *)
and checkUType (e: expr) (uty : ty) : constr checker =
  match e, uty with
  (* Constrained type intro *)
  | _, UTyCs(c, ty) -> checkUType e ty >>= fun cs_b -> return_ch (CAnd(c, CImpl(c, cs_b)))
  (* Primitive expressions *)
  |  Prim (i, ep), tp -> if tp = un_type_of_prim ep
    then return_leaf_ch else fail i @@ WrongUShape (tp, "primitive")
  |  Fix(i, vi_f, vi_x, e), _ -> check_fix i vi_f vi_x e uty
  (* List type expressions *)
  | Nil i, _ -> check_nil i uty
  | Cons(i, e1, e2), _ -> check_cons e1 e2 i uty
  | CaseL(i,e, e_n, x_h, x_tl, e_c), _ -> check_case_list i e e_n x_h x_tl e_c uty
  (* Sum type expressions *)
  | Inl(i, e), UTySum (ty1,_) -> checkUType e ty1
  | Inr(i, e), UTySum (_,ty2) -> checkUType e ty2
  | Case(i,e, x_l, e_l, x_r, e_r), _ -> check_case_sum i e x_l e_l x_r e_r uty
  (* If statement *)
  | IfThen(i, e, el, er), _ -> check_if i e el er uty
  (* Pairs *)
  | Pair(i, e1, e2), _ ->
    begin
      match uty with
      | UTyProd (ty1,ty2) -> (checkUType e1 ty1) >> (checkUType e2 ty2)
      | _ -> fail i (WrongUShape (uty, "product"))
    end
  (* Index abstraction *)
  | ILam (i, e), UTyForall(x, s, mu, k, ty) ->
    check_body ((x |::| s) i
                  (with_mode mu (checkUType e ty))) k
  (* Existential introduction and elimination *)
  | Pack (i, e), _ -> check_pack i e uty
  | Unpack (i, e1, vi_x, e2), _ -> check_unpack i e1 vi_x e2 uty
  (* Let bound *)
  | Let (i, vi_x, e1, e2), _ ->
    inferUType e1 <->=
    (fun uty_x -> (vi_x  |:| uty_x) (checkUType e2 uty))
  (* Constrained type elim *)
  | CLet (i, vi_x, e1, e2), _ -> check_clet i vi_x e1 e2 uty
  | Contra i, _ -> return_ch empty_constr
  |  _, _ -> infer_and_check (expInfo e) e uty

and check_fix (i: info) (vi_f : var_info) (vi_x : var_info) (e : expr) (uty : ty) =
  match uty with
  | UTyArr(ty1, mu, k_fun, ty2) ->
    check_body ((vi_f |:| uty)
                  ((vi_x |:| ty1)
                     (with_mode mu (checkUType e ty2)))) k_fun
  | _ ->  fail i (WrongUShape (uty, "fuction"))

and check_body (m: constr checker) (k_fun : iterm) : constr checker =
  fun(ctx, k) ->
    match k with
    | Some k' -> 
      begin
        match m (ctx, Some k_fun) with
        | Right c ->  Right (CAnd(c, cost_cs ctx (IZero, k')))
        | Left err -> Left err
      end
    | None -> m (ctx, None)

and check_if (i : info) e el er uty =
  inferUType e <->=
  (fun uty_g ->
     match uty_g with
     | UTyPrim UPrimBool -> (checkUType el uty) >&&> (checkUType er uty)
     | _ -> fail i (WrongUShape (uty, "bool")))

and check_nil i uty =
  match uty with
  | UTyList(n, ty) -> check_size_eq n IZero return_leaf_ch
  | _ -> fail i (WrongUShape (uty, "list"))


and check_cons e1 e2 i uty =
  match uty with
  | UTyList(n, ty) ->
    checkUType e1 ty >>
    (* Introduce a new size variable and add it to the existential ctx*)
    let v = fresh_evar Size in
    let sz = IVar v in
    (v |:::| Size) i
      (* Check that (sz + 1 = n) *)
      (check_size_eq (n) (ISucc sz)
         (checkUType e2 (UTyList(sz, ty))))
  | _ -> fail i (WrongUShape (uty, "list"))


and check_case_list i e e_n x_h x_tl e_c uty =
  inferUType e <->=
  (fun uty_g ->
     match uty_g with
     | UTyList (n, tye) ->
       (* Nil case *)
       (assume_size_eq n IZero (checkUType e_n uty))
       >&&>
       (* Cons case *)
       (* Generate a fesh size variable *)
       let v = fresh_ivar Size in
       let sz = IVar v in
       (* Extend the index ctx with freshly gen. size*)
       (v |::| Size) i
         ((x_h |:| tye)
            (* Assume that n = sz + 1*)
            (assume_size_eq n (ISucc sz)
               ( (x_tl |:| UTyList(sz, tye)) (checkUType e_c uty))))
     | _ -> fail i (WrongUShape (uty, "list"))
  )

and check_case_sum i e x_l e_l x_r e_r  uty =
  inferUType e <->=
  (fun uty_g ->
     match uty_g with
     | UTySum (tyl, tyr) -> 
       ((x_l |:| tyl) (checkUType e_l uty)) >>>=
       fun c1 -> (x_r |:| tyr) (checkUType e_r uty) >>>=
       fun c2 -> return_ch (merge_cs c1 c2) 
     | _ -> fail i (WrongUShape (uty, "sum"))
  )

and check_pack i e uty =
  match uty with
  | UTyExists(x, s, ty) ->
    let v = fresh_evar s in
    let witness = IVar v in
    (v |:::| s) i (checkUType e (un_ty_subst x witness ty))
  | _ -> fail i (WrongUShape (uty, "existential"))

and check_unpack i e1 vi_x e2 uty =
  inferUType e1 <->=
  (fun uty_x ->
     match uty_x with
     | UTyExists(x, s, ty) ->
       (x |::| s) i ((vi_x |:| ty) (checkUType e2 uty))
     | _ -> fail i (WrongUShape (uty, "existential")))

and check_clet i vi_x e1 e2 uty =
  inferUType e1 <->=
  (fun csty ->
     match csty with
     | UTyCs(cs, uty_x) ->
        (vi_x |:| uty_x) (checkUType e2 uty) >>= fun cs_b -> return_ch (CImpl(cs, cs_b))
     | _ -> fail i (WrongUShape (uty, "constrained")))




and infer_and_check (i: info) (e: expr) (uty : ty) : constr checker =
  fun(ctx, k) ->
    match inferUType e ctx with
    | Right (inf_uty, c, psi_ctx, k') ->
      (match (check_usubtype i inf_uty uty (extend_e_ctx psi_ctx ctx, None)) with
       | Right c' ->
	  let cs = option_combine k' k (cost_cs ctx) |> Core.Std.Option.value ~default:CTrue in
          Right (quantify_all_exist psi_ctx (merge_cs (merge_cs c c') cs))
       | Left err -> Left err)
    | Left err' -> Left err'


let check_type ctx program uty k  =
  match checkUType program uty (ctx, k) with
  | Right c ->  c
  | Left err -> typing_error_pp  err.i pp_tyerr err.v
 
