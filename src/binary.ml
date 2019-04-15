(* ---------------------------------------------------------------------- *)
(* Relational typechecking engine for BiRelCost                           *)
(* ---------------------------------------------------------------------- *)

open Tycheck

module BinaryTy =
struct
  type ty = Syntax.bi_ty
end
    

module AbstractBinary = TyCheck(BinaryTy)
     
open AbstractBinary
open Fresh_var
open Syntax
open IndexSyntax
open Constr
open Ctx
open Ty_error
open Support.FileInfo

module Opt = Support.Options
module Err = Support.Error


let typing_error_pp = Err.error_msg_pp Opt.TypeChecker


let rec lift2bi_ty (uty : un_ty) : bi_ty =
match uty with
| UTyPrim pty                 -> BTyPrim (lift_prim_bi_ty pty)
| UTyProd(uty1, uty2)         -> BTyProd (BTyBox(lift2bi_ty (uty1)), BTyBox(lift2bi_ty uty2))
| UTySum(uty1, uty2)          -> BTySum (BTyBox(lift2bi_ty uty1), BTyBox(lift2bi_ty uty2))
| UTyArr(uty1, _, _, uty2)    -> BTyArr (BTyBox (lift2bi_ty uty1), IZero, BTyBox (lift2bi_ty uty2))
| UTyForall(i, s, _, _, uty') -> BTyForall(i, s, IZero, BTyBox(lift2bi_ty uty'))
| UTyExists(i, s, uty')       -> BTyExists(i, s, BTyBox (lift2bi_ty uty'))
| UTyList(n, uty')            -> BTyList(n, IZero, BTyBox(lift2bi_ty uty'))
| UTyCs(c, uty')              -> BTyCs(c, BTyBox(lift2bi_ty uty'))



let push_box (bty: bi_ty) : bi_ty =
let aux bty =
  match bty with
  | BTyPrim pty -> bty
  | BTyProd(bty1, bty2)    -> BTyProd(BTyBox bty1, BTyBox bty2)
  | BTyArr(bty1, k, bty2)  -> BTyArr(BTyBox bty1, IZero, BTyBox bty2)
  | BTyForall(i, s, k, ty) -> BTyForall(i, s, IZero, BTyBox ty)
                                
  | BTyUnrel(UTyArr(uty1, _, _, uty2),
             UTyArr(uty1', _, _, uty2')) ->
    BTyArr(BTyBox(BTyUnrel(uty1, uty1')), IZero, BTyBox(BTyUnrel(uty2, uty2')))
  | BTyUnrel(UTyForall(i, s, _, _, ty),
             UTyForall(i', s', _, _, ty'))  ->
    BTyForall(i, s, IZero, BTyBox (BTyUnrel(ty,ty')))
  | BTyUnrel(UTyProd(uty1, uty2),
             UTyProd(uty1', uty2')) ->
    BTyProd(BTyBox(BTyUnrel(uty1,uty1')), BTyBox(BTyUnrel(uty2,uty2')))
  | BTyUnrel(UTyPrim pty1, UTyPrim pty2) when pty1 = pty2 -> BTyPrim (lift_prim_bi_ty pty1)
  | _ -> bty
in match bty with
  | BTyBox (BTyBox ty) -> aux ty
  | BTyBox ty -> aux ty
  | _ -> bty


(* Check whether bty1 is a subtype of bty2, generating the necessary constraints along the way. *)
let rec check_bsubtype (i: info) (bty1 : bi_ty) (bty2 : bi_ty) : constr checker =
  let fail = fail i @@ NotBSubtype (bty1, bty2) in
   match bty1, bty2 with
  (* primitives *)
  | BTyPrim pty1, BTyPrim pty2 when pty1 = pty2 -> return_ch empty_constr
  | BTyPrim p, (BTyBox (BTyUnrel(UTyPrim p1, UTyPrim p2))) 
    when proj_prim_bi_ty p = p1 && p1 = p2-> return_ch empty_constr
  (* Lists *)
  | BTyList(n, alph, ty), BTyBox( BTyList(n', alph', ty')) ->
    check_size_eq n n' (check_size_eq alph (IZero) (check_bsubtype i (BTyBox ty) ty'))
  | BTyList (n, a,  ty1), BTyList (n', a', ty2) ->
    check_size_eq n n' (check_size_leq a a' (check_bsubtype i ty1 ty2))
  (* Sum and products *)
  | BTySum (ty1, ty2), BTySum (ty1',ty2')  -> check_bsubtype i ty1 ty1' >> check_bsubtype i ty2 ty2'
  | BTyProd (ty1, ty2), BTyProd (ty1',ty2') -> check_bsubtype i ty1 ty1' >> check_bsubtype i ty2 ty2'
  (* Fuction and forall types *)
  | BTyArr (ty1, k, ty2), BTyArr (ty1', k', ty2') ->
      check_size_leq k k' (check_bsubtype i ty1' ty1 >> check_bsubtype i ty2 ty2')
  | BTyForall (x,s, k, ty), BTyForall (x',s',  k', ty') ->
     if s = s' then
       let m = fresh_evar s in
       let x_m = IVar m in
       (m |::| s) i
          (check_size_leq (iterm_subst x x_m k) (iterm_subst x' x_m k')
              (check_bsubtype i (bi_ty_subst x x_m ty) (bi_ty_subst x' x_m ty')))
     else fail
 (* Existential types *)
  | BTyExists (x,s, ty), BTyExists (x',s', ty') ->
     if  x = x' && s = s' then
       (x |::| s) i (check_bsubtype i ty ty')
     else fail
 (* Constrained types *)
  | BTyCs(c1, ty1), BTyCs(c2, ty2) -> 
     check_bsubtype i ty1 ty2 >>=
       fun cs_b -> return_ch (CAnd(CImpl(c1, c2), cs_b))

  (* (\* Box Types *\) *)
 
  | BTyBox ty1, BTyBox (BTyBox ty2 as bty2') -> check_bsubtype i bty1  bty2'
   (* >||> check_bsubtype i ((\* push_box b *\)ty1) bty2 *)
  | BTyBox ty1, BTyBox ty2 -> check_bsubtype i (ty1) bty2 >||> check_bsubtype i ty1 ty2

  | BTyBox ty1, _ -> check_bsubtype i (push_box bty1) bty2 (* >||> check_bsubtype i ty1 bty2 *)

  (* Unrelated Types *)
  | BTyUnrel(uty1, uty2), BTyUnrel (uty1', uty2') -> check_unrel_subty i bty1 uty1 uty2
  | _, BTyUnrel (uty1, uty2) -> check_unrel_subty i bty1 uty1 uty2
  | _, _ -> fail 


and check_unrel_subty  i bty uty1 uty2 = 
 fun(ctx, k) ->
       let ectx = Ctx.empty_context.var_ctx in
       let lctx = (set_ctx ectx MaxEx ctx) in
       let rctx = (set_ctx ectx MaxEx ctx) in
   match (Unary.check_usubtype i (bi_ty_proj true bty) uty1) (lctx, None) with
   | Right c1 ->
     begin
     match (Unary.check_usubtype i (bi_ty_proj false bty) uty2) (rctx, None) with
     | Right c2 -> Right (merge_cs c1 c2)
     | Left err' -> Left err'
     end
   | Left err -> Left err
                 
(** [inferType e] infers that expression [e] has type [bi_ty] along with
    cost [k] in context [ctx]. If it does,
    it returns [bi_ty inferer: (bi_ty, k, psi)] where all the free
    existential variables occuring in bi_ty and k are declared in
    psi, otherwise it raises an exception. *)
let rec inferBType (ePair: expr * expr) : ty inferer  =
  match ePair with
  | Var (i1, vi1), Var(i2, vi2) -> 
    if vi1 = vi2
    then (get_var_ty i1 vi1 <<= fun y ->  (return_inf y))
    else infer_unrel (fst ePair) (snd ePair)
  | Prim (i1, ep1), Prim (i2, ep2) -> 
    if ep1 = ep2 then return_inf(BTyBox (bi_type_of_prim ep1))
    else infer_unrel (fst ePair) (snd ePair)
  | Fst(i1, e1), Fst(i2, e2) -> infer_handle_unrel ePair (inferBType (e1,e2) <<= infer_proj i1 fst)
  | Snd(i1, e1), Snd(i2, e2) -> infer_handle_unrel ePair (inferBType (e1,e2) <<= infer_proj i2 snd)
  | App (i, e1, e2), App (i', e1', e2') -> infer_app (inferBType (e1, e1')) i (e2, e2') ePair
  | IApp (i1, e1), IApp(i2, e2) -> infer_iapp (inferBType (e1,e2)) i1 ePair
  | BAnno (i1, e1, bty1, k1), BAnno (i2, e2, bty2, k2) ->
    if bty1 = bty2 && k1 = k2 then infer_check_anno i1 e1 e2 bty1 k1
    else fail (expInfo e1) (Internal ("Types and costs should match in annotated expressions!"))
  |  _ -> infer_unrel (fst ePair) (snd ePair)

and infer_unrel e1 e2 = 
  fun ctx -> 
    let u1ctx = List.map (fun (v, bty) -> (v, bi_ty_proj true bty)) ctx.var_ctx in
    let u2ctx = List.map (fun (v, bty) -> (v, bi_ty_proj false bty)) ctx.var_ctx in
    let lctx = (set_ctx u1ctx MaxEx ctx) in
    let rctx = (set_ctx u2ctx MinEx ctx) in
    let r = Unary.inferUType e1 (lctx) in
    match r with
    | Right (uty1, c1, ex_ctx1, k1) ->
      begin
        match Unary.inferUType e2 (rctx) with
        | Right (uty2, c2, ex_ctx2, k2) -> 
          Right (BTyUnrel(uty1, uty2), merge_cs c1 c2, ex_ctx1 @ ex_ctx2, option_combine k1 k2 (fun (x,y) -> IMinus(x,y)))
        | Left err -> Left err
      end
    | Left err -> Left err

and infer_check_anno i e1 e2 bty k =
  fun ctx ->
    (*TODO: only if nocost is disabled*)
    match checkBType (e1, e2) bty (ctx, Some k) with
    | Right c -> Right (bty, c, [], Some k)
    | Left err -> Left err


and infer_iapp m i eP =
  fun ctx ->
    match m ctx with
    | Right (bty, c, psi, k) ->
      begin
        match push_box bty, k with
        | BTyForall(x, s, k_e, ty), k->
          let v = fresh_evar s in
          let witn = IVar v in
          Right (bi_ty_subst x witn ty, c, (v,s):: psi, 
		 Core.Std.Option.map ~f:( fun k -> add_costs(k, iterm_subst x witn k_e)) k)
        | BTyUnrel(uty1, uty2) , _-> infer_unrel (fst eP) (snd eP) ctx
        | _ -> fail i (WrongBShape (bty, "index quantified (forall) ")) ctx
      end
    | Left err -> Left err


and infer_handle_unrel eP  (m: ty inferer) : ty inferer =
  fun ctx ->
    let mc = m ctx in 
    match mc with
    | Left err' when err'.v = Ty_error.SwitchPMatch -> infer_unrel (fst eP) (snd eP) ctx
    | _ ->  mc

and infer_app m i eP2 eP =
  infer_handle_unrel eP (m =<-> (fun inf_bty heur ->
      let pbty = push_box inf_bty in
      match inf_bty, heur with
      | BTyBox (BTyArr(ty1, k'', ty2) ), NoChange
      | BTyArr(ty1, k'', ty2), _ -> [(checkBType eP2 ty1, ty2, k'')]
      | BTyBox(BTyUnrel(_,_)), NoChange
      | BTyUnrel(_,_), _ -> [(fail i SwitchPMatch, BTyPrim (BPrimInt), IZero)]
      | _ -> 
      begin
        match pbty, inf_bty with
        | BTyArr(pty1, pk'', pty2), BTyBox(BTyUnrel(_)) -> 
          [(checkBType eP2 pty1, pty2, pk''); (fail i SwitchPMatch, BTyPrim (BPrimInt), IZero)]
        | BTyArr(pty1, pk'', pty2), BTyBox(BTyArr(ty1, k'',ty2)) -> [(checkBType eP2 pty1, pty2, pk''); (checkBType eP2 ty1, ty2, k'')]
        | _ -> [(fail i (WrongBShape (inf_bty, "function")), BTyPrim (BPrimInt), IZero)]
      end
    ))

and infer_proj i f =
  fun bty ->
    match push_box bty with
    | BTyProd (ty1, ty2) ->  return_inf(f (ty1, ty2))
    | BTyUnrel(_) -> fail i Ty_error.SwitchPMatch
    | _ -> fail i (WrongBShape (bty, "product"))

(** [checkBType e] verifies that expression [e] has unary type [bty]
    in the context [ctx] with the cost [k]. If
    it does, it returns unit, otherwise it raises an exception. *)
and checkBType (ePair : expr * expr) (bty : ty) : constr checker =
  match ePair, bty with
  (* Switch to unary mode for constructors typed with U(A1,A2) *)
  | (Fix(_, _, _, _), Fix(_, _, _, _)), BTyUnrel(uty1,uty2)
  | (Nil _, Nil _),  BTyUnrel(uty1,uty2) 
  | (Pair(_,_,_), Pair(_,_,_)), BTyUnrel(uty1,uty2)
  | (Cons(_,_,_), Cons(_,_,_)), BTyUnrel(uty1,uty2)
  | (Inl(_,_), Inl(_,_)), BTyUnrel(uty1,uty2)
  | (Inr(_,_), Inr(_,_)), BTyUnrel(uty1,uty2)
  | (ILam(_,_), ILam(_,_)), BTyUnrel(uty1,uty2)
  | (Pack(_,_), Pack(_,_)), BTyUnrel(uty1,uty2) -> check_unrel (fst ePair) (snd ePair) uty1 uty2

  (* Constrained type intro *)
  | _, BTyCs(c, ty) -> checkBType ePair ty >>=
			 fun cs_b -> return_ch (CAnd(c, CImpl(c, cs_b)))
  (* Primitive expressions *)
  | (Prim (i, ep1), Prim (i', ep2)), tp when tp = bi_type_of_prim ep1 && ep1 = ep2 -> 
    return_leaf_ch 
  |  (Fix(i1, vi_f1, vi_x1, e1), Fix(i2, vi_f2, vi_x2, e2)), _
    when vi_f1 = vi_f2 && vi_x1 = vi_x2 -> check_fix i1 vi_f1 vi_x1 (e1, e2) bty
  (* List type expressions *)
  | (Nil i1, Nil i2),  _ -> check_nil i1 bty
  | (Cons(i, e1, e2), Cons(i', e1', e2')), _ -> check_cons (e1, e1') (e2, e2') i bty
  | (CaseL(i,e, e_n, x_h, x_tl, e_c), CaseL(i',e', e_n', x_h', x_tl', e_c')), _
    when x_h = x_h' && x_tl = x_tl' ->
    check_case_list(* _heuristic *) i (e,e') (e_n,e_n') x_h x_tl (e_c, e_c') bty
  (* Sum type expressions *)
  | (Inl(i1, e1), Inl(i2, e2)), BTySum (ty1,_) -> checkBType (e1, e2) ty1
  | (Inr(i1, e1), Inr(i2, e2)), BTySum (_,ty2) -> checkBType (e1, e2) ty2
  | (Case(i,e, x_l, e_l, x_r, e_r), Case(i',e', x_l', e_l', x_r', e_r')), _
    when x_l = x_l' && x_r = x_r' -> check_case_sum i (e, e') x_l (e_l, e_l') x_r (e_r, e_r') bty
  (* If statement *)
  | (IfThen(i, e, el, er), IfThen(i', e', el', er')), _ -> check_if i (e, e') (el, el') (er, er') bty ePair
  (* Pairs *)
  | (Pair(i, e1, e2), Pair(i', e1', e2')), _ ->
    let pbty = push_box bty in
    begin match pbty with
      | BTyProd (ty1,ty2) -> (checkBType (e1, e1') ty1) >> (checkBType (e2, e2') ty2)
      | _ -> fail i (WrongBShape (bty, "product"))
    end
  (* Index abstraction *)
  | (ILam (i, e),  ILam (i', e')), BTyForall(x, s, k, ty) ->
    check_body ((x |::| s) i (checkBType (e, e') ty)) k
  (* Existential introduction and elimination *)
  | (Pack (i, e), Pack (i', e')), _ -> check_pack i (e, e') bty
  | (Unpack (i, e1, vi_x, e2), Unpack (i', e1', vi_x', e2')), _ 
    when vi_x = vi_x' -> check_unpack i (e1, e1') vi_x (e2, e2') bty
  (* Let bound *)
  | (Let (i, vi_x, e1, e2), Let (i', vi_x', e1', e2')), _ 
    when vi_x = vi_x' ->
    inferBType (e1, e1') <->=
    (fun bty_x -> (vi_x |:| bty_x) (checkBType (e2, e2') bty))
  (* Constrained type elim *)
  | (CLet (i, vi_x, e1, e2), CLet (i', vi_x', e1', e2')), _ 
    when vi_x = vi_x' -> check_clet i vi_x (e1, e1') (e2, e2') bty
  (* Contra returns immediately *)
  | (Contra i, Contra i'),  _ -> return_ch empty_constr
  (* Switch to inference *)
  |  _, _ -> infer_and_check (expInfo (fst ePair)) ePair bty


and check_fix (i: info) (vi_f : var_info) (vi_x : var_info) (eP: expr * expr) (bty : ty) =
  get_heur >>>= 
    fun heur ->
      let ch_heur_fix m ty1 ty2 k_fun = 
	if heur = NoChange then
	  begin
	    match ty1 with
	    | BTyList(n, alph, ty) ->
	       (* assume alpha = 0 *)
	       assume_size_eq IZero alph
		(check_body ((vi_f |:| bty) ((vi_x |:| (BTyList(n, IZero, ty)))
		 (check_no_change eP (checkBType eP ty2) >||> (checkBType eP ty2)))) k_fun)
	       >&&>
		 (* assume alpha >= 1 *)
		 assume_size_leq (ISucc IZero) alph m
				 
            | _ -> m
          end
        else m
      in
      match bty with
      | BTyArr(ty1, k_fun, ty2) ->
        let m = check_body ((vi_f |:| bty) ((vi_x |:| ty1) (checkBType eP ty2))) k_fun in
	ch_heur_fix m ty1 ty2 k_fun
      | BTyBox (BTyArr(ty1, k_fun, ty2)) ->
	 if is_equal_exp (fst eP) (snd eP) then
	    let with_no_cost m = fun(ctx, k) -> m (ctx, None) in
	    let ch_ctx = with_no_cost
			   (check_no_change_types (Fix(i, vi_f, vi_x, fst eP), snd eP)) in
	    let m = check_body ((vi_f |:| bty) 
				  ((vi_x |:| ty1) (ch_ctx  >&&> checkBType eP ty2))) k_fun in
	    ch_heur_fix m ty1 ty2 k_fun
	 else  fail i (WrongBShape (bty, "Boxed function types require identical expressions"))
    | _ ->  fail i (WrongBShape (bty, "fuction"))
    

and check_body (m: constr checker) (k_fun : iterm) : constr checker =
  fun(ctx, k) ->
    match k with
    | Some k -> 
      begin
        match m (ctx, Some k_fun) with
      | Right c ->  Right(CAnd(c, cost_cs ctx (IZero, k)))
      | Left err -> Left err
      end
    | None -> m (ctx, None)
    
and check_handle_unrel (m: constr checker) ePair bty : constr checker =
  fun(ctx, k) ->
    let mc = m(ctx, k) in 
    match mc with
    | Left err' when err'.v = Ty_error.SwitchPMatch -> 
      let uty1 = (bi_ty_proj true bty) in
      let uty2 = (bi_ty_proj false bty) in
      check_unrel (fst ePair) (snd ePair) uty1 uty2(ctx, k)
    | _ ->  mc

                  
and check_if (i : info) eP ePl ePr bty ePair =
 check_handle_unrel (inferBType eP  <->=
   (fun bty_g ->
      let pty = push_box bty_g in
      match pty with
      | BTyPrim BPrimBool -> (checkBType ePl bty) >> (checkBType ePr bty)
      | BTyUnrel _ -> 
        begin
          match bty with
          | BTyUnrel _ -> 
            (* Guard is unrelated, force switching to unary mode at top level *)
            fail i SwitchPMatch
          | _ -> fail i (WrongBShape (bty, "unrelated result"))
        end
      | _ -> fail i (WrongBShape (bty_g, "bool"))))
   ePair bty
   

and check_nil i bty =
  match bty with
  | BTyList(n, a, ty) -> check_size_eq n IZero return_leaf_ch
  | _ -> fail i (WrongBShape (bty, "list"))

and check_cons eP1 eP2 i bty =
  match bty with
  | BTyList(n, alph, ty) ->
    (* Introduce a new size variable and add it to the existential ctx*)
    let v = fresh_evar Size in
    let sz = IVar v in
    (v |:::| Size) i
      (* Check that (sz + 1 = n) *)
      (check_size_eq n (ISucc sz)
         begin
           (*-- Case for boxed head *)
           ( (checkBType eP1 (BTyBox ty)) >>
             (checkBType eP2 (BTyList(sz, alph, ty))))
           >||>
           (*-- Case for changeable head *)
           (* Introduce a new size variable and add it to the
              existential ctx *)
           (let v' = fresh_evar Size in
            let beta = IVar v' in
            (v' |:::| Size) i
              (checkBType eP1 ty >>
               check_size_leq (ISucc beta) (alph)
                 (checkBType eP2 (BTyList(sz, beta, ty)))))
         end
      )
  | _ ->  fail i (WrongBShape (bty, "list"))


and check_case_list i eP ePn x_h x_tl ePc bty =
  inferBType eP <->=
  fun bty_g ->
    match bty_g

 with
    | BTyBox(BTyList (n, alph, tye)) 
    | BTyList (n, alph, tye) ->
      (* Nil case *)
      (* (assume_size_eq n IZero (checkBType ePn bty))  *)
      (* >&&> *)
      (* Cons case *)
      (* Generate a fresh size variable *)
      let v = fresh_ivar Size in
      let sz = IVar v in
      (* Extend the index ctx with freshly gen. size*)
      (v |::| Size) i
        (* Assume that n = sz + 1*)
        (assume_size_eq n (ISucc sz)
           (* There are two cases depending on whether head can change *)
           (* Cons case1-- x_h : box tye, x_tl: L[sz+1, alph] *)
           begin 
             (* ( (x_h  |:| BTyBox tye) *)
             (*     ( (x_tl |:| BTyList(sz, alph, tye)) (checkBType ePc bty))) *)
             (* >&&> *)
             (* Cons case2-- x_h : tye, x_tl: L[sz+1, beta] where beta+1 = alph *)
             (
               let v' = fresh_ivar Size in
               let beta = IVar v' in
               (* Extend the index ctx with freshly gen. size*)
               ((v' |::| Size) i
                  (* Assume that alph = beta + 1*)
                  (assume_size_eq alph (ISucc beta)
                     ((x_h |:| tye)
                        (( x_tl |:| BTyList(sz, beta, tye))
                           (checkBType ePc bty)))))
             )
           end
        ) 
      
    | _ -> fail i (WrongBShape (bty_g, "list"))
  



and check_case_sum i eP x_l ePl x_r ePr  bty =
  inferBType eP <->=
  (fun bty_g ->
     match bty_g with
     | BTySum (tyl, tyr) -> 
       (x_l |:| tyl) (checkBType ePl bty) >&&>  (x_r |:| tyr) (checkBType ePr bty)
     | _ -> fail i (WrongBShape (bty, "sum"))
  )

and check_pack i eP bty =
  match bty with
  | BTyExists(x, s, ty) ->
    let v = fresh_evar s in
    let witness = IVar v in
    (v |:::| s) i (checkBType eP (bi_ty_subst x witness ty))
  | _ -> fail i (WrongBShape (bty, "existential"))

and check_unpack i eP1 vi_x eP2 bty =
  inferBType eP1 <->=
  (fun bty_x ->
     match push_box bty_x with
     | BTyExists(x, s, ty) ->
       (x |::| s) i
         ((vi_x |:| ty) (checkBType eP2 bty))
     | BTyUnrel(uty1, uty2) -> check_unrel (Unpack(i, fst eP1, vi_x, fst eP2)) (Unpack(i, snd eP1, vi_x, snd eP2)) uty1 uty2
     | _ -> fail i (WrongBShape (bty, "existential")))

and check_clet i vi_x eP1 eP2 bty =
  inferBType eP1 <->=
  (fun csty ->
     match push_box csty with
     | BTyCs(cs, bty_x) ->
         (vi_x |:| bty_x) (checkBType eP2 bty) >>=
	  fun cs_b -> return_ch (CImpl(cs, cs_b))
     | _ -> fail i (WrongBShape (bty, "constrained")))

(* only checks if the expression has any dependencies to changeable
   input, cost restriction is checked later *)
and check_no_change_types (eP: expr * expr) : constr checker =
  fun(ctx, k) ->
    let i = (expInfo (fst eP)) in
    let free_vars = (exp_free_vars (fst eP)) in
    let check_context_stable = List.fold_left
        (fun acc x-> 
           (match (lookup_var x ctx) with
              None -> fail i (Internal ("variable " ^ x ^ " missing type"))
            | Some (v, g_tau) -> 
	      check_bsubtype i g_tau (BTyBox g_tau) >&&> acc)) (return_ch empty_constr) free_vars in
    check_context_stable(ctx, k)

and check_no_change (eP: expr * expr)  (m': constr checker)  : constr checker =
  if is_equal_exp (fst eP) (snd eP) then
    let m = check_no_change_types eP in
    let k' = fresh_evar Cost in 
    let with_no_cost m = fun(ctx, k) -> m (ctx, None) in
    (k' |:::| Cost) (NOCHANGE) (with_no_cost (m >&&> m'))
  else fail (expInfo (fst eP)) (Internal ("expressions are not the same "))


and check_unrel e1 e2 uty1 uty2 =
  fun(ctx, k) ->
    let u1ctx = List.map (fun (v, bty) -> (v, bi_ty_proj true bty)) ctx.var_ctx in
    let u2ctx = List.map (fun (v, bty) -> (v, bi_ty_proj false bty)) ctx.var_ctx in
    let lctx = (set_ctx u1ctx MaxEx ctx) in
    let rctx = (set_ctx u2ctx MinEx ctx) in
    let v' = fresh_evar Cost in
    let k' = IVar v' in
    let kl_ctx = Core.Std.Option.value_map ~default:lctx ~f:(fun _ -> extend_e_var v'.v_name Cost lctx) k in
    let kr_ctx = Core.Std.Option.value_map ~default:rctx ~f:(fun _ -> extend_e_var v'.v_name Cost rctx) k in
    let k1 = Core.Std.Option.map ~f:(fun k -> IAdd(k, k')) k in
    let k2 = Core.Std.Option.map ~f:(fun _ -> k') k in
    begin
      match Unary.checkUType e1 uty1 (kl_ctx, k1) with
      | Right c1 ->
         begin
           match Unary.checkUType e2 uty2 (kr_ctx, k2) with
           | Right c2 -> Right (CExists(v', (expInfo e1),  Cost, merge_cs c1 c2))
           | Left err -> Left err
         end
      | Left err -> Left err
    end
       
and infer_and_check (i: info) (eP: expr * expr) (bty : ty) : constr checker =
  fun(ctx, k) ->
    match inferBType eP ctx with
    | Right (inf_bty, c, psi_ctx, k') ->
       begin
         match (check_bsubtype i inf_bty bty (extend_e_ctx psi_ctx ctx, None)) with
         | Right c' ->
            let cs = option_combine k' k (cost_cs ctx) |> Core.Std.Option.value ~default:CTrue in
          Right (quantify_all_exist psi_ctx (merge_cs (merge_cs c c') cs))
       | Left err -> Left err
       end
    | Left err' -> Left err'



let check_type ctx prgm1 prgm2 bty k =
  match checkBType (prgm1, prgm2) bty (ctx, k) with
  | Right c -> c
  | Left err -> typing_error_pp  err.i pp_tyerr err.v
 
