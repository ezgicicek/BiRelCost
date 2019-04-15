
(* ---------------------------------------------------------------------- *)
(* Abstract Syntax Tree for index terms                                   *)
(* ---------------------------------------------------------------------- *)


(* Sorts for index variables *)
type sort =
    Size
  | Cost

(* Different types of variable binding, for debugging purposes *)
type birel_binding =
    BiVar           (* Regular varible *)
  | BiIVar          (* Index variable   *)
  | BiEVar of sort  (* Existential variable  *)

type var_info = {
  v_name  : string;
  v_type  : birel_binding;
}


(* Default var_info *)
let dvi = {
  v_name        = "lorem";
  v_type        = BiIVar;
}

(* Default var_info *)
let new_var x = {
  v_name        = x;
  v_type        = BiEVar Size;
}


(* Index terms *)
type iterm =
  | IZero
  | ISucc    	of iterm
  | IInfty
  | IConst   	of float
  | IVar     	of var_info
  | IAdd     	of iterm * iterm
  | IMinus   	of iterm * iterm
  | IMult    	of iterm * iterm
  | IDiv     	of iterm * iterm
  | IPow     	of iterm * iterm
  | IMin     	of iterm * iterm
  | IMinPowLin  of iterm * iterm
  | IMinPowCon  of iterm * iterm
  | ISum    	of iterm * iterm * iterm
  | ILog     	of iterm
  | ICeil    	of iterm
  | IFloor   	of iterm

(* Map over index variables *)
let rec iterm_map f it =
  let smf = iterm_map f     in
  match it with
    IVar v           -> f v
  | IZero            -> IZero
  | ISucc s          -> ISucc (smf s)
  | IConst c         -> IConst c
  | IAdd(x, y)       -> IAdd (smf x, smf y)
  | IMinus(x, y)     -> IMinus (smf x, smf y)
  | IMult(x, y)      -> IMult (smf x, smf y)
  | IDiv(x, y)       -> IDiv (smf x, smf y)
  | IPow(x, y)       -> IPow (smf x, smf y)
  | IMin(x, y)       -> IMin (smf x, smf y)
  | IMinPowLin(x, y) -> IMinPowLin (smf x, smf y)
  | IMinPowCon(x, y) -> IMinPowLin (smf x, smf y)
  | ISum(x, y, z)    -> ISum (smf x, smf y, smf z)
  | ILog s           -> ILog (smf s)
  | ICeil s          -> ICeil (smf s)
  | IFloor s         -> IFloor (smf s)
  | IInfty           -> IInfty
    
(* Substitution it[t/x] for index vars *)
let iterm_subst x t it =
  iterm_map (fun v -> if v = x then t else IVar v) it

let rec iterm_simpl it : iterm = 
  match it with
  | IZero -> IConst 0.0
  | ISucc it' -> let r = iterm_simpl it' in 
    begin
      match r with 
    | IConst c -> IConst (c +. 1.0) 
    |  _ -> ISucc r
    end
  | IAdd(it1, it2) ->
    let r1 = iterm_simpl it1 in
    let r2 = iterm_simpl it2 in
    begin 
      match r1,r2 with
      | IConst c1 , IConst c2 -> IConst (c1+.c2) 
      | IZero, _  
      | IConst 0.0, _  -> r2
      | _, IZero 
      | _, IConst 0.0  -> r1
      | _, _ ->  IAdd(r1, r2)
    end
  | IMinus(it1, it2) ->     
    let r1 = iterm_simpl it1 in
    let r2 = iterm_simpl it2 in
    begin
      match r1,r2 with
      | _, IZero | _, IConst 0.0 -> r1
      | IConst c1 , IConst c2 -> IConst (c1-.c2) 
      | _, _ ->IMinus(r1, r2)
    end
  | IMult(it1, it2) ->
    begin
      let r1 = iterm_simpl it1 in
      let r2 = iterm_simpl it2 in
      match r1,r2 with
      | IConst c1 , IConst c2 -> IConst (c1*.c2) 
      |  _, _ ->IMult(r1, r2)
    end
  | IDiv(it1, it2) ->
    begin
      let r1 = iterm_simpl it1 in
      let r2 = iterm_simpl it2 in
      match r1,r2 with
      | IConst c1 , IConst c2 -> IConst (c1/.c2) 
      |  _, _ ->IDiv(r1, r2)
    end
  | IMin(it1, it2) ->
    begin
      let r1 = iterm_simpl it1 in
      let r2 = iterm_simpl it2 in
      match r1,r2 with
      | IConst c1 , IConst c2 -> IConst (min c1 c2) 
      |  _, _ ->IMin(r1, r2)
    end
  | IPow (it1, it2) ->
    let r1 = iterm_simpl it1 in
    let r2 = iterm_simpl it2 in IPow(r1,r2)
  | IMinPowLin (it1, it2) -> IMinPowLin (iterm_simpl it1, iterm_simpl it2)
  | IMinPowCon (it1, it2) -> IMinPowCon (iterm_simpl it1, iterm_simpl it2)
  | ISum(it1, it2, it3) ->
    let r1 = iterm_simpl it1 in
    let r2 = iterm_simpl it2 in
    let r3 = iterm_simpl it3 in  ISum(r1, r2, r3)
  | ICeil it' -> ICeil (iterm_simpl it')
  | IFloor it' -> IFloor (iterm_simpl it')
  | ILog it' -> ILog (iterm_simpl it')
  | IInfty 
  | IConst _ 
  | IVar _ -> it     

    let rec dedup (l: 'a list) : 'a list =
      match l with
        [] -> []
      | h :: tl -> let r = dedup tl in if List.mem h r then r else h :: r

(* Get free index variables ofan index term *)
let rec iterm_free_i_vars (it: iterm) : var_info list =
  match it with
    IVar v    ->  [v]

  | IZero 
  | IInfty    -> []
  | IConst c  -> []

  | ISucc  s  
  | ILog s 
  | ICeil s  
  | IFloor s  -> dedup (iterm_free_i_vars s)

  | IAdd (x, y) 
  | IMinus  (x, y) 
  | IMult (x, y) 
  | IDiv (x, y) 
  | IPow(x, y) 
  | IMin (x, y)
  | IMinPowLin (x, y)
  | IMinPowCon (x, y) ->
   dedup (iterm_free_i_vars x  @ iterm_free_i_vars y)

  | ISum(x,y,z) -> dedup (iterm_free_i_vars x  @ iterm_free_i_vars y @ iterm_free_i_vars z)
  



  
let add_costs  (sl, sr) : iterm =
match  sl, sr with
| IZero, _ -> iterm_simpl sr
| _, IZero -> iterm_simpl sl
| _ -> IAdd(iterm_simpl sl, iterm_simpl sr)
        

(* A simplifying version of sl+sr that checks if one of sl or sr are 0. *)
let sum_costs  sl sr : iterm option =
match sl, sr with
| Some x, Some y -> Some (add_costs (x, y))
| _, Some y -> Some (iterm_simpl  y)
| Some x, _ -> Some (iterm_simpl  x)
| _ -> None
   
