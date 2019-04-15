module WC = WhyCore
module WT = WhyTrans

open Why3
open Support.Error
open Support.Options

open Why3.Ty
open Why3.Term
open WT 
module CP = Call_provers

exception Why3_error of string

let why_error   fi   = raise( Why3_error fi)

let dp = Support.FileInfo.dummyinfo

 let why_debug  fi = message 3 SMT fi


let ps_plus =
  let v = ty_var (create_tvsymbol (Ident.id_fresh "a")) in
  Term.create_psymbol (Ident.id_fresh "infix +") [v; v]

let real_theory : Why3.Theory.theory = Why3.Env.read_theory WhyCore.env ["real"] "Real"

let get_why3_sym th name =
  try Why3.Theory.ns_find_ls th.Why3.Theory.th_export [name]
  with Not_found -> why_error "Primitive %s cannot be mapped to Why3" name

let why3_rplus  = get_why3_sym real_theory "infix +"

let why3_rsub  = get_why3_sym real_theory "infix -"


let rec fmla_rewrite_subst f =
  match f.t_node with
    | Tapp (ls,[{t_node=Tvar vs} as tv;t]) when ls_equal ls ps_equ ->
      begin
      match t.t_node with
      | Tapp (ls', [t';{t_node=Tvar vs'} as tv']) when ls_equal ls'  why3_rplus -> print_string "HERE HERE\n\n";
        t_app_infer ps_equ  [tv'; (t_app_infer why3_rsub [ tv; t'])]
      | _ -> f end
      | _ -> TermTF.t_map (fun t -> t) fmla_rewrite_subst f



let simplify_trivial_quantification_in_goal2 =
  Trans.goal (fun pr f -> [Decl.create_prop_decl Pgoal pr (Simplify_formula.fmla_remove_quant
  (fmla_rewrite_subst f))])

let simplify_trivial_quantification_in_goal =
 Trans.rewriteTF (fun t -> Simplify_formula.fmla_simpl t) Simplify_formula.fmla_remove_quant None


let alt_ergo : Whyconf.config_prover =
  let fp = Whyconf.parse_filter_prover "Alt-Ergo"   in
  (** all provers that have the name "Alt-Ergo" *)
  let provers = Whyconf.filter_provers WC.config fp in
  if Whyconf.Mprover.is_empty provers then begin
    Format.eprintf "Prover Alt-Ergo not installed or not configured@.";
    exit 0
  end else
    snd (Whyconf.Mprover.max_binding provers)

        
(* loading the Alt-Ergo driver *)
let alt_ergo_driver : Driver.driver =
  try
    Driver.load_driver WC.env alt_ergo.Whyconf.driver []
  with e ->
    Format.eprintf "Failed to load driver for alt-ergo: %a@."
      Exn_printer.exn_printer e;
    exit 1

let splitGoals = ref false

let timelimit = ref 15


let prove_alt_ergo task showDebug =
  let result : Call_provers.prover_result =
    Call_provers.wait_on_call
      (Driver.prove_task ~command:alt_ergo.Whyconf.command ~limit:{Call_provers.empty_limit with limit_time = Some (!timelimit)} alt_ergo_driver task ()) ()                                   in
  (if showDebug then why_debug dp "@[Alt-Ergo answers %a@]@." Call_provers.print_prover_result result);
  match result.CP.pr_answer with
  | CP.Valid   -> true
  | CP.Invalid -> false
  | CP.Unknown (s, _) -> why_debug dp "UNKNOWN %s"  s ; false
  | _          -> false




let post cs i =

  let task    = None                                                   in
  let goal_id = Decl.create_prsymbol (Ident.id_fresh "ty_goal")        in
  let task    = Task.use_export task real_theory                    in
  let task    = Task.use_export task birel_theory                  in
  let task    = Task.add_prop_decl task Decl.Pgoal goal_id cs          in

  let simpl   = simplify_trivial_quantification_in_goal  in
  let task    = Trans.apply simpl task in
 let res = prove_alt_ergo task true in
  if !splitGoals then 
    
    if not (res) then
      let trans_task =  Trans.apply_transform "split_goal_wp" WC.env task in
      why_debug dp "First %i  attempt failed, next will try splitting the goal and proving subgoals: \n" i;
      why_debug dp  "calling solver on subgoals....";
      List.fold_left (fun acc t -> let res = prove_alt_ergo t true in
        	       if not res then
                  let t' = Trans.apply simpl t in
                  let term = (Task.task_goal_fmla t') in
       	          let sub_res =
                    (prove_alt_ergo t' true) in sub_res
        	else
           res && acc) true trans_task
    else true
  else res
let send_smt cs =
  let t = Unix.gettimeofday () in

  let why3_cs = why3_translate cs              in

  why_debug dp  "!*! Why3 term: @[%a@]"  Why3.Pretty.print_term why3_cs;
  why_debug dp "!*! -----------------------------------------------";
  
   let res =  post why3_cs 1 in
   why_debug dp "Execution time of constraint solving & manipulation: %fs\n" (Unix.gettimeofday () -. t); res
