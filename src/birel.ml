open Unix
open Support.Options
open Constr 
open IndexSyntax

module T = Tycheck_sigs
module WS = WhySolver
module E = Exist_elim
module SE = Support.Error


(* Default arguments *)
let outfile  = ref (None : string option)
let infile   = ref ("" : string)
       

(* Exceptions for constraint solving *)
exception Success
exception Timeout
     
let argDefs = [
    "-o", Arg.String (fun s -> outfile := Some s),
         "File to write the generated code to" ;
    "-v", Arg.Int (fun l  -> debug_options := {!debug_options with level = l} ),
         "Set printing level to n (1 Warning [2 Info], 3+ Debug)" ;
    "-u", Arg.Unit (fun () -> debug_options := {!debug_options with exec_mode = UnaryMode}),
         "Typecheck in unary execution mode (by default DiffMode)";
    "-t", Arg.Int (fun l  -> WhySolver.timelimit := l ),
         "Set timelimit for constraint solving to n (by defalt 15 s)" ;
    "-i", Arg.Int (fun l  -> debug_options := {!debug_options with iter_no = l} ),
         "Set number of iterations for existential elimination (default 1)" ;
    "--nochange", Arg.Unit (fun l  -> debug_options := {!debug_options with no_ch_mode = true}),
         "Typecheck using no change heuristic (not set by default)";
    "--disable-cost", Arg.Unit (fun l  -> debug_options := {!debug_options with types_mode = true}),
         "Typecheck only the types without costs (not set by default)";
    "--split-goal", Arg.Set WS.splitGoals,
         "Optimization: split constraint into sub goals (not set by default)";
]


let dp = Support.FileInfo.dummyinfo

let main_error = SE.error_msg General

let smt_error = SE.error_msg SMT

let main_warning fi = SE.message 1 General fi
let main_info    fi = SE.message 2 General fi
let main_debug   fi = SE.message 3 General fi


let parseArgs () =
  let inFile = ref (None : string option) in
  Arg.parse argDefs
     (fun s ->
       match !inFile with
         Some(_) -> main_error dp "Please specify exactly one input file"
       | None -> inFile := Some(s))
     "Usage: birel [options] inputfile";
  match !inFile with
      None    -> main_error dp "No input file specified (use --help to display usage info)"; ""
    | Some(s) -> s


(* Parse the diff mode input *)
let parse_diff file =
   let fh = open_in file in
   let lexbuf = (Lexing.from_channel fh) in
   let (program1, program2, cost, binary_ty) as quad =
     try Parser.b_toplevel Lexer.main lexbuf
     with Parsing.Parse_error -> SE.error_msg Parser (Lexer.info lexbuf) "Parse error" in
   Parsing.clear_parser();
   close_in fh;
   quad
       
(* Parse the unary mode input *)
let parse_exec file =
  let fh = open_in file in
  let lexbuf = (Lexing.from_channel fh) in
  let (program,cost, unary_ty, mu) as quad =
      try Parser.u_toplevel Lexer.main lexbuf
      with Parsing.Parse_error -> SE.error_msg Parser (Lexer.info lexbuf) "Parse error" in
    Parsing.clear_parser();
    close_in fh;
    quad
  

let type_check_un infile  t= 
let (prgm, cost, uty, mu) = parse_exec !infile in
    (* Print the results of the parsing phase *)
    main_debug dp "Parsed program:@\n@[%a@]@.\nParsed type:@\n@[%a@]@." 
	       Print.pp_expr prgm Print.pp_utype uty;
    let ctx = Ctx.set_exec_mode mu (Ctx.empty_context) in
    let cost = if (!debug_options.types_mode) then None else Some cost in
    let cs =  (Unary.check_type ctx prgm uty cost) in
    
    main_debug dp "Typechecking engine: %fs\n" (Unix.gettimeofday () -. t);
    main_debug dp "Resulting constraint:@\n@[%a@]@." Print.pp_cs cs;
    
    let tcons= Unix.gettimeofday ()  in
   try 
     E.elim ctx (Constr.constr_simpl cs)
	    (fun cs' ->
             let elim_cs = Constr.constr_simpl cs' in
             main_debug dp "Existential elimination time: %fs\n" (Unix.gettimeofday () -. tcons);
	     main_debug dp "Eliminated constraint:@\n@[%a@]@." Print.pp_cs elim_cs;
             if ((WS.send_smt) elim_cs) then 
	       (main_debug dp "Total execution time: %fs\n" (Unix.gettimeofday () -. t);
		raise Success) else ())
   with
     Success -> main_info dp "Successfully typechecked!\n"


let type_check_diff infile t = 
   let (prgm1, prgm2, cost, bty) = parse_diff !infile in
    (* Print the results of the parsing phase *)
    main_debug dp "Parsed programs:@\n@[%a@]@ @\n@\n@[%a@]@." 
	       Print.pp_expr prgm1 Print.pp_expr prgm2;
    let heur = if (!debug_options.no_ch_mode) then Ctx.NoChange else Ctx.Usual in
    let ctx =  Ctx.set_heur_mode heur (Ctx.empty_context) in
    let cost = if (!debug_options.types_mode) then None else Some cost in
    let cs  =  (Binary.check_type ctx prgm1 prgm2 bty cost) in

    main_debug dp "Typechecking engine: %fs\n" (Unix.gettimeofday () -. t);
    main_debug dp "Resulting constraint:@\n@[%a@]@." Print.pp_cs cs; 
    let tcons= Unix.gettimeofday ()  in
    try
      E.elim ctx (cs)
        (fun cs' ->
           let elim_cs = Constr.constr_simpl cs' in
           main_debug dp "Existential elimination time: %fs\n" (Unix.gettimeofday () -. tcons);
           main_debug dp "Eliminated constraint:@\n@[%a@]@." Print.pp_cs elim_cs;
           if !debug_options.iter_no > 0
           then
             (debug_options := {!debug_options with iter_no = !debug_options.iter_no -1};
              if WS.send_smt elim_cs
              then 
                (main_debug dp "Total execution time: %fs\n" (Unix.gettimeofday () -. t);
                 raise Success)
              else ())
           else raise Timeout
        )

    with
      Success -> main_info dp "Successfully typechecked!\n"
    | Timeout -> smt_error dp "Existential elim. iteration limit reached and typechecking failed: either increase the timelimit or the iteration count. Otherwise, program doesn't typecheck."




(**----- The main BiRelCost program------ *)
let main =
  let t= Unix.gettimeofday ()  in
  (* Setup the pretty printing engine *)

  let fmt_margin =
    try
      snd (Util.get_terminal_size ())
    with _ ->
      main_warning dp "Failed to get terminal size value.";
      120
  in

  let set_pp fmt =
    Format.pp_set_ellipsis_text fmt "[...]";
    Format.pp_set_margin fmt (fmt_margin + 1); (* Don't ever ask *)
    Format.pp_set_max_indent fmt fmt_margin    in

  set_pp Format.std_formatter;
  set_pp Format.err_formatter;

  (* Read the command-line arguments *)
  infile      := parseArgs();
  match !debug_options.exec_mode with
  | UnaryMode ->   type_check_un infile t
  | DiffMode -> type_check_diff infile t
