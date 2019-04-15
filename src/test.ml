open OUnit2
module T = Tycheck_sigs
module E = Exist_elim

exception Success

  let parse_exec file =
  let fh = open_in file in
  let lexbuf = (Lexing.from_channel fh) in
  let (program,cost, unary_ty, mu) as triple =
      try Parser.u_toplevel Lexer.main lexbuf
      with Parsing.Parse_error -> Support.Error.error_msg Support.Options.Parser (Lexer.info lexbuf) "Parse error" in
    Parsing.clear_parser();
    close_in fh;
    triple

      
let parse_diff file =
  let fh = open_in file in
  let lexbuf = (Lexing.from_channel fh) in
  let (program1, program2, cost, binary_ty) as quad =
    try Parser.b_toplevel Lexer.main lexbuf
    with Parsing.Parse_error -> Support.Error.error_msg Support.Options.Parser (Lexer.info lexbuf) "Parse error" in
   Parsing.clear_parser();
   close_in fh;
   quad
       
let run_unary_test infile =
  let (prgm, cost, uty, mu) = parse_exec infile in 
    let ctx = Ctx.set_exec_mode mu (Ctx.empty_context) in
    let cs =  (Unary.check_type ctx prgm uty (Some cost)) in
    E.elim ctx (cs)
              (fun cs' -> 
                let elim_cs = Constr.constr_simpl cs' in 
                if ((WhySolver.send_smt) elim_cs) then raise Success else ())

let recordResults test totalT typeChT  existT  csT =
  let oc = open_out_gen [Open_creat; Open_text; Open_append] 0o640 "results.txt" in
  let fmt = format_of_string "%s & %0.2f & %0.2f & %0.2f & %0.2f \\\\ \\hline \n" in
  let r = Str.regexp "examples/binary/\\(.*\\).br" in
  let name =   Str.replace_first r "\kw{\\1}" test in 
  output_string oc (Printf.sprintf fmt ("$" ^name ^ "$") (totalT) typeChT  existT  csT );
  close_out oc

            
let run_binary_test infile heur =
    let t= Unix.gettimeofday ()  in
   let (prgm1, prgm2, cost, bty) = parse_diff infile in
   let ctx = Ctx.set_heur_mode heur (Ctx.empty_context) in
   let cost = Some cost in
   let cs  =  (Binary.check_type ctx prgm1 prgm2 bty cost) in
   let typeChT = (Unix.gettimeofday () -. t) in
   let tcons= Unix.gettimeofday ()  in
   let existT = ref 0.0 in
    E.elim ctx (cs)
         (fun cs' ->
           let elim_cs = Constr.constr_simpl cs' in
           let t'' = Unix.gettimeofday () in
           existT := (t'' -. tcons);
           if ((WhySolver.send_smt) elim_cs) then (recordResults infile (Unix.gettimeofday () -. t) typeChT !existT  (Unix.gettimeofday () -. t'')
; raise Success) else ())




let u_pre s = (fun _ -> run_unary_test ("examples/unary/" ^ s)) 
let b_pre s = (fun _ -> run_binary_test ("examples/binary/" ^ s) Ctx.Usual) 
let b_pre_NC s = (fun _ -> run_binary_test ("examples/binary/" ^ s) Ctx.NoChange) 


  
let utest_app utest_ctxt = assert_raises Success (u_pre "app.br");;
let utest_map utest_ctxt = assert_raises Success (u_pre "map.br");;
let utest_rev utest_ctxt = assert_raises Success (u_pre "rev.br");;
let utest_bsplit utest_ctxt = assert_raises Success (u_pre "bsplit-precise.br");;
let utest_bfold utest_ctxt = assert_raises Success (u_pre "bfold-precise.br");;
let utest_merge utest_ctxt = assert_raises Success (u_pre "merge.br");;
let utest_mergeMin utest_ctxt = assert_raises Success  (u_pre "merge-min.br");;
let utest_msort utest_ctxt = assert_raises Success  (u_pre "msort-precise.br");;


let btest_append btest_ctxt = assert_raises Success  (b_pre "append.br");;
let btest_map btest_ctxt = assert_raises Success  (b_pre "map.br");;
let btest_filter btest_ctxt = assert_raises Success  (b_pre "filter.br");;
let btest_map_box_unrel btest_ctxt = assert_raises Success  (b_pre "map-unrel-func.br");;
let btest_rev btest_ctxt = assert_raises Success  (b_pre "rev.br");;
let btest_id btest_ctxt = assert_raises Success  (b_pre "id.br");;
let btest_comp btest_ctxt = assert_raises Success  (b_pre "constant-comp.br");;
let btest_sam btest_ctxt = assert_raises Success  (b_pre "sam.br");;
let btest_merge btest_ctxt = assert_raises Success  (b_pre "merge.br");;
let btest_bsplit btest_ctxt = assert_raises Success  (b_pre "bsplit.br");;
let btest_bfold btest_ctxt = assert_raises Success  (b_pre_NC "bfold.br");;
let btest_msort btest_ctxt = assert_raises Success  (b_pre_NC "msort.br");;
let btest_find btest_ctxt = assert_raises Success  (b_pre "find.br");;
let btest_2Dcount btest_ctxt = assert_raises Success  (b_pre "2Dcount.br");;
let btest_ssort utest_ctxt = assert_raises Success  (b_pre "ssort.br");;
let btest_appsum utest_ctxt = assert_raises Success  (b_pre "appSum.br");;
let btest_zip utest_ctxt = assert_raises Success  (b_pre "zip.br");;
let btest_flatten utest_ctxt = assert_raises Success  (b_pre "flatten.br");;

  
(* Tests for maximum execution mode *)
let max_suite =
"suite">:::
 ["test app">:: utest_app;
  "test map">:: utest_map;
  "test reverse">:: utest_rev;
  "test bsplit">:: utest_bsplit;
  (* "test balalnced fold">:: utest_bfold; *)
  "test merge">:: utest_merge;
  (* "test mergesort">:: utest_msort; *)
 ]
;;

(* Tests for minimum execution mode *)
let min_suite =
"suite">:::
 ["test merge [min]">:: utest_mergeMin;
 ]
;;

(* Tests for diff execution mode *)
let diff_suite =
"suite">:::
 ["test apppend">:: btest_append;
  "test map">:: btest_map;
  "test filter">:: btest_filter;
  "test reverse">:: btest_rev;
  "test constant time comparison">:: btest_comp;
  "test square-and-multiply">:: btest_sam;
  "test bsplit">:: btest_bsplit;
  "test find">:: btest_find;
  "test 2Dcount">:: btest_2Dcount;
  "test selection sort">:: btest_ssort;
  "test merge">:: btest_merge;
  "test appsum">:: btest_appsum;
  "test flatten">:: btest_flatten;
  "test zip">:: btest_zip;
  "test bfold">:: btest_bfold;
  "test mergesort">:: btest_msort;
 ]
;;


let () =
  run_test_tt_main max_suite;
  run_test_tt_main min_suite;
  run_test_tt_main diff_suite;
;;
