(* ---------------------------------------------------------------------- *)
(* Meta level error handling                                              *)
(* ---------------------------------------------------------------------- *)

module Options = struct

  (* Components of BiRelCost's compiler *)
  type component =
  | General
  | Lexer
  | Parser
  | TypeChecker
  | SMT

  type execMode = DiffMode | UnaryMode

  let default_components =
    [Lexer; Parser; TypeChecker; SMT]

  let components = ref default_components

  let comp_enabled comp =
    List.mem comp !components

  let comp_disable comp =
    let (_, l) = List.partition (fun c -> c = comp) !components in
    components := l

  (* Pretty printing options *)
  type pr_vars =
      PrVarName
    | PrVarIndex
    | PrVarBoth

  type debug_options = {
    components   : component list;
    level        : int;      (* Printing level *)
    unicode      : bool;     (* Use unicode output  *)
    pr_level     : int;      (* Default printing depth *)
    iter_no      : int;      (* Default number of iterations for SMT *)
    full_context : bool;     (* Only names in ctx   *)
    exec_mode    : execMode; (* Execution mode *)
    no_ch_mode   : bool;     (* No change mode *)
    types_mode   : bool;     (* No change mode *)
  }

  let debug_default = {
    components   = [General;Lexer;Parser;TypeChecker;SMT];
    level        = 2;
    unicode      = true;
    pr_level     = 8;
    iter_no      = 1;
    full_context = true;
    exec_mode    = DiffMode;
    no_ch_mode   = false;
    types_mode   = false;
  }

  let debug_options = ref debug_default;
end

module FileInfo = struct

  type info = FI of string * int * int | UNKNOWN | SUBTYPING | EXISTQ | NOCHANGE
  type 'a withinfo = {i: info; v: 'a}

  let dummyinfo = UNKNOWN
  let createInfo f l c = FI(f, l, c)

  let pp_fileinfo ppf = function
    | FI(f,l,c) -> let f_l = String.length f   in
                   let f_t = min f_l 20        in
                   let f_s = max 0 (f_l - f_t) in
                   let short_file = String.sub f f_s f_t in
                   Format.fprintf ppf "(-----%s:%02d.%02d)" short_file l c
    | UNKNOWN   -> Format.fprintf ppf ""
    | SUBTYPING   -> Format.fprintf ppf "subtype"
    | EXISTQ   -> Format.fprintf ppf "EX."
    | NOCHANGE   -> Format.fprintf ppf "NOCHANGE"


end

module Error = struct

  open Options

  exception Exit of int

  (* Printing levels:
        0  Error
        1  warning
        2  Info
        3+ Debug.

     Debug levels:

     3: Print rules executed and return types.
     4: Print rules executed, return types, constraint store and context.
     5: Print everything, including detailed stuff about type eq and unification, context merging, etc...
     6: Print everything, including optimizations.
  *)

  let comp_to_string = function
    | General     -> "[General]"
    | Lexer       -> "[Lexer  ]"
    | Parser      -> "[Parser ]"
    | TypeChecker -> "[TyCheck]"
    | SMT         -> "[SMT    ]"

  let level_to_string = function 
    | 0 -> "Error  "
    | 1 -> "Warning"
    | 2 -> "Info   "
    | 3 -> "Debug 1"
    | 4 -> "Debug 2"
    | _ -> ""

  let level_to_string = function
    | 0 -> "E "
    | 1 -> "W "
    | 2 -> "I "
    | 3 -> "D1"
    | 4 -> "D2"
    | _ -> ""

  (* Default print function *)
  let message level component fi =
    if level <= !debug_options.level &&
      List.mem component !debug_options.components then
      begin
	Format.eprintf "@[%s %s %a: @[" (level_to_string level) (comp_to_string component) FileInfo.pp_fileinfo fi;
	Format.kfprintf (fun ppf -> Format.fprintf ppf "@]@]@.") Format.err_formatter
      end
    else
      Format.ifprintf Format.err_formatter

(* XXX: Note the caveat that the eprintf here will be executed *)
  let error_msg comp fi =
    let cont _ =
      Format.eprintf "@]@.";
      raise (Exit 1)                in
    Format.eprintf "@[%s %s %a: " (level_to_string 0) (comp_to_string comp) FileInfo.pp_fileinfo fi;
    Format.kfprintf cont Format.err_formatter

  let error_msg_pp comp fi pp v =
    Format.eprintf "@[%s %s %a: %a@." (level_to_string 0) (comp_to_string comp)
      FileInfo.pp_fileinfo fi pp v;
    raise (Exit 1)
 
end
