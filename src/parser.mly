%{
open Syntax
open IndexSyntax
open Constr
open Support.FileInfo

let parser_error   fi = Support.Error.error_msg   Support.Options.Parser fi
let parser_warning fi = Support.Error.message   1 Support.Options.Parser fi
let parser_info    fi = Support.Error.message   2 Support.Options.Parser fi

let dummy_ty  = UTyPrim UPrimUnit

let rec int_to_speano n = if n = 0 then IZero else ISucc (int_to_speano (n-1))

(* look for a variable in the context *)
let existing_var fi id ctx =
  match Ctx.lookup_var id ctx with
      None            -> parser_error fi "Identifier %s is unbound" id
    | Some (var, _) -> var

(* look for an index variable in the context *)
let existing_ivar fi id ctx =
  match Ctx.lookup_ivar id ctx with
      None            -> parser_error fi "Index variable %s is unbound" id
    | Some (var, s)  -> (var, s)

(* look for an existential variable in the context *)
let existing_evar fi id ctx =
  match Ctx.lookup_evar id ctx with
      None            -> parser_error fi "Index variable %s is unbound" id
    | Some (var, s)  -> (var, s)

let extend_var id ctx =
  Ctx.extend_var id dummy_ty ctx

let extend_i_var id s ctx =
  Ctx.extend_i_var id s ctx

(* Create a new binder *)
(* TODO: set the proper b_size !!! *)
let nb_prim  n = {v_name = n; v_type = BiVar}
let nb_var   n = {v_name = n; v_type = BiVar}
let nb_ivar n = {v_name = n; v_type = BiIVar}

(* From a list of arguments to a universally quantified unary type *)
let rec qf_to_forall_utype qf u_ty = match qf with
    []               -> u_ty
  | (_, n, mu, t, s) :: qfl -> UTyForall(nb_ivar n, mu, t, s, qf_to_forall_utype qfl u_ty)

(* From a list of arguments to an existentially quantified unary type *)
let rec qf_to_exists_utype qf u_ty = match qf with
    []               -> u_ty
  | (_, n, s) :: qfl -> UTyExists(nb_ivar n, s, qf_to_exists_utype qfl u_ty)
                                        

(* From a list of arguments to a universally quantified binary type *)
let rec qf_to_forall_btype qf bi_ty = match qf with
    []               -> bi_ty
  | (_, n, t, s) :: qfl -> BTyForall(nb_ivar n, t, s, qf_to_forall_btype qfl bi_ty)

(* From a list of arguments to an existentially quantified binary type *)
let rec qf_to_exists_btype qf bi_ty = match qf with
    []               -> bi_ty
  | (_, n, s) :: qfl -> BTyExists(nb_ivar n, s, qf_to_exists_btype qfl bi_ty)
                                        


%}

/* ---------------------------------------------------------------------- */
/* Preliminaries */

/* Keyword tokens */
%token <Support.FileInfo.info> AT
%token <Support.FileInfo.info> ADD
%token <Support.FileInfo.info> AMP
%token <Support.FileInfo.info> AND
%token <Support.FileInfo.info> ARROW
%token <Support.FileInfo.info> LARROW
%token <Support.FileInfo.info> COLON
%token <Support.FileInfo.info> CONS
%token <Support.FileInfo.info> COMMA
%token <Support.FileInfo.info> DASH
%token <Support.FileInfo.info> LBRACE
%token <Support.FileInfo.info> SEMI
%token <Support.FileInfo.info> RBRACE
%token <Support.FileInfo.info> EQUAL
%token <Support.FileInfo.info> HAT
%token <Support.FileInfo.info> DBLARROW
%token <Support.FileInfo.info> SUB
%token <Support.FileInfo.info> MUL
%token <Support.FileInfo.info> TIMES
%token <Support.FileInfo.info> DIV
%token <Support.FileInfo.info> LPAREN
%token <Support.FileInfo.info> RPAREN
%token <Support.FileInfo.info> LEQ
%token <Support.FileInfo.info> LBRACK
%token <Support.FileInfo.info> RBRACK
%token <Support.FileInfo.info> PIPE
%token <Support.FileInfo.info> OR
%token <Support.FileInfo.info> TRUE
%token <Support.FileInfo.info> FALSE
%token <Support.FileInfo.info> INF
%token <Support.FileInfo.info> UNIT
%token <Support.FileInfo.info> UNITR
%token <Support.FileInfo.info> INL
%token <Support.FileInfo.info> INR
%token <Support.FileInfo.info> FUN
%token <Support.FileInfo.info> UNIONCASE
%token <Support.FileInfo.info> LISTCASE
%token <Support.FileInfo.info> OF
%token <Support.FileInfo.info> AS
%token <Support.FileInfo.info> DIFF
%token <Support.FileInfo.info> MAX
%token <Support.FileInfo.info> MIN
%token <Support.FileInfo.info> SND
%token <Support.FileInfo.info> FST
%token <Support.FileInfo.info> NIL
%token <Support.FileInfo.info> MU
%token <Support.FileInfo.info> LET
%token <Support.FileInfo.info> CLET
%token <Support.FileInfo.info> FIX
%token <Support.FileInfo.info> PRIMITIVE
%token <Support.FileInfo.info> BIGLAMBDA
%token <Support.FileInfo.info> LAMBDA
%token <Support.FileInfo.info> IF
%token <Support.FileInfo.info> THEN
%token <Support.FileInfo.info> ELSE
%token <Support.FileInfo.info> PRINT
%token <Support.FileInfo.info> EOF
%token <Support.FileInfo.info> BOOL
%token <Support.FileInfo.info> BOOLR
%token <Support.FileInfo.info> NUM
%token <Support.FileInfo.info> STRING
%token <Support.FileInfo.info> SIZE
%token <Support.FileInfo.info> SENS
%token <Support.FileInfo.info> TYPE
%token <Support.FileInfo.info> PACK
%token <Support.FileInfo.info> WITH
%token <Support.FileInfo.info> IN
%token <Support.FileInfo.info> COST
%token <Support.FileInfo.info> SIZE
%token <Support.FileInfo.info> UNPACK
%token <Support.FileInfo.info> FORALL
%token <Support.FileInfo.info> EXISTS
%token <Support.FileInfo.info> LIST
%token <Support.FileInfo.info> DBLCOLON
%token <Support.FileInfo.info> NAT
%token <Support.FileInfo.info> INT
%token <Support.FileInfo.info> INTR
%token <Support.FileInfo.info> DOT
%token <Support.FileInfo.info> ZERO
%token <Support.FileInfo.info> SUCC
%token <Support.FileInfo.info> UNREL
%token <Support.FileInfo.info> CONTRA
%token <Support.FileInfo.info> FLOOR
%token <Support.FileInfo.info> CEIL
%token <Support.FileInfo.info> LOG
%token <Support.FileInfo.info> MINPOWLIN
%token <Support.FileInfo.info> MINPOWCONSTANT
%token <Support.FileInfo.info> SUM
%token <Support.FileInfo.info> BOX

/* Identifier and constant value tokens */
%token <string Support.FileInfo.withinfo> ID
%token <int    Support.FileInfo.withinfo> INTV
%token <float  Support.FileInfo.withinfo> FLOATV

/* ---------------------------------------------------------------------- */
/* RelCost grammar                                                           */
/* ---------------------------------------------------------------------- */

%start u_toplevel b_toplevel
%type < Syntax.expr * IndexSyntax.iterm * Syntax.un_ty * Syntax.mode > u_toplevel
%type < Syntax.expr *  Syntax.expr * IndexSyntax.iterm * Syntax.bi_ty > b_toplevel
%%

/* ---------------------------------------------------------------------- */
/* Main body of the parser definition                                     */
/* ---------------------------------------------------------------------- */

u_toplevel :
    Term LEQ LBRACK Mode COMMA ITerm RBRACK COLON UType EOF
        { let ctx = Ctx.set_exec_mode $4 (Ctx.empty_context) in
          ($1 ctx, $6 ctx, $9 ctx, $4) }


b_toplevel :
    Term COMMA Term LEQ ITerm COLON BType EOF
        { let ctx = Ctx.empty_context in
          ($1 ctx, $3 ctx, $5 ctx, $7 ctx) }
  | Term LEQ ITerm COLON BType EOF
      { let ctx = Ctx.empty_context in
        ($1 ctx, $1 ctx, $3 ctx, $5 ctx) }


Term :
    LET ID EQUAL Term IN Term
        {
          fun ctx ->
          let ctx' = extend_var $2.v ctx in
          Let($2.i, (nb_var $2.v), $4 ctx, $6 ctx')
        }
        
   | CLET Term AS ID IN Term
        {
          fun ctx ->
          let ctx' = extend_var $4.v ctx in
          CLet($4.i, (nb_var $4.v),  $2 ctx, $6 ctx')
        }
        
    | FIX ID LPAREN ID RPAREN DOT Term
      {
        fun ctx ->
        let ctx_f = extend_var $2.v ctx   in
        let ctx_x = extend_var $4.v ctx_f in
        Fix($2.i, nb_var $2.v, nb_var $4.v, $7 ctx_x)
      }
    | LAMBDA ID DOT Term
      {
        fun ctx ->
        let ctx_x = extend_var $2.v ctx   in
        Fix($2.i, nb_var "_", nb_var $2.v, $4 ctx_x)
      }

    | BIGLAMBDA DOT Term
      {
        fun ctx -> let e = $3 ctx in ILam(expInfo e, e)
      }
    |  IF Expr THEN Term ELSE Term 
      { fun ctx -> IfThen($1, $2 ctx, $4 ctx, $6 ctx)
      }

    | PACK Term
      { fun ctx -> Pack ($1, $2 ctx) }

    | UNPACK Term AS ID IN Term
      { fun ctx ->
        let ctx' = extend_var $4.v ctx in
        Unpack($1,$2 ctx, nb_var $4.v, $6 ctx')
      }
    | UNIONCASE Expr OF INL LPAREN ID RPAREN DBLARROW Term PIPE INR LPAREN ID RPAREN DBLARROW Term 
      { fun ctx ->
        let ctx_l = extend_var $6.v  ctx in
        let ctx_r = extend_var $13.v ctx in
        Case($1, $2 ctx, nb_var $6.v, $9 ctx_l, nb_var $13.v, $16 ctx_r) }

    | LISTCASE Expr OF NIL DBLARROW Term PIPE ID DBLCOLON ID DBLARROW Term 
      { fun ctx ->
        let ctx_h  = extend_var $8.v ctx in
        let ctx_tl = extend_var $10.v ctx_h in
        CaseL($1, $2 ctx, $6 ctx, nb_var $8.v, nb_var $10.v, $12 ctx_tl) }

    | LBRACE Term COLON UType COMMA ITerm RBRACE { fun ctx -> UAnno($1, $2 ctx, $4 ctx, $6 ctx)}
    | LBRACE Term COLON BType COMMA ITerm RBRACE { fun ctx -> BAnno($1, $2 ctx, $4 ctx, $6 ctx)}
    | App  { $1 }
        

/* Applications */
App:
   App Expr
  { fun ctx ->
      let e1 = $1 ctx in
      let e2 = $2 ctx in
      App (expInfo e1 , e1, e2) 
  }
  |  Expr 
     { $1 }
  | App LBRACK RBRACK { fun ctx -> let e = $1 ctx in IApp(expInfo e, e) } 
  

/* Syntactic sugar for n-ary tuples */
PairSeq:
    Term COMMA Term 
      { fun ctx -> Pair($2, $1 ctx, $3 ctx) }
  | Term COMMA PairSeq 
      { fun ctx -> Pair($2, $1 ctx, $3 ctx)  }


Expr:
    TRUE
     { fun _cx -> Prim ($1, PrimTBool true) }
  | FALSE
     { fun _cx -> Prim ($1, PrimTBool false) }
  | INTV
     { fun _cx -> Prim($1.i, PrimTInt $1.v) }
  | NIL
     { fun _cx -> Nil($1) }
  | CONTRA 
    { fun _cx -> Contra($1) }
  | LPAREN RPAREN
     { fun _cx -> Prim ($1, PrimTUnit) }
  | ID
     { fun ctx -> Var($1.i, existing_var $1.i $1.v ctx) }
  | LPAREN Term RPAREN
     { $2 }
  | FST Term
     { fun ctx -> Fst ($1, $2 ctx) }
  | SND Term   
     { fun ctx -> Snd ($1, $2 ctx) }    
  | INL Expr
     { fun ctx -> Inl($1, $2 ctx)  }
  | INR Expr
     { fun ctx -> Inr ($1, $2 ctx) }
  | LPAREN PairSeq RPAREN 
     { $2 }
  | Term DBLCOLON Term
     { fun ctx -> Cons($2, $1 ctx, $3 ctx) }
 
/* Sorts */
Sort :
    SIZE
      { Size }
  | COST
      { Cost }

Mode:
   MAX
    { MaxEx }
  | MIN
    { MinEx }


  /* Unary Types */
UType:
    UAType LBRACK Mode COMMA ITerm RBRACK ARROW UType
    { fun ctx -> UTyArr($1 ctx, $3, $5 ctx, $8 ctx) }
  | UAType ARROW UType
    { fun ctx -> UTyArr($1 ctx, MaxEx, IZero, $3 ctx) }
  | LIST LBRACK ITerm RBRACK UType
    { fun ctx -> UTyList($3 ctx, $5 ctx) }

  | UType ADD UType
    { fun ctx -> UTySum($1 ctx, $3 ctx) }

  | Constr AND UType
    { fun ctx -> UTyCs($1 ctx, $3 ctx) }

  | QuantifiedUTypes
    { $1 }

  | ConstrainedUTypes
    { $1 }

  | UAType
    { $1 }

UAType:
    LPAREN UType RPAREN
    { $2 }
  | BOOL
    { fun _cx -> UTyPrim UPrimBool }
  | INT
    { fun _cx ->  UTyPrim UPrimInt }
  | UNIT
    { fun _cx ->  UTyPrim UPrimUnit }
  | UTPairSeq
    { fun ctx -> $1 ctx }

UTPairSeq:
    UType TIMES UType
    { fun ctx -> UTyProd($1 ctx, $3 ctx) }
  | UType TIMES UTPairSeq
    { fun ctx -> UTyProd($1 ctx, $3 ctx) }

FSortUAnn :
    ID LBRACK Mode COMMA ITerm RBRACK DBLCOLON Sort
      { fun ctx -> ([($1.i, $1.v, $8, $3, $5 ctx)], extend_i_var $1.v $8 ctx) }

ESortUAnn :
    ID DBLCOLON Sort
      { fun ctx -> ([($1.i, $1.v, $3)], extend_i_var $1.v $3 ctx) }
     
FQuantifierUList :
    FSortUAnn
      { $1 }
  | FSortUAnn SEMI FQuantifierUList
      { fun ctx -> let (iv, ctx')  = $1 ctx  in
                   let (qf, ctx_qf) = $3 ctx' in
                   (iv @ qf, ctx_qf)
      }

EQuantifierUList :
    ESortUAnn
      { $1 }
  | ESortUAnn SEMI EQuantifierUList
      { fun ctx -> let (iv, ctx')  = $1 ctx  in
                   let (qf, ctx_qf) = $3 ctx' in
                   (iv @ qf, ctx_qf)
      }

QuantifiedUTypes :
   FORALL FQuantifierUList DOT UType
          { fun ctx -> let (qf, ctx') =  $2 ctx in
                        qf_to_forall_utype qf ($4 ctx')  }
  | EXISTS EQuantifierUList DOT UType
    { fun ctx ->  let (qf, ctx') =  $2 ctx in qf_to_exists_utype qf ($4 ctx') }


ConstrainedUTypes :
    LBRACE Constr RBRACE UType
    { fun ctx -> UTyCs ($2 ctx, $4 ctx) }      


 /* Binary Types */
BType:
    BAType LBRACK DIFF COMMA ITerm RBRACK ARROW BType
    { fun ctx -> BTyArr($1 ctx, $5 ctx, $8 ctx) }
  |  BAType DBLARROW BType
    { fun ctx -> BTyArr($1 ctx, IZero, $3 ctx) }
  | LIST LBRACK ITerm COMMA ITerm RBRACK BType
    { fun ctx -> BTyList($3 ctx, $5 ctx, $7 ctx) }
  | QuantifiedBTypes
    { $1 }
  | UnrelatedTypes
    { $1 }
  | ConstrainedBTypes
    { $1 }
  | BOX BType
    { fun ctx -> BTyBox ($2 ctx) }
  | BAType
    { $1 }

BAType:
    LPAREN BType RPAREN
    { $2 }
  | BOOLR
    { fun _cx -> BTyPrim BPrimBool }
  | INTR
    { fun _cx ->  BTyPrim BPrimInt }
  | UNITR
    { fun _cx ->  BTyPrim BPrimUnit }
  | BTPairSeq
    { fun ctx -> $1 ctx }

BTPairSeq:
    BType TIMES BType
    { fun ctx -> BTyProd($1 ctx, $3 ctx) }
  | BType TIMES BTPairSeq
    { fun ctx -> BTyProd($1 ctx, $3 ctx) }

FSortBAnn :
     ID LBRACK DIFF COMMA ITerm RBRACK DBLCOLON Sort
      { fun ctx -> ([($1.i, $1.v, $8, $5 ctx)], extend_i_var $1.v $8 ctx) }
   | ID 
      { fun ctx -> ([($1.i, $1.v, Size, IZero)], extend_i_var $1.v Size ctx) }

ESortBAnn :
    ID DBLCOLON Sort
      { fun ctx -> ([($1.i, $1.v, $3)], extend_i_var $1.v $3 ctx) }
     
FQuantifierBList :
    FSortBAnn
      { $1 }
  | FSortBAnn SEMI FQuantifierBList
      { fun ctx -> let (iv, ctx')  = $1 ctx  in
                   let (qf, ctx_qf) = $3 ctx' in
                   (iv @ qf, ctx_qf)
      }

EQuantifierBList :
    ESortBAnn
      { $1 }
  | ESortBAnn SEMI EQuantifierBList
      { fun ctx -> let (iv, ctx')  = $1 ctx  in
                   let (qf, ctx_qf) = $3 ctx' in
                   (iv @ qf, ctx_qf)
      }

QuantifiedBTypes :
   FORALL FQuantifierBList DOT BType
          { fun ctx -> let (qf, ctx') =  $2 ctx in
                        qf_to_forall_btype qf ($4 ctx')  }
  | EXISTS EQuantifierBList DOT BType
    { fun ctx ->  let (qf, ctx') =  $2 ctx in qf_to_exists_btype qf ($4 ctx') }

UnrelatedTypes :
   UNREL LPAREN UType COMMA UType RPAREN 
    { fun ctx -> BTyUnrel ($3 ctx, $5 ctx) }
  | UNREL UType
    { fun ctx -> BTyUnrel ($2 ctx, $2 ctx) }

ConstrainedBTypes :
    LBRACE Constr RBRACE BType
    { fun ctx -> BTyCs ($2 ctx, $4 ctx) }      


/* Index terms */
 ITerm:
   ITerm ADD ITerm
    { fun ctx -> IAdd($1 ctx, $3 ctx) }
  | ITerm MUL ITerm
    { fun ctx -> IMult($1 ctx, $3 ctx) }
  | ITerm DIV ITerm
    { fun ctx -> IDiv($1 ctx, $3 ctx) }
  | ITerm SUB ITerm
    { fun ctx -> IMinus($1 ctx, $3 ctx) }
  | MIN LPAREN ITerm COMMA ITerm RPAREN
    { fun ctx -> IMin($3 ctx, $5 ctx) }
  | INF
    { fun ctx -> IInfty }
  | LOG LPAREN ITerm RPAREN    	
    { fun ctx -> ILog($3 ctx) }
  | ITerm HAT ITerm     	
    { fun ctx -> IPow($1 ctx, $3 ctx) }
  | MINPOWLIN LPAREN ITerm COMMA ITerm RPAREN    	
    { fun ctx -> IMinPowLin($3 ctx, $5 ctx) }
  | MINPOWCONSTANT LPAREN ITerm COMMA ITerm RPAREN    	
    { fun ctx -> IMinPowCon($3 ctx, $5 ctx) }
  | SUM LPAREN ITerm COMMA LBRACE
    ITerm COMMA ITerm RBRACE RPAREN 	
    { fun ctx -> ISum($3 ctx, $6 ctx, $8 ctx)}
  | ZERO
    { fun _cx ->
      IZero
    }
  | SUCC ITerm
    { fun ctx ->
      ISucc ($2 ctx)
    }

  | FLOOR LPAREN ITerm RPAREN
    { fun ctx ->
      IFloor ($3 ctx)
    }

  | CEIL LPAREN ITerm RPAREN
    { fun ctx ->
      ICeil ($3 ctx)
    }
  | LPAREN ITerm RPAREN
    { fun ctx -> $2 ctx }
  | ID
    { fun ctx -> let (v, k) = existing_ivar $1.i $1.v ctx in
                  IVar v
    }
  | INTV
      { fun _cx ->
        (int_to_speano $1.v)
      }
  | FLOATV
      { fun _cx -> IConst $1.v }


/* Constraints */
Constr:
  | ITerm EQUAL ITerm       { fun ctx ->CEq($1 ctx,$3 ctx) }
  | ITerm LEQ ITerm         { fun ctx -> CLeq($1 ctx,$3 ctx) }
  | Constr AND Constr       { fun ctx -> CAnd($1 ctx,$3 ctx) }
  | LPAREN Constr RPAREN    { fun ctx -> $2 ctx }
