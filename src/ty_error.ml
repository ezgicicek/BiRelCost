(* ---------------------------------------------------------------------- *)
(* Errors                                                                 *)
(* ---------------------------------------------------------------------- *)

open Syntax
open Format
open Print

(* Errors *)
type ty_error_elem =
| UTypeMismatch of un_ty * un_ty
| BTypeMismatch of bi_ty * bi_ty
| NotUSubtype   of un_ty * un_ty
| NotBSubtype   of bi_ty * bi_ty
| WrongUShape   of un_ty * string
| WrongBShape   of bi_ty * string
| WrongMode     of mode * mode
| SwitchPMatch
| Internal of string



let pp_tyerr ppf s = match s with
 | UTypeMismatch(uty1, uty2)-> fprintf ppf "Cannot unify %a with %a" pp_utype uty1 pp_utype uty2
 | BTypeMismatch(bty1, bty2)  -> fprintf ppf "Cannot unify %a with %a" pp_btype bty1 pp_btype bty2
 | WrongUShape(uty, sh)     -> fprintf ppf "Unary type %a has wrong shape, expected %s type." pp_utype uty sh
 | WrongBShape(bty, sh)     -> fprintf ppf "Relational type %a has wrong shape, expected %s type." pp_btype bty sh
 | WrongMode(mu1, mu2)     -> fprintf ppf "Modes %a and %a do not match." pp_mode mu1 pp_mode mu2
  | NotUSubtype(uty1,uty2)   -> fprintf ppf "Unary type %a is not a subtype of %a" pp_utype uty1 pp_utype uty2
  | NotBSubtype(bty1,bty2)   -> fprintf ppf "Relational type %a is not a subtype of %a" pp_btype bty1 pp_btype bty2
  | SwitchPMatch            -> fprintf ppf "Switch pattern match to unary mode"
  | Internal s            -> fprintf ppf "Internal error: %s" s
