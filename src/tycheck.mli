open Tycheck_sigs

module TyCheck (Ty : CH_TYPE) : CHECK with type ty = Ty.ty
