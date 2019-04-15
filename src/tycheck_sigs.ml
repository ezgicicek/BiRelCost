module type CH_TYPE =
    sig
      type ty
    end

 

module type CHECK =
    sig
      open IndexSyntax
      open Constr
      open Ctx
      open Support.FileInfo

      type ty
      type cost = iterm option

      type 'a ty_error = 
          Right of 'a
        | Left  of Ty_error.ty_error_elem Support.FileInfo.withinfo

      (* Reader/Error monad for type-checking *)
      type 'a checker = (ty context * cost) -> 'a ty_error
          
      (* Reader/Error monad for type-inference *)
      type 'a inferer = ty context -> ('a * constr * sort ctx * cost) ty_error

      
      val (>>=) : 'a checker -> ('a -> 'b checker) -> 'b checker
      val (>>>=) : 'a checker -> ('a -> 'b checker) -> 'b checker
      val (>>)   : constr checker -> constr checker -> constr checker
      val (>&&>)  : constr checker -> constr checker -> constr checker
      val (>||>)  : constr checker -> constr checker -> constr checker
      val (<<=)  : 'a inferer -> ('a -> 'b inferer) -> 'b inferer
      val (<->=) : ty inferer -> (ty -> constr checker) -> constr checker
      val (=<->) : ty inferer-> (ty -> Ctx.heurMode -> (constr checker  * ty * iterm) list ) -> ty inferer      
      val return_ch     : constr -> 'a * 'b  -> constr ty_error
      val return_inf    : 'a -> 'a inferer
      val return_leaf_ch : 'a context * cost  -> constr ty_error
      val fail : info -> Ty_error.ty_error_elem -> 'a -> 'b ty_error

      val get_infer_ctx  : ty context inferer
      val get_var_ty     : info -> var_info -> ty inferer
      val get_heur       : heurMode checker

      val with_new_ctx : (ty context -> ty context) -> 'a checker -> 'a checker
     
      (* Extend the type context with a fresh type variable binding, for checker *)
      val (|:|) : var_info -> ty -> constr checker -> constr checker

      (* Extend the sort context with a fresh index variable binding, for checker *)
      val (|::|) : var_info -> sort -> info -> constr checker -> constr checker

      (* Extend the existential context with a fresh index variable binding, for checker *)
      val (|:::|) : var_info -> sort -> info -> constr checker -> constr checker

      (* Change checking mode *)
      val with_mode : Syntax.mode -> 'a checker -> 'a checker
      
      val check_size_eq : iterm -> iterm -> constr checker -> constr checker
      val assume_size_eq : iterm -> iterm -> constr checker -> constr checker
      val assume_size_leq : iterm -> iterm -> constr checker -> constr checker
      val check_size_leq : iterm -> iterm -> constr checker -> constr checker
      
      val cost_cs : 'a context -> iterm * iterm -> constr

    end
 
