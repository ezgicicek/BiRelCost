open IndexSyntax

let letters = ["A";"B";"C";"D";"E";"F";"G";"H";"I";"J";"K";"L";"M";"N";"O";"P";"Q";"R";"S";"T";"U";"V";"W";"X";"Y";"Z"]
let cnt = ref 0
let meta_vars = ref letters


(*  New variable generator:  gen_var s and reset ()  *)
let gen_var s =
  let l = (! meta_vars) in
  if (List.length l) = 0 then(
    cnt := (! cnt) + 1;
    meta_vars := List.map (fun s -> "_" ^ s ^ string_of_int (! cnt)) letters)
  else ();
  let nhd = (List.hd (! meta_vars)) in 
  meta_vars := List.tl (! meta_vars);
  nhd

    
 let fresh_evar s =
   {v_name = gen_var s; v_type = BiEVar s}

 let fresh_ivar s =
   {v_name = gen_var s; v_type = BiIVar}
 
let reset () =
  cnt := 0;
  meta_vars :=letters

