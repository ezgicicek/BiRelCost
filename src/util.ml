(* LICENSE:
   Based on PLEAC, adapted to use COLUMNS and tput

*)

(* Here we include general library and utility functions, not directly
   related to birel. Ideally, we would use library functions.
*)

let get_terminal_size () =

  let in_channel = Unix.open_process_in "stty size" in
  try
    begin
      try
        Scanf.fscanf in_channel "%d %d"
          (fun rows cols ->
             ignore (Unix.close_process_in in_channel);
             (rows, cols))
      with End_of_file ->
        ignore (Unix.close_process_in in_channel);
        (0, 0)
    end
  with e ->
    ignore (Unix.close_process_in in_channel);
    raise e

let map f s = String.map f s
