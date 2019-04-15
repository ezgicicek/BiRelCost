open Why3

(* Native @@ is already in ocaml 4.0 *)
let (@@) x y = x y

(* Core file, setup env and config *)

(* Read the config file *)
let config : Whyconf.config = Whyconf.read_config None

(* the [main] section of the config file *)
let main : Whyconf.main = Whyconf.get_main config

(* all the provers detected, from the config file *)
let provers : Whyconf.config_prover Whyconf.Mprover.t =
  Whyconf.get_provers config

(* builds the environment from the [loadpath] *)
let env : Env.env = Env.create_env @@
  (Whyconf.loadpath main) @
  ["./"]

