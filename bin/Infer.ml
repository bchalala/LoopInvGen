open Core
open LoopInvGen

let output_stats stats = function
  | None -> ()
  | Some statsfile
    -> let stats_chan = Out_channel.create statsfile
        in Out_channel.output_string stats_chan
             (Sexplib.Sexp.to_string_hum ~indent:4 (LIG.sexp_of_stats stats))
         ; Out_channel.close stats_chan

let main expressiveness logfile statefile statsfile zpath
         max_conflicts max_strengthening_attempts max_restarts max_steps_on_restart
         min_separating_examples num_counter_examples filename () =
  Log.enable ~msg:"INFER" logfile ;
  let state_chan = Utils.get_in_channel statefile in
  let states = List.(permute
    ~random_state:(Random.State.make [| 79 ; 97 |])
    (map (Stdio.In_channel.input_lines state_chan)
         ~f:(fun l -> map (String.split ~on:'\t' l) ~f:Value.of_string)))
  in Stdio.In_channel.close state_chan
   ; Log.debug (lazy ("Loaded " ^ (Int.to_string (List.length states)) ^
                      " program states."))
   ; let sygus = SyGuS.read_from filename
     in let logic = Logic.of_string sygus.logic
     in let conf = {
       LIG.default_config with
       _VPIE = {
         LIG.default_config._VPIE with
         _PIE = {
           LIG.default_config._VPIE._PIE with
           _Synthesizer = {
             LIG.default_config._VPIE._PIE._Synthesizer with
             logic = logic
           ; max_level = expressiveness
           ; min_examples = min_separating_examples
           }
           ; max_conflict_group_size = (if max_conflicts > 0 then max_conflicts
                                      else (logic.conflict_group_size_multiplier
                                            * PIE.base_max_conflict_group_size)) ;
         }
       ; max_tries = max_strengthening_attempts
       ; num_counter_examples = num_counter_examples
       }
     ; max_restarts
     ; max_steps_on_restart
     }
     in let inv, stats = LIG.learnInvariant ~conf ~zpath ~states sygus
     in Out_channel.output_string Stdio.stdout
          SyGuS.(func_definition {
            sygus.inv_func with body = (translate_smtlib_expr inv)
          })
      ; output_stats stats statsfile

let spec =
  let open Command.Spec in (
      empty
      +> flag "-e" (optional_with_default 4 int)
         ~doc:"INTEGER expressiveness level. 4 = Polyhedra"
      +> flag "-l" (optional string)
         ~doc:"FILENAME enable logging"
      +> flag "-s" (required string)
         ~doc:"FILENAME states file, containing program states"
      +> flag "-t" (optional string)
         ~doc:"FILENAME output statistics"
      +> flag "-z" (required string)
         ~doc:"FILENAME path to the z3 executable"

      +> flag "-max-conflicting" (optional_with_default 0 int)
         ~doc:"INTEGER max size of the conflict group (POS+NEG). 0 = auto"
      +> flag "-max-strengthening" (optional_with_default (LIG.default_config._VPIE.max_tries) int)
         ~doc:"INTEGER max candidates to consider, per strengthening. 0 = unlimited"
      +> flag "-max-restarts" (optional_with_default (LIG.default_config.max_restarts) int)
         ~doc:"INTEGER number of times the inference engine may restart"
      +> flag "-max-steps-on-restart" (optional_with_default (LIG.default_config.max_steps_on_restart) int)
         ~doc:"NUMBER number of states to collect after each restart"
      +> flag "-min-separating-examples" (optional_with_default (LIG.default_config._VPIE._PIE._Synthesizer.min_examples) float)
         ~doc:"NUMBER percent of examples at a minimum necessary to separate conflict set"
      +> flag "-num-gen-counter-examples" (optional_with_default (LIG.default_config._VPIE.num_counter_examples) int)
         ~doc:"NUMBER number of counterexamples to be generated when precondition is not sufficient"
      +> anon ("filename" %: file)
    )

let () =
  Command.run
    (Command.basic_spec spec main
       ~summary: "Infer a loop invariant sufficient for proving the correctness of the input problem in SyGuS format.")
