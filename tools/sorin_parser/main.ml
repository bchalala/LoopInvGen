
open Core
open Core.Out_channel

let parse s : string = 
  let lexbuf = Lexing.from_string (s ^ "\n") in
  let ast = UserFunParser.main UserFunLexer.token lexbuf in
  ast

let main outfile filename () =
  Utils.start_logging_to ~msg:"INFER" logfile ;
  let state_chan = Utils.get_in_channel statefile in
  let states = List.(map (In_channel.input_lines state_chan)
                       ~f:(fun l -> map (Types.deserialize_values l)
                                        ~f:(fun v -> Option.value_exn v)))
  in In_channel.close state_chan
   ; Log.debug (lazy ("Loaded " ^ (string_of_int (List.length states)) ^
                      " program states."))
   ; let sygus = SyGuS.load (Utils.get_in_channel filename)
     in let synth_logic = Types.logic_of_string sygus.logic
     in let user_input = if (compare user_input_file "") then [] 
                    else In_channel.read_lines user_input_file
     in let conf = {
       LoopInvGen.default_config with
       for_VPIE = {
         LoopInvGen.default_config.for_VPIE with
         for_PIE = {
           LoopInvGen.default_config.for_VPIE.for_PIE with
           synth_logic;
           max_conflict_group_size = (if max_conflicts > 0 then max_conflicts
                                      else ((PIE.conflict_group_size_multiplier_for_logic synth_logic)
                                            * PIE.base_max_conflict_group_size)) ;
         }
       ; max_tries = max_strengthening_attempts ;
       }
     ; max_restarts
     ; max_steps_on_restart
     ; user_functions = Utils.gen_user_functions user_input_unparsed sygus.state_vars ;
     }
     in let inv = LoopInvGen.learnInvariant ~conf ~zpath ~states sygus
     in let out_chan = Utils.get_out_channel outfile
     in if (not do_false) && inv = "false" then ()
        else output_string out_chan (build_inv_func (ZProc.normalize inv) ~sygus)
      ; Out_channel.close out_chan
      ; exit (if inv = "false" then 1 else 0)

let spec =
  let open Command.Spec in (
      empty
      +> flag "-o" (optional string)  ~doc:"FILENAME output file for invariant, defaults to stdout"
      +> anon (maybe_with_default "-" ("filename" %: file))
    )

let cmd =
  Command.basic_spec spec main
    ~summary: "Parses user inputs from Sorin."

let () =
  Command.run
    ~version:"0.6b"
    ~build_info:("padhi @ " ^ (Core_extended.Logger.timestamp ()))
    cmd
