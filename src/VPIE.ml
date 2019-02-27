open Core_kernel

open Utils

type 'a config = {
  _PIE : PIE.config ;

  base_random_seed : string ;
  describe : (('a Job.feature Job.with_desc) CNF.t option) -> Job.desc ;
  max_tries : int ;
  simplify : bool ;
  num_counter_examples : int ;
}

type stats = {
  mutable vpi_ce : int ;
  mutable vpi_time_ms : float ;
  mutable _PIE : PIE.stats list ;
} [@@deriving sexp]

let default_config = {
  _PIE = PIE.default_config ;

  base_random_seed = "VPIE" ;
  describe = PIE.cnf_opt_to_desc ;
  max_tries = 512 ;
  simplify = true ;
  num_counter_examples = 1 ;
}


let learnVPreCond ?(conf = default_config) ?(eval_term = "true") ~(z3 : ZProc.t)
                  ?(consts = []) ~(post_desc : Job.desc) (job : Job.t)
                  : Job.desc * stats =
  let stats = { _PIE = [] ; vpi_time_ms = 0.0 ; vpi_ce = 0 } in
  let rec helper tries_left job =
    if conf.max_tries > 0 && tries_left < 1
    then (Log.error (lazy ("VPIE Reached MAX attempts ("
                            ^ (Int.to_string conf.max_tries)
                            ^ "). Giving up ..."))
         ; (conf.describe None, stats))
    else begin
      Log.info (lazy ("VPIE Attempt "
                      ^ (Int.to_string (1 + conf.max_tries - tries_left))
                      ^ "/" ^ (Int.to_string conf.max_tries) ^ ".")) ;
      match PIE.learnPreCond ~conf:conf._PIE ~consts job with
      | (None, pie_stats) | ((Some [[]]), pie_stats)
        -> Log.warn (lazy ("Failed to learn a verified precondition!"))
         ; stats._PIE <- pie_stats :: stats._PIE
         ; stats.vpi_time_ms <- stats.vpi_time_ms +. pie_stats.pi_time_ms
         ; ((conf.describe None), stats)
      | (precond, pie_stats)
        -> stats._PIE <- pie_stats :: stats._PIE
         ; stats.vpi_time_ms <- stats.vpi_time_ms +. pie_stats.pi_time_ms
         ; let pre_desc = conf.describe precond
            in Log.info (lazy ("Candidate Precondition: " ^ pre_desc))
             ; begin match ZProc.implication_counter_example
                             ~eval_term z3 pre_desc post_desc with
               | None -> let pre_desc = if conf.simplify
                                        then ZProc.simplify z3 pre_desc
                                        else pre_desc
                          in Log.info (lazy ("Verified Precondition: " ^ pre_desc))
                           ; (pre_desc, stats)
               | Some model
                 -> let model = Hashtbl.Poly.of_alist_exn model in
                    let test =
                      List.map2_exn job.farg_names job.farg_types
                        ~f:(fun n t -> match Hashtbl.find model n with
                                       | Some v -> v
                                       | None -> let open Quickcheck
                                                  in random_value (TestGen.for_type t)
                                                       ~size:1
                                                       ~seed:(`Deterministic (
                                                         conf.base_random_seed ^
                                                         (string_of_int tries_left))))
                      in Log.info (lazy ("Counter example: {"
                                        ^ (List.to_string_map2
                                             test job.farg_names ~sep:", "
                                             ~f:(fun v n -> n ^ " = " ^
                                                            (Value.to_string v)))
                                        ^ "}"))
                       ; stats.vpi_ce <- stats.vpi_ce + 1 ;
            let rec genCounterExamples ?(curCounters = "true") (job : Job.t) (n : int): Job.t =
                (if n <= 0 then job else
                match ZProc.gen_counter_example ~eval_term z3 pre_desc post_desc curCounters with
                  | None -> job
                  | Some model -> let model = Hashtbl.Poly.of_alist_exn model in
                      let test =
                        List.map2_exn job.farg_names job.farg_types
                          ~f:(fun n t -> match Hashtbl.find model n with
                                          | Some v -> v
                                          | None -> let open Quickcheck
                                                    in random_value (TestGen.for_type t)
                                                          ~size:1
                                                          ~seed:(`Deterministic (
                                                            conf.base_random_seed ^
                                                            (string_of_int tries_left))))
                        in Log.info (lazy ("Counter example: {"
                                          ^ (List.to_string_map2
                                                test job.farg_names ~sep:", "
                                                ~f:(fun v n -> n ^ " = " ^
                                                              (Value.to_string v)))
                                          ^ "}"))
                          ; stats.vpi_ce <- stats.vpi_ce + 1 ;
                        let counter_string = "(and " ^ (List.to_string_map2
                                                test job.farg_names ~sep:" "
                                                ~f:(fun v n -> "(= " ^ n ^ " " ^ (Value.to_string v) ^ ")")) ^ ")" in
                        let j = (Job.add_neg_test ~job test) in
                        (genCounterExamples ~curCounters:("(and " ^ curCounters ^ " (not " ^ counter_string ^ "))") j (n - 1)))
              in helper (tries_left - 1) (genCounterExamples job 5)
               end
    end
  in try helper conf.max_tries job
     with _ -> ("false" , stats)