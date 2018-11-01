open Base
open Exceptions
open Sexplib.Type

type psexp = 
    | ZeroOrMore of psexp
    | OneOrMore of psexp
    | NT of string
    | T of string
    | PList of psexp list

type grammar = (string*(psexp list)) list

let start_nt = "Start"

let rec gen_psgram (nts : string list) (gram : Sexp.t) : psexp = match gram with
    | Atom(x) -> 
        let last_letter = String.get x (String.length x - 1) in
        let str = if Char.equal last_letter '+' or Char.equal last_letter '*' then String.sub x 0 (String.length x - 1) else x in
                  if not (List.exists ~f:(String.equal str) nts) then T x else (match last_letter with 
                    | '+' -> OneOrMore (NT str)
                    | '*' -> ZeroOrMore (NT str)
                    | _ -> NT x)
    | List (f :: r) -> 
        let fP = gen_psgram nts f in
        let fR = gen_psgram nts (List r) in (match fR with | PList fRL -> PList (fP :: fRL))
    | List ([]) -> PList []

let rec get_rules (gram : grammar) (nt : string) : psexp list = match gram with
    | (nt_cand,rules) :: rest -> if String.equal nt nt_cand then rules else get_rules rest nt
    | [] -> []

let get_nt (ntruleset : Sexp.t) : string = match ntruleset with 
    | List(Atom(nt) :: _) -> nt
    | _ as sexp -> raise (Parse_Exn ("Unknown gram exp: " ^ (Sexp.to_string_hum sexp)))

let rec transform_gram (nts : string list) (gram : Sexp.t list) : grammar = match gram with
    | List([Atom(nt_cand); _; List(l)]) :: rest -> (nt_cand, List.map ~f:(gen_psgram nts) l) :: (transform_gram nts rest)
    | [] -> []

let get_gram (unparsedgram : string) : grammar = match Sexplib.Sexp.of_string unparsedgram with
    | List(gram) -> transform_gram (List.map gram ~f:get_nt) gram
    | _ as sexp -> raise (Parse_Exn ("Unknown gram exp: " ^ (Sexp.to_string_hum sexp))) 

let rec try_rules (rule_fun : string -> psexp list) (rules : psexp list) (continue : (unit -> 'b) -> Sexp.t -> 'b) 
                      (reject : unit -> 'b) (expr : Sexp.t) : 'b = match rules with
        | f :: r -> let new_reject = (fun () -> try_rules rule_fun r continue reject expr) in
                    let new_continue = (fun rej -> function | List([]) -> continue rej (List ([])) | _ -> rej ()) in 
                    match_rule rule_fun f new_continue new_reject expr 
        | [] -> reject () 
and    
match_rule (rule_fun : string -> psexp list) (rule : psexp) (continue : (unit -> 'b) -> Sexp.t -> 'b) (reject : unit -> 'b) (expr : Sexp.t) : 'b = 
        match (rule, expr) with 
        | (ZeroOrMore pexpr, _) ->
            let continue_on_reject = (fun () -> continue reject expr) in 
            match_rule rule_fun pexpr 
                (match_rule rule_fun (ZeroOrMore pexpr) continue) 
            continue_on_reject 
            expr
        | (OneOrMore pexpr, _) -> 
                match_rule rule_fun pexpr 
                    (match_rule rule_fun (ZeroOrMore pexpr) continue) 
                reject 
                expr
        | (NT strNT, List(f :: r)) ->  
                try_rules rule_fun (rule_fun strNT) (fun rj -> function | List [] -> (continue rj (List r))  | _ -> rj ()) reject f
        | (NT strNT, Atom(e)) -> try_rules rule_fun (rule_fun strNT) continue reject expr
        | (T strT, List ((Atom strE) :: r)) -> if String.equal strE strT then continue reject (List r) else reject ()
        | (T strT, Atom strE) ->  if String.equal strE strT then continue reject (List []) else reject ()
        | (PList(f :: r), _) -> match_rule rule_fun f (match_rule rule_fun (PList r) continue) reject expr
        | (PList([]), List([])) -> continue reject (List [])
        | (_,_) -> reject ()

let parse (nt : string) (rule_fun : string -> psexp list) (expr : Sexp.t) : Sexp.t option = 
    try_rules rule_fun (rule_fun nt) (fun rej -> function | List a -> Some (List a) | _ -> rej ()) (fun () -> None) expr

let parse_gram (rule_fun : string -> psexp list) (expression : Sexp.t) (start : string) : bool = 
  match (parse start rule_fun expression) with 
    | Some(List []) -> true 
    | _ -> false

let parser_gen (gramSexp : Sexp.t list) : (Sexp.t -> string list)*(Sexp.t -> bool) = 
    let nts = List.map ~f:(get_nt) gramSexp in
    let gram = transform_gram nts gramSexp in
    let rule_fun = get_rules gram in
    ((fun (expression : Sexp.t) -> List.filter nts ~f:(parse_gram rule_fun expression)),
     (fun (expression : Sexp.t) -> parse_gram rule_fun expression start_nt))
    
