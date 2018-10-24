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

let accept_empty = function
    | List [] -> Some (List [])
    | _ -> None

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

let parse (nt : string) (rule_fun : string -> psexp list) (accept : Sexp.t -> Sexp.t option) (expr : Sexp.t) : Sexp.t option = 
    let rec try_rules (rules : psexp list) (accept : Sexp.t -> Sexp.t option) (expr : Sexp.t) : Sexp.t option = match rules with
        | f :: r -> let res = match_rule f accept expr in if (match res with | None -> true | _ -> false) then (try_rules r accept expr) else res
        | [] -> None and
    match_rule (rule : psexp) (accept : Sexp.t -> Sexp.t option) (expr : Sexp.t) : Sexp.t option = 
        match (rule, expr) with 
        | (ZeroOrMore pexpr, _) -> 
            let res = accept expr in (match res with 
                | Some (List []) -> Some (List [])
                | _ -> match_rule (OneOrMore pexpr) accept expr)
        | (OneOrMore pexpr, _) -> match_rule pexpr (match_rule (ZeroOrMore pexpr) accept) expr
        | (NT strNT, List(f :: r)) -> 
            let res = try_rules (rule_fun strNT) (accept_empty) f in (match res with
                | None -> None
                | _ -> accept (List r))
        | (NT strNT, _) -> try_rules (rule_fun strNT) accept expr
        | (T strT, List ((Atom strE) :: r)) -> if String.equal strE strT then accept (List r) else None
        | (T strT, Atom strE) ->  if String.equal strE strT then accept (List []) else None
        | (PList(f :: r), _) -> match_rule f (match_rule (PList r) accept) expr
        | (PList([]), _) -> accept expr
        | (_,_) -> None
    in try_rules (rule_fun nt) accept_empty expr

let parser_gen (gram : grammar) (expression : Sexp.t) = 
  match (parse start_nt (get_rules gram) (accept_empty) expression) with 
    | Some(List []) -> true 
    | _ -> false

