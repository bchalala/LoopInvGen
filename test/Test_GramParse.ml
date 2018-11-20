open Base
open LoopInvGen
open LoopInvGen.GramParse

let empty_grammar () = 
    let g = Parsexp.Single.parse_string_exn "(Start Int ())" in
    let p1, p2 = parser_gen [g] in 
    let s = Parsexp.Single.parse_string_exn "()" in 
    Alcotest.(check bool) "empty grammar parses nothing" false 
    ((p2 s) && (equal 0 (List.length (p1 s))))
    
let empty_list_grammar () = 
    let g = Parsexp.Single.parse_string_exn "(Start Int (()))" in
    let _, p2 = parser_gen [g] in 
    let s = Parsexp.Single.parse_string_exn "()" in 
    Alcotest.(check bool) "empty list grammar parses empty list" true 
    ((p2 s) && (equal 1 (List.length (p1 s))))

let get_example_parser () = 
    let g = Parsexp.Single.parse_string_exn 
        "(
            (Start Int (x y 0 1
                (+ Start Start)
                (- Start Start)
                (ite StartBool Start Start)))
            (StartBool Bool ((and StartBool StartBool)
                  (or StartBool StartBool)
                  (not StartBool)
                  (<= Start Start)
                  (= Start Start)
                  (>= Start Start)))
        )" in parser_gen (match g with | List(a) -> a)

let example_sygus_grammar_empty_list () = 
    let p1, p2 = get_example_parser () in
    let s = Parsexp.Single.parse_string_exn "()" in 
    Alcotest.(check bool) "sygus gram handles empty invparser" false 
    ((p2 s) && (equal 0 (List.length (p1 s))))

let example_sygus_grammar_parse_exp () =
    let p1, p2 = get_example_parser () in
    let s = Parsexp.Single.parse_string_exn "(+ x (- y (ite (<= 1 0) 1 0)))" in 
    Alcotest.(check bool) "sygus gram handles empty invparser" true 
    ((p2 s) && (equal 1 (List.length (p1 s))))

let get_parser_with_ebnf () = 
    let g = Parsexp.Single.parse_string_exn 
        "(
            (Start Int (x y 0 1
                (+ Start Start)
                (- Start Start)
                (ite StartBool Start Start)))
            (StartBool Bool ((and StartBool StartBool* StartBool)
                  (>= Start Start)))
        )" in parser_gen (match g with | List(a) -> a)

let ebnf_grammar_parse_exp_repeat_0 () =
    let p1, p2 = get_parser_with_ebnf () in
    let s = Parsexp.Single.parse_string_exn "(and (>= 0 1) (>= 0 0))" in 
    Alcotest.(check bool) "ebnf gram handles parse nothing" true 
    ((not (p2 s)) && (equal 1 (List.length (p1 s))))

let ebnf_grammar_parse_exp_repeat_multiple () =
    let p1, p2 = get_parser_with_ebnf () in
    let s = Parsexp.Single.parse_string_exn "(and (>= 0 1) (>= 0 0) (>= 1 1) (>= (+ x y) y))" in 
    Alcotest.(check bool) "ebnf gram handles parse nothing" true 
    ((not (p2 s)) && (equal 1 (List.length (p1 s))))


let all = [
  "Empty grammar",                                  `Quick, empty_grammar  ;
  "Empty list grammar test",                        `Quick, empty_list_grammar    ;
  "SyGuS grammar fails to parse empty list",        `Quick, example_sygus_grammar_empty_list ;
  "SyGuS grammar parses exp",                       `Quick, example_sygus_grammar_parse_exp ;
  "Parse 0 occurences of nonterminal",              `Quick, ebnf_grammar_parse_exp_repeat_0 ;
  "Parse multiple occurences of nonterminal",       `Quick, ebnf_grammar_parse_exp_repeat_multiple ;
]