(*SETTING UP DELAYED FUNCTION CALLING*)
let and_then (f : 'a -> ('b, 'e) result) (res : ('a, 'e) result): ('b, 'e) result =
  Result.bind res f
(*SUPPORT FOR TAILORED OPTIONS*)
let all_ok (ls : ('a, 'e) result list): ('a list, 'e) result =
  let combine_result a b =
    a |> and_then @@ fun a ->
    b |> and_then @@ fun b ->
    Ok(b :: a)
  in
  List.fold_left combine_result (Ok([])) ls |> Result.map List.rev

(*PROGRAM DEFINITIONS*)
type var = Var of string

(*CONSTANT TYPES*)
type const =
  | Int of int
  | String of string
  | Name of var

(*COMMAND TYPES*)
type com =
  | Quit
  | Push of const
  | Pop
  | Add
  | Sub
  | Mul
  | Div
  | Swap
  | Neg
  | Concat
  | And
  | Or
  | Not
  | Equal
  | Lte
  | Local of var
  | Global of var
  | BeginEnd of prog
  | IfThenElse of prog * prog
  | InjL
  | InjR
  | CaseLeftRight of prog*prog
  | Tuple of const
  | Get of const
  | Fun of var*var*prog
  | Mut of var*var*prog
  | Call
  | Return

and prog = com list

and value =
  | VInt of int
  | VString of string
  | Left of value
  | Right of value
  | Tuple of value list
  | Clo of ((var*value) list) * (var*var*prog) * ((var*var*prog) list)

(*PROGRAM FUNDAMENTAL STRUCTURS: STACK, LOG, ENVIRONMENT, STATE*)
type stack = value list
type log = string list

type env = (var * value) list
type state = stack * log * (* local *) env * (* global *) env * (* functions *) env

let int_of_bool (b : bool): int =
  if b then 1 else 0

let is_bool (n : int): bool =
  n = 0 || n = 1

(*GLOBAL, LOCAL, AND ENVIRONMENT VARIABLE LOOKUP*)
let lookup_bind (x : var) (envs : env * env * env): value option =
  let rec lookup e =
    match e with
    | [] -> None
    | (y, v)::rst -> if y = x
        then Some(v)
        else lookup rst
  in
  let (local, global, funcs) = envs in
  match lookup funcs with
  | Some(b) -> Some(b)
  | None -> (
      match lookup local with 
      | None -> lookup global
      | Some(v) -> Some(v))

(*ADDING VARIABLES TO GLOBAL, LOCAL, AND ENVIRONMENTS*)
let add_bind (x : var) (v : value) (e : env): env  =
  let updated, e =
    List.fold_left
      (fun (updated, acc) (y, v') ->
         if y = x
         then true, (y, v)::acc
         else updated, (y, v')::acc)
      (false, [])
      e
  in
  let e = List.rev e in
  if updated then e else (x, v)::e

(*# OF STACK CALLS FOR ERRORS*)
let com_arity (c : com): int =
  match c with
  | Quit | Push(_) | BeginEnd(_) | IfThenElse(_) | CaseLeftRight(_) | Fun(_) | Mut(_) -> 0
  | Pop  | Neg | Not | Local(_) | Global(_) | InjL | InjR | Tuple(_) | Get(_) | Return -> 1
  | Add  | Sub | Mul | Div | Swap | Concat | And | Or | Equal | Lte | Call -> 2

(*PRINTERS*)
let string_of_const c =
  match c with
  | Int(i)       -> string_of_int i
  | String(s)    -> "\"" ^ s ^ "\""
  | Name(Var(v)) -> v

let rec string_of_value v =
  match v with
  | VInt(i)    -> string_of_int i
  | VString(s) -> "\"" ^ s ^ "\"" 
  | Left(x) -> "Left " ^ (string_of_value x)
  | Right(x) -> "Right " ^ (string_of_value x)
  | Tuple(x) -> 
      let tuple_string = List.fold_left (fun acc x -> acc ^ (string_of_value x) ^ ", ") "" x in 
      if (String.length tuple_string - 2) > 0 then
        "(" ^ (String.sub tuple_string 0 (String.length tuple_string - 2)) ^ ")"
      else
        "(" ^ ")"
  | Clo (ev, tp, li) -> 
      match tp with
      | Var(fn), Var(arg), prog -> "Clo (" ^ fn ^ ", " ^ arg ^ ")"

let rec string_of_com (c : com) : string =
  match c with
  | Quit    -> "Quit"
  | Push(c) -> Printf.sprintf "Push %s" (string_of_const c)
  | Pop     -> "Pop"
  | Add     -> "Add"
  | Sub     -> "Sub"
  | Mul     -> "Mul"
  | Div     -> "Div"
  | Swap    -> "Swap"
  | Neg     -> "Neg"
  | Concat  -> "Concat"
  | And     -> "And"
  | Or      -> "Or"
  | Not     -> "Not"
  | Equal   -> "Equal"
  | Lte     -> "Lte"
  | Local (Var(v))   -> Printf.sprintf "Local %s" v
  | Global(Var(v))   -> Printf.sprintf "Global %s" v
  | BeginEnd(p)      ->
      "Begin\n"
      ^ List.fold_left (fun acc x -> acc ^ "\n" ^ string_of_com x ) "" (List.rev p)
      ^ "\nEnd\n"
  | IfThenElse(t, e) ->
      "IfThen\n"
      ^ List.fold_left (fun acc x -> acc ^ "\n" ^ string_of_com x ) "" (List.rev t)
      ^ "\nElse\n"
      ^ List.fold_left (fun acc x -> acc ^ "\n" ^ string_of_com x ) "" (List.rev e)
      ^ "\nEnd\n"
  | InjL -> "InjL"
  | InjR -> "InjR"
  | CaseLeftRight(l, r) -> 
      "CaseLeft\n"
      ^ List.fold_left (fun acc x -> acc ^ "\n" ^ string_of_com x ) "" (List.rev l)
      ^ "\nRight\n"
      ^ List.fold_left (fun acc x -> acc ^ "\n" ^ string_of_com x ) "" (List.rev r)
      ^ "\nEnd\n"
  | Tuple(v) -> Printf.sprintf "Tuple %s" (string_of_const v)
  | Get(v)   -> Printf.sprintf "Get %s" (string_of_const v)
  | Fun(Var(f_name), Var(arg), pr)-> 
      "Fun\n"
      ^ List.fold_left (fun acc x -> acc ^ "\n" ^ string_of_com x ) "" (List.rev pr)
      ^ "\nEnd\n"
  | Mut(Var(f_name), Var(arg), pr)-> 
      "Mut\n"
      ^ List.fold_left (fun acc x -> acc ^ "\n" ^ string_of_com x ) "" (List.rev pr)
      ^ "\nEnd\n"
  | Call -> "Call"
  | Return -> "Return"

let rec string_of_list (p : 'a -> string) (ls : 'a list): string =
  match ls with
  | []       -> "[]"
  | fst::rst -> p fst ^ "::" ^ string_of_list p rst

(*TOKENIZING*)
let char_list_of_string (s : string): char list =
  List.init (String.length s) (String.get s)

type token =
  | NEWLINE
  | STRING of string
  | NUMBER of int
  | SYMBOL of string

let string_of_token tok =
  match tok with
  | NEWLINE   -> "\\n"
  | STRING(s) -> "\"" ^ s ^ "\""
  | NUMBER(n) -> string_of_int n
  | SYMBOL(s) -> s

let is_space (c : char): bool =
  c = ' ' || c = '\t'

let is_digit (c : char): bool =
  match c with | '0' .. '9' -> true | _ -> false

let is_alpha (c : char): bool =
  match c with | 'a' .. 'z' | 'A' .. 'Z' -> true | _ -> false

let int_of_char (c : char): int =
  int_of_string @@ Char.escaped c

type lexer_err =
  | UnclosedString of (* line number *) int
  | InvalidChar    of (* line number *) int * char
  | UnknownChar    of (* line number *) int * char

let string_of_lexer_err e =
  match e with
  | UnclosedString(i) -> Printf.sprintf "Unclosed string at line %i" i
  | InvalidChar(i, c) -> Printf.sprintf "Invalid char '%c' at line %i" c i
  | UnknownChar(i, c) -> Printf.sprintf "Unknown char '%c' at line %i" c i


let tokenize_string line_num (ls : char list): (string * char list, lexer_err) result =
  let rec helper ls acc =
    match ls with
    | [] -> Error(UnclosedString(line_num))
    | ch::rst ->
        if ch = '\"' then
          Ok(acc, rst)
        else if is_alpha ch then
          helper rst (acc ^ Char.escaped ch)
        else
          Error(InvalidChar(line_num, ch))
  in helper ls ""

let tokenize_number line_num (ls : char list): (int * char list, lexer_err) result =
  let rec helper ls acc =
    match ls with
    | [] -> Ok(acc, [])
    | ch::rst ->
        if ch = '\n' || is_space ch then
          Ok(acc, ls)
        else if is_digit ch then
          helper rst @@ acc * 10 + int_of_char ch
        else Error(InvalidChar(line_num, ch))
  in helper ls 0

let tokenize_symbol line_num (ls : char list): (string * char list, lexer_err) result =
  let rec helper ls acc =
    match ls with
    | [] -> Ok(acc, [])
    | ch::rst ->
        if ch = '\n' || is_space ch then
          Ok(acc, ls)
        else if is_alpha ch || ch = '_' || is_digit ch then
          helper rst (acc ^ Char.escaped ch)
        else
          Error(InvalidChar(line_num, ch))
  in helper ls ""

let tokenize_source (src : string): (token list, lexer_err) result =
  let rec helper line_num ls acc =
    match ls with
    | [] -> Ok(List.rev @@ acc)
    | ch::rst ->
        match ch with
        | '\n' -> helper (line_num + 1) rst (NEWLINE :: acc)
        | '\"' -> tokenize_string line_num rst |> and_then @@ fun (s, rst) ->
            helper line_num rst (STRING(s) :: acc)
        | '-'  -> tokenize_number line_num rst |> and_then @@ fun (n, rst) ->
            helper line_num rst (NUMBER(-1 * n) :: acc)
        | ch when is_digit ch
          -> tokenize_number line_num (ch::rst) |> and_then @@ fun (n, rst) ->
            helper line_num rst (NUMBER(n) :: acc)
        | ch when is_alpha ch
          -> tokenize_symbol line_num ls |> and_then @@ fun (s, rst) ->
            helper line_num rst (SYMBOL(s) :: acc)
        | ch when is_space ch -> helper line_num rst acc
        | ch -> Error(UnknownChar(line_num, ch))
  in helper 1 (char_list_of_string src) []


(*PARSING*)
type parse_err =
  | MissingArguments of (* line number *) int
  | InvalidCom       of (* line number *) int * token
  | ExpectedConst    of (* line number *) int * token
  | ExpectedVar      of (* line number *) int * token
  | InvalidVar       of (* line number *) int * token
  | UnexpectedEOF    of (* line number *) int
  | MissingNewline   of (* line number *) int

let string_of_parse_err e =
  match e with
  | MissingArguments(i) ->
      Printf.sprintf "Missing arguments to command at line %i" i
  | InvalidCom(i, tok) ->
      Printf.sprintf "Invalid command at line %i, got: \"%s\"" i (string_of_token tok)
  | ExpectedConst(i, tok) ->
      Printf.sprintf "Expected constant at line %i, got: \"%s\"" i (string_of_token tok)
  | ExpectedVar(i, tok) ->
      Printf.sprintf "Expected a variable name at line %i, got: \"%s\"" i (string_of_token tok)
  | InvalidVar(i, tok) ->
      Printf.sprintf "Invalid variable name at line %i, got: \"%s\"" i (string_of_token tok)
  | UnexpectedEOF(i) ->
      Printf.sprintf "Ran out of tokens at line %i" i
  | MissingNewline(i) ->
      Printf.sprintf "Missing newline on line %i" i

(*DEPENDS ON: Symbol tokens being valid variables with arbitrary case starting char*)
let make_var line_num (s : string): (var, parse_err) result =
  if String.length s <> 0 then
    match String.get s 0 with
    | 'a' .. 'z' -> Ok(Var(s))
    | _ -> Error(InvalidVar(line_num, SYMBOL(s)))
  else Error(InvalidVar(line_num, SYMBOL(s)))

(*Consume a newline from the token list, if it is required and not present, error.*)
let consume_newline (line_num : int) (required : bool) (ls : token list)
  : (int * token list, parse_err) result =
  match ls with
  | [] -> Ok(line_num, [])
  | NEWLINE::tl -> Ok((line_num + 1, tl))
  |      hd::tl -> if required then
        Error(MissingNewline(line_num))
      else
        Ok(line_num, hd::tl)

(*MUTUAL RECURSIVE COMMAND PARSING*)
let rec parse_com line_num ls : (com * int * token list, parse_err) result =
  let parse_const line_num tok =
    match tok with
    | NUMBER(n) -> Ok(Int(n))
    | STRING(s) -> Ok(String(s))
    | SYMBOL(s) -> make_var line_num s |> Result.map (fun x -> Name(x))
    | tok       -> Error(ExpectedConst(line_num, tok))
  in
  match ls with
  | SYMBOL("Push")  ::fst::rst ->
      parse_const line_num fst |> and_then @@ fun x ->
      Ok(Push(x), line_num, rst)
  | SYMBOL("Quit")  ::rst -> Ok(Quit, line_num, rst)
  | SYMBOL("Pop")   ::rst -> Ok(Pop, line_num, rst)
  | SYMBOL("Add")   ::rst -> Ok(Add, line_num, rst)
  | SYMBOL("Sub")   ::rst -> Ok(Sub, line_num, rst)
  | SYMBOL("Mul")   ::rst -> Ok(Mul, line_num, rst)
  | SYMBOL("Div")   ::rst -> Ok(Div, line_num, rst)
  | SYMBOL("Swap")  ::rst -> Ok(Swap, line_num, rst)
  | SYMBOL("Neg")   ::rst -> Ok(Neg, line_num, rst)
  | SYMBOL("Concat")::rst -> Ok(Concat, line_num, rst)
  | SYMBOL("And")   ::rst -> Ok(And, line_num, rst)
  | SYMBOL("Or")    ::rst -> Ok(Or, line_num, rst)
  | SYMBOL("Not")   ::rst -> Ok(Not, line_num, rst)
  | SYMBOL("Equal") ::rst -> Ok(Equal, line_num, rst)
  | SYMBOL("Lte")   ::rst -> Ok(Lte, line_num, rst) 
  | SYMBOL("Local") ::SYMBOL(s)::rst ->
      make_var line_num s |> Result.map @@ fun x -> Local(x), line_num, rst
  | SYMBOL("Local") ::c::rst -> Error(ExpectedVar(line_num, c)) 
  | SYMBOL("Global")::SYMBOL(s)::rst ->
      make_var line_num s |> Result.map @@ fun x -> Global(x), line_num, rst
  | SYMBOL("Global")::c::rst -> Error(ExpectedVar(line_num, c)) 
  | SYMBOL("Begin") ::rst ->
      consume_newline line_num false rst
      |> and_then @@ fun (line_num, rst) ->
      parse_com_list line_num (SYMBOL("End")) rst
      |> and_then @@ fun (blk, line_num, rst) ->
      Ok(BeginEnd(blk), line_num, rst) 
  | SYMBOL("IfThen")::rst ->
      consume_newline line_num false rst
      |> and_then @@ fun (line_num, rst) ->
      parse_com_list line_num (SYMBOL("Else")) rst
      |> and_then @@ fun (then_blk, line_num, rst) ->
      consume_newline line_num false rst
      |> and_then @@ fun (line_num, rst) ->
      parse_com_list line_num (SYMBOL("End")) rst
      |> and_then @@ fun (else_blk, line_num, rst) ->
      Ok(IfThenElse(then_blk, else_blk), line_num, rst)
  | SYMBOL("InjL")  ::rst -> Ok(InjL, line_num, rst)
  | SYMBOL("InjR")  ::rst -> Ok(InjR, line_num, rst)
  | SYMBOL("CaseLeft")::rst -> 
      consume_newline line_num false rst
      |> and_then @@ fun (line_num, rst) ->
      parse_com_list line_num (SYMBOL("Right")) rst
      |> and_then @@ fun (left_blk, line_num, rst) ->
      consume_newline line_num false rst
      |> and_then @@ fun (line_num, rst) ->
      parse_com_list line_num (SYMBOL("End")) rst
      |> and_then @@ fun (right_blk, line_num, rst) ->
      Ok(CaseLeftRight(left_blk, right_blk), line_num, rst)
  | SYMBOL("Tuple")::fst::rst -> 
      parse_const line_num fst |> and_then @@ fun x ->
      Ok(Tuple(x), line_num, rst)
  | SYMBOL("Get")::fst::rst ->
      parse_const line_num fst |> and_then @@ fun x ->
      Ok(Get(x), line_num, rst)
  | SYMBOL("Fun")::SYMBOL(fst)::SYMBOL(scd)::rst -> 
      consume_newline line_num false rst
      |> and_then @@ fun (line_num, rst) ->
      parse_com_list (line_num) (SYMBOL("End")) rst
      |> and_then @@ fun (right_blk, line_num, rst) ->
      Ok(Fun(Var(fst), Var(scd), right_blk), line_num, rst)
  | SYMBOL("Mut")::SYMBOL(fst)::SYMBOL(scd)::rst -> 
      consume_newline line_num false rst
      |> and_then @@ fun (line_num, rst) ->
      parse_com_list_2 line_num (SYMBOL("Mut")) (SYMBOL("End")) rst
      |> and_then @@ fun (right_blk, line_num, rst) ->
      Ok(Mut(Var(fst), Var(scd), right_blk), line_num, rst)
  | SYMBOL("Call")  ::rst -> Ok(Call, line_num, rst)
  | SYMBOL("Return")::rst -> Ok(Return, line_num, rst)
  | tok::_ -> Error(InvalidCom(line_num, tok))
  | [] -> Error(UnexpectedEOF(line_num))
and parse_com_list (line_num : int) (terminator : token) (ls : token list)
  : (prog * int * token list, parse_err) result =
  match ls with
  | fst::rst when fst = terminator -> Ok([], line_num, rst)
  | _  -> parse_com line_num ls
          |> and_then @@ fun (fst, line_num, ls') ->
      consume_newline line_num false ls'
      |> and_then @@ fun (line_num, ls'') ->
      parse_com_list line_num terminator ls''
      |> and_then @@ fun (rst, line_num, ls''') ->
      Ok((fst::rst, line_num, ls'''))
(*ALTERNATIVE PARSE CALL FOR MUTUAL RECURSION SUPPORT*)
and parse_com_list_2 (line_num : int) (terminator_1 : token) (terminator_2 : token) (ls : token list)
  : (prog * int * token list, parse_err) result =
  match ls with
  | fst::rst when fst = terminator_1 -> Ok([], line_num, ls)
  | fst::rst when fst = terminator_2 -> Ok([], line_num, NEWLINE::SYMBOL("End")::rst)
  | _  -> parse_com line_num ls
          |> and_then @@ fun (fst, line_num, ls') ->
      consume_newline line_num false ls'
      |> and_then @@ fun (line_num, ls'') ->
      parse_com_list_2 line_num terminator_1 terminator_2 ls''
      |> and_then @@ fun (rst, line_num, ls''') ->
      Ok((fst::rst, line_num, ls'''))

(*PARSE COMMAND*)
let parse_program (src : token list): (prog, parse_err) result  =
  let rec parse_all line_num ls acc  =
    match ls with
    | [] -> Ok(List.rev acc)
    | _  -> parse_com line_num ls
            |> and_then @@ fun (c, line_num, ls) ->
        consume_newline line_num true ls
        |>  and_then @@ fun (line_num, ls) ->
        parse_all line_num ls (c::acc)
  in
  parse_all 1 src []

(*EVALUATION*)
type eval_err =
  | InvalidArity of com * (* # got *) int
  | WrongType    of com * (* args got *) value list
  | DivByZero    of int * int
  | UnboundVar   of var
  | NoValue      of com

let string_of_eval_err e =
  match e with
  | InvalidArity(c, i) ->
      Printf.sprintf "Got %i arguments to %s, expected %i" i (string_of_com c) (com_arity c)
  | WrongType(_, ls) ->
      Printf.sprintf "Got arguments of incorrect type: " ^ string_of_list string_of_value ls
  | DivByZero(m, n) ->
      Printf.sprintf "Got arguments to div: %i / %i" m n
  | UnboundVar(Var(s)) ->
      Printf.sprintf "Unbound variable %s" s
  | NoValue(c) ->
      Printf.sprintf "Expected return value from command %s" (string_of_com c)

let with_stack (f : stack -> (stack, 'e) result) (s, l, loc, glob, func : state): (state, 'e) result =
  f s |> Result.map (fun s -> s, l, loc, glob, func)

(*PROGRAM METHODS*)
(* Quit program *)
let quit (stk, log, loc, glob, func : state): state =
  stk
, (List.fold_right
     (fun elem acc -> string_of_value elem :: acc)
     stk
     [])
  @ log
, loc
, glob
, func

(* Push values onto stack *)
let push (stk, log, loc, glob, func : state) (c : const): (state, eval_err) result =
  match c with
  | Name(v)   -> lookup_bind v (loc, glob, func)
                 |> Option.to_result ~none:(UnboundVar(v))
                 |> Result.map (fun x -> x::stk, log, loc, glob, func)
  | String(s) -> Ok(VString(s) :: stk, log, loc, glob, func)
  | Int(n)    -> Ok(VInt(n) :: stk, log, loc, glob, func)

(* Pop values off stack *)
let pop : state -> (state, eval_err) result =
  with_stack @@
  function
  | []    -> Error(InvalidArity(Pop, 0))
  | _::tl -> Ok(tl)

(* Add top two values on stack *)
let add : state -> (state, eval_err) result =
  with_stack @@
  function
  | VInt(x) :: VInt(y) :: rst -> Ok(VInt(x + y) :: rst)
  | _ :: [] | [] as stk       -> Error(InvalidArity(Add, List.length stk))
  | x :: y :: _               -> Error(WrongType(Add, [x; y]))

(* Subtract top two values on stack *)
let sub : state -> (state, eval_err) result =
  with_stack @@
  function
  | VInt(x) :: VInt(y) :: rst -> Ok(VInt(x - y) :: rst)
  | _ :: [] | [] as stk       -> Error(InvalidArity(Sub, List.length stk))
  | x :: y :: _               -> Error(WrongType(Sub, [x; y]))

(* Multiply top two values on stack *)
let mul : state -> (state, eval_err) result =
  with_stack @@
  function
  | VInt(x) :: VInt(y) :: rst -> Ok(VInt(x * y) :: rst)
  | _ :: [] | [] as stk       -> Error(InvalidArity(Mul, List.length stk))
  | x :: y :: _               -> Error(WrongType(Mul, [x; y]))

(* Divide top two values on stack *)
let div : state -> (state, eval_err) result =
  with_stack @@
  function
  | VInt(x) :: VInt(0) :: _   -> Error(DivByZero(x, 0))
  | VInt(x) :: VInt(y) :: rst -> Ok(VInt(x / y) :: rst)
  | _ :: [] | [] as stk       -> Error(InvalidArity(Div, List.length stk))
  | x :: y :: _               -> Error(WrongType(Div, [x; y]))

(* Swap top two values on stack *)
let swap : state -> (state, eval_err) result =
  with_stack @@
  function
  | x :: y :: rst       -> Ok(y :: x :: rst)
  | _ :: [] | [] as stk -> Error(InvalidArity(Swap, List.length stk))

(* Negate top value on stack *)
let neg : state -> (state, eval_err) result =
  with_stack @@
  function
  | VInt(x) :: rst -> Ok(VInt(-1 * x) :: rst)
  | []             -> Error(InvalidArity(Neg, 0))
  | x :: _         -> Error(WrongType(Neg, [x]))

(* Concatenate top two values on stack *)
let concat : state -> (state, eval_err) result =
  with_stack @@
  function
  | VString(x) :: VString(y) :: rst -> Ok(VString(x ^ y) :: rst)
  | _ :: [] | [] as stk             -> Error(InvalidArity(Concat, List.length stk))
  | x :: y :: _                     -> Error(WrongType(Concat, [x; y]))

(* Boolean AND top two values on stack; 0-false and 1-true *)
let and_ : state -> (state, eval_err) result =
  with_stack @@
  function
  | VInt(x) :: VInt(y) :: rst when is_bool x && is_bool y
    -> Ok(VInt(int_of_bool (x = y)) :: rst)
  | _ :: [] | [] as stk -> Error(InvalidArity(And, List.length stk))
  | x :: y :: _         -> Error(WrongType(And, [x; y]))

(* Boolean OR top two values on stack; 0-false and 1-true *)
let or_ : state -> (state, eval_err) result =
  with_stack @@
  function
  | VInt(x) :: VInt(y) :: rst when is_bool x && is_bool y
    -> Ok(VInt(int_of_bool (x = 1 || y = 1)) :: rst)
  | _ :: [] | [] as stk -> Error(InvalidArity(Or, List.length stk))
  | x :: y :: _         -> Error(WrongType(Or, [x; y]))

(* Boolean NOT top value on stack; 0-false and 1-true *)
let not_ : state -> (state, eval_err) result =
  with_stack @@
  function
  | VInt(x) :: rst when is_bool x
    -> Ok(VInt(abs(x - 1)) :: rst)
  | []     -> Error(InvalidArity(Not, 0))
  | x :: _ -> Error(WrongType(Not, [x]))

(* Equal evalutation on top two values on stack *)
let equal : state -> (state, eval_err) result =
  with_stack @@
  function
  | VInt(x) :: VInt(y) :: rst -> Ok(VInt(int_of_bool (x = y)) :: rst)
  | _ :: [] | [] as stk       -> Error(InvalidArity(Equal, List.length stk))
  | x :: y :: _               -> Error(WrongType(Equal, [x; y]))

(* Less than or equal evalutation on top two values on stack *)
let lte : state -> (state, eval_err) result =
  with_stack @@
  function
  | VInt(x) :: VInt(y) :: rst -> Ok(VInt(int_of_bool (x <= y)) :: rst)
  | _ :: [] | [] as stk       -> Error(InvalidArity(Lte, List.length stk))
  | x :: y :: _               -> Error(WrongType(Lte, [x; y]))

(* Store top value on stack into local environment *)
let local (s, l, loc, glob, func : state) (x : var) : (state, eval_err) result =
  match s with
  | v::rst -> Ok((rst, l, add_bind x v loc, glob, func))
  | []     -> Error(InvalidArity(Local(x), 0))

(* Store top value on stack into global environment *)
let global (s, l, loc, glob, func : state) (x : var) : (state, eval_err) result =
  match s with
  | v::rst -> Ok((rst, l, loc, add_bind x v glob, func))
  | []     -> Error(InvalidArity(Global(x), 0)) 
                
(* Encapsulate top value on stack with Left() *)
let inject_left : state -> (state, eval_err) result =
  with_stack @@
  function
  | [] -> Error(InvalidArity(InjL, 0))
  | x::rst -> Ok(Left(x) :: rst)
                
(* Encapsulate top value on stack with Right() *)
let inject_right : state -> (state, eval_err) result = 
  with_stack @@
  function
  | [] -> Error(InvalidArity(InjR, 0))
  | x::rst -> Ok(Right(x) :: rst)
                
(* Create tuple on stack with x top values on the stack *)
let tuple (stk, log, loc, glob, func : state) (x : const) : (state, eval_err) result = 
  match x with
  | Name(v) -> Error(WrongType(Tuple(x), []))
  | String(s) -> Error(WrongType(Tuple(x), []))
  | Int(x) -> (
      let get_tuple n stack = 
        let rec go n stack acc = 
          if n > 0 then
            match stack with 
            | [] -> None
            | hd::tl -> go (n - 1) tl (hd::acc)
          else
            Some((acc, stack))
        in
        go n stack [] in
      match get_tuple x stk with
      | None -> Error(InvalidArity(Tuple(Int(x)), x))
      | Some(x, y) -> Ok(Tuple(x)::y, log, loc, glob, func)
    ) 
    
(* Get value at index x from tuple on the stack *)
let get (stk, log, loc, glob, func : state) (x : const) : (state, eval_err) result = 
  match stk with
  | [] -> Error(InvalidArity(Get(x), 1))
  | hd::tl -> 
      match hd with
      | Tuple(v) -> (
          let get_from_arr n arr = 
            let rec go count arr = 
              match arr with
              | [] -> None
              | hd::tl -> 
                  if count = n then
                    Some(hd)
                  else
                    go (count + 1) tl
            in
            go 0 arr in
          match x with
          | Int(y) -> (
              match get_from_arr y v with
              | None -> Error(InvalidArity(Tuple(x), 1))
              | Some(output) -> Ok(output::stk, log, loc, glob, func)
            )
          | _ -> Error(WrongType(Get(x), []))
        )
      | _ -> Error(WrongType(Get(x), []))
      
(* Length of array function *)
let get_len arr = 
  let rec go array acc = 
    match array with
    | [] -> acc
    | hd::tl -> go tl (acc + 1)
  in go arr 0
  
(* Evaluate and pushing function into closure, with snapshot of local environment and mutual functions, onto the environment *)
let eval_fun (s, l, loc, glob, func : state) (fun_name) (fun_arg) (fun_body) : (state, eval_err) result = 
  let get_fun_body function_body = 
    let rec go func_body acc1 acc2 = 
      match func_body with
      | [] -> (acc1, acc2)
      | hd::tl -> 
          match hd with
          | Mut(x, y, z) -> go tl (hd::acc1) acc2
          | _ -> go tl acc1 (acc2@[hd])
    in go function_body [] [] in
  let func_body = 
    match get_fun_body fun_body with
    | x, y -> y
  in
  let mut_functions = 
    match get_fun_body fun_body with
    | x, y -> x
  in
  let function_env = loc in
  let function_func = (fun_name, fun_arg, func_body) in 
  let get_mut_bodies mut_functions_list = 
    let rec go mut_funcs acc = 
      match mut_funcs with
      | [] -> acc
      | Mut(mut_name, mut_args, mut_body)::tl -> go tl (acc@[(mut_name, mut_args, mut_body)])
      | _ -> acc
    in go mut_functions_list [] in 
  let function_func_list = (get_mut_bodies mut_functions) @ [function_func] in
  let new_func_env = 
    let first_clo = Clo(function_env, function_func, function_func_list) in
    let make_new_closures = 
      let rec go mut_functs acc = 
        match mut_functs with
        | [] -> acc
        | hd::tl -> go tl (acc @ [Clo(function_env, hd, function_func_list)])
      in go (get_mut_bodies mut_functions) [] in
    let closure_list = (make_new_closures) @ [first_clo] in 
    let rec bind_closures clo_list acc_env =
      match clo_list with
      | [] -> acc_env
      | hd::tl -> 
          match hd with
          | Clo(a, b, c) -> 
              (match b with
               | (x, y, z) -> (bind_closures tl (add_bind (x) (hd) acc_env)))
          | _ -> acc_env
    in bind_closures closure_list func in
  Ok((s, l, loc, glob, new_func_env))

(* Return call at at end of function *)
let return (stk, log, loc, glob, func : state) : (bool * state, eval_err) result = 
  match stk with
  | hd::tl -> Ok(false, (stk, log, loc, glob, func))
  | [] -> Error(InvalidArity(Return, 0))

(* Creating new evaluating block with new stack and new local environment *)
let rec begin_end (s, l, loc, glob, func : state) (blk : prog): (bool * state, eval_err) result =
  eval blk ([], l, loc, glob, func) |> and_then @@ fun (quitting, (s', l, _, glob, func)) ->
  match s' with
  | v::rst -> Ok((quitting, (v::s, l, loc, glob, func)))
  | []     -> Error(NoValue(BeginEnd(blk)))

(* If then, else logic blocks handling and evaluation *)
and ifthen_else (s, l, loc, glob, func : state) (then_blk : prog) (else_blk : prog): (bool * state, eval_err) result =
  match s with
  | VInt(v)::rst when v = 1
    -> eval then_blk (rst, l, loc, glob, func)
  | VInt(v)::rst when v = 0
    -> eval else_blk (rst, l, loc, glob, func)
  | []     -> Error(InvalidArity(IfThenElse(then_blk, else_blk), 0))
  | x::rst -> Error(WrongType(IfThenElse(then_blk, else_blk), [x]))
       
(* Unwrapping top values of stack with Left and Right encapsulation *)
and caseleft_right (s, l, loc, glob, func : state) (left_blk : prog) (right_blk : prog): (bool * state, eval_err) result = 
  match s with
  | Left(x)  :: rst -> eval left_blk (x::rst, l, loc, glob, func)
  | Right(x) :: rst -> eval right_blk (x::rst, l, loc, glob, func)
  | [] -> Error(InvalidArity(CaseLeftRight(left_blk, right_blk), 0))
  | x::rst -> Error(WrongType(CaseLeftRight(left_blk, right_blk), [x])) 

(* Calling and evaluating functions *)
and call (s, l, loc, glob, func : state): (bool * state, eval_err) result =
  match s with
  | Clo(fun_local, fun_details, fun_functions)::arg_value::rst -> 
      (let make_closures = 
         let rec go function_functions acc = 
           match function_functions with
           | [] -> acc
           | hd::tl -> go tl (acc@[Clo(fun_local, hd, fun_functions)])
         in go fun_functions []
       in
       let new_environment = 
         let rec go closure_list acc_env = 
           match closure_list with
           | [] -> acc_env
           | hd::tl ->
               match hd with
               | Clo(a, b, c) -> 
                   (match b with
                    | (x, y, z) -> go tl (add_bind x hd acc_env))
               | _ -> acc_env
         in go make_closures []
       in
       match fun_details with
       | (x, y, z) -> 
           match z with
           | [] -> Error(NoValue(Call))
           | _ -> eval z ([], l, add_bind y arg_value fun_local, glob, new_environment) |> and_then @@ fun (quitting, (s', l, _, glob, func)) -> 
               match s' with
               | v::rest -> Ok((quitting, (v::rst, l, loc, glob, func)))
               | []     -> Error(NoValue(Call)))
  | _ -> Error(InvalidArity(Call, 2))
        
(* Main evaluating function *)
and eval (prog : prog) (st : state) : (bool * state, eval_err) result =
    match prog with
    | []                -> Ok(false, st)
    | Quit      :: _    -> Ok(true, quit st)
    | Push(c)   :: prog -> push   st c |> and_then (eval prog)
    | Pop       :: prog -> pop    st   |> and_then (eval prog)
    | Add       :: prog -> add    st   |> and_then (eval prog)
    | Sub       :: prog -> sub    st   |> and_then (eval prog)
    | Mul       :: prog -> mul    st   |> and_then (eval prog)
    | Div       :: prog -> div    st   |> and_then (eval prog)
    | Swap      :: prog -> swap   st   |> and_then (eval prog)
    | Neg       :: prog -> neg    st   |> and_then (eval prog)
    | And       :: prog -> and_   st   |> and_then (eval prog)
    | Or        :: prog -> or_    st   |> and_then (eval prog)
    | Not       :: prog -> not_   st   |> and_then (eval prog)
    | Lte       :: prog -> lte    st   |> and_then (eval prog)
    | Concat    :: prog -> concat st   |> and_then (eval prog)
    | Equal     :: prog -> equal  st   |> and_then (eval prog)
    | Local(x)  :: prog -> local  st x |> and_then (eval prog)
    | Global(x) :: prog -> global st x |> and_then (eval prog) 
    | BeginEnd(p)      :: prog -> begin_end st p
                                  |> and_then @@ fun (quitting, st) ->
        if not quitting then eval prog st else Ok(quitting, st)
    | IfThenElse(t, e) :: prog -> ifthen_else st t e
                                  |> and_then @@ fun (quitting, st) ->
        if not quitting then eval prog st else Ok(quitting, st)
    | InjL      :: prog -> inject_left   st   |> and_then (eval prog)
    | InjR      :: prog -> inject_right  st   |> and_then (eval prog)
    | CaseLeftRight(l, r)   :: prog -> caseleft_right st l r
                                       |> and_then @@ fun (quitting, st) ->
        if not quitting then eval prog st else Ok(quitting, st)
    | Tuple(x)  :: prog -> tuple st x |> and_then (eval prog)
    | Get(x)    :: prog -> get st x |> and_then (eval prog)
    | Fun(x, y, z)    :: prog -> eval_fun st x y z |> and_then (eval prog)
    | Mut(x, y, z)    :: prog -> Ok(false, st)
    | Call      ::      prog  -> call st
                                 |> and_then @@ fun (quitting, st) ->
        if not quitting then eval prog st else Ok(quitting, st)
    | Return    ::       prog -> return st
      

(*------------------------------------*)
(* Debugging Helper Function: Print out array contents; Called in: write_file_with_log *) 
let get_string_arr arr = 
  List.fold_left (fun acc x -> 
      match x with
      | a -> String.cat acc (String.cat a "\n")
    ) "" arr;;
(*------------------------------------*)

let write_file_with_log (file_path: string) (log: log) : unit =
  let fp = open_out file_path in
  let _ =
    List.fold_left (
      fun items_left elem ->
        match items_left with
        | 1 -> Printf.fprintf fp "%s" elem; items_left - 1
        | _ -> Printf.fprintf fp "%s\n" elem; items_left - 1
    ) (List.length log) log
  in close_out fp

type interp_err =
  | LexerErr of lexer_err
  | ParseErr of parse_err
  | EvalErr  of eval_err

let lexer_err e = LexerErr(e)
let parse_err e = ParseErr(e)
let eval_err  e = EvalErr(e)

let string_of_interp_err e =
  match e with
  | LexerErr(e) -> string_of_lexer_err e
  | ParseErr(e) -> string_of_parse_err e
  | EvalErr(e)  -> string_of_eval_err  e

let interpreter (src : string) (output_file_path: string): unit =
  let run src =
    tokenize_source src        |> Result.map_error lexer_err |> and_then @@ fun tokens ->
    parse_program tokens       |> Result.map_error parse_err |> and_then @@ fun prog ->
    eval prog ([], [], [], [], []) |> Result.map_error eval_err
  in
  (match run src with
   | Ok(_, (_, log, _, _, _)) -> log
   | Error(e)      -> print_endline (string_of_interp_err e); ["\"Error\""])
  |> write_file_with_log output_file_path
  
let parse_test_interpreter (src : string) (output_file_path: string) =
  let run src =
    tokenize_source src        |> Result.map_error lexer_err |> and_then @@ fun tokens ->
    parse_program tokens       |> Result.map_error parse_err
  in
  run src;;

let token_test_interpreter (src : string) (output_file_path: string) =
  let run src =
    tokenize_source src        |> Result.map_error lexer_err
  in
  run src;; 


(* EXAMPLE TEST CASES:
// Test Functions
let test_string_1 = "Fun foo my_arg\nPush 1\nPush 2\n Add\nEnd\nPush foo\nQuit";;
let test_string_2 = "Fun foo my_arg\nPush 1\nPush 2\n Add\nMut bar my_arg2\nPush 1\nMut bar my_arg2\nPush 1\nEnd\nPush foo\nQuit";;
let test_string_3 = "Push 2\nFun foo my_arg\nPush 1\nEnd\nPush foo\nCall\nQuit";;
let test_string_4 = "Fun foo my_arg\nPush 1\nPush 2\n Add\nMut bar my_arg2\nPush 1\nMut car my_arg2\nPush 1\nMut jar my_arg2\nPush 1\nEnd\nPush foo\nPush bar\nPush car\nPush jar\nQuit";;
let output_1 = parse_test_interpreter test_string2 "output.txt"
let output_2 = token_test_test_interpreter test_string2 "output.txt"

// Final Testing
let final_test = "Push 1\nGlobal x\nFun x p\nPush 2\nGlobal x\nEnd\nPush x\nQuit";;
interpreter final_test "output.txt";;*)