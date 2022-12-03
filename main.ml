open Parsing;;
open Lexing;;

open Lambda;;
open Parser;;
open Lexer;;
open String;;


let rec read_multi_lines () =
  let line = trim(read_line()) in
    if (contains line ';' && length line > 0) then sub line 0 (index line ';') (* we ignore everything from ';' *)
    else line ^ " " ^ (read_multi_lines ())
;;


let top_level_loop () =
  print_endline "   Lambda calculus Interpreter version 1.0\n";
  let rec loop (vctx, tctx) =
    print_string ">> ";
    flush stdout;
    try
      let c = s token (from_string (read_multi_lines ())) in
      loop (execute (vctx, tctx) c)
    with
       Lexical_error ->
         print_endline "lexical error";
         loop (vctx, tctx)
     | Parse_error ->
         print_endline "syntax error";
         loop (vctx, tctx)
     | Type_error e ->
         print_endline ("type error: " ^ e);
         loop (vctx, tctx)
     | End_of_file ->
         print_endline "\n...closing interpreter\nBye!"
  in
    loop (emptyctx, emptyctx)
  ;;

top_level_loop ()
;;
