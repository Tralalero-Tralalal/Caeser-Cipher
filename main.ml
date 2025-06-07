open Datatypes
open PeanoNat
open List
open Encrypt

 let rec nat_to_int (n : nat) : int =
    match n with
    | O -> 0
    | S n' -> 1 + (nat_to_int n')

let rec int_to_nat (i : int) : nat =
    if i <= 0 then O
    else S (int_to_nat (i - 1))

let turn_to_char (num : nat) : char =
  let int_num = nat_to_int num in
  if int_num < 0 || int_num > 26 then (* 0 is < 1, so this branch is taken *)
    '\000' (* Returns null character *)
  else if int_num = 0 then 
    'z' else
    Char.chr (96 + int_num)

let turn_to_num (c : char) =
  match c with
  | 'a' -> (S O) (* 1 *)
  | 'b' -> S(S O) (* 2 *)
  | 'c' -> S(S(S O)) (* 3 *)
  | 'd' -> S(S(S(S O))) (* 4 *)
  | 'e' -> S(S(S(S(S O)))) (* 5 *)
  | 'f' -> S(S(S(S(S(S O))))) (* 6 *)
  | 'g' -> S(S(S(S(S(S(S O)))))) (* 7 *)
  | 'h' -> S(S(S(S(S(S(S(S O))))))) (* 8 *)
  | 'i' -> S(S(S(S(S(S(S(S(S O)))))))) (* 9 *)
  | 'j' -> S(S(S(S(S(S(S(S(S(S O))))))))) (* 10 *)
  | 'k' -> S(S(S(S(S(S(S(S(S(S(S O)))))))))) (* 11 *)
  | 'l' -> S(S(S(S(S(S(S(S(S(S(S(S O))))))))))) (* 12 *)
  | 'm' -> S(S(S(S(S(S(S(S(S(S(S(S(S O)))))))))))) (* 13 *)
  | 'n' -> S(S(S(S(S(S(S(S(S(S(S(S(S(S O))))))))))))) (* 14 *)
  | 'o' -> S(S(S(S(S(S(S(S(S(S(S(S(S(S(S O)))))))))))))) (* 15 *)
  | 'p' -> S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S O))))))))))))))) (* 16 *)
  | 'q' -> S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S O)))))))))))))))) (* 17 *)
  | 'r' -> S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S O))))))))))))))))) (* 18 *)
  | 's' -> S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S O)))))))))))))))))) (* 19 *)
  | 't' -> S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S O))))))))))))))))))) (* 20 *)
  | 'u' -> S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S O)))))))))))))))))))) (* 21 *)
  | 'v' -> S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S O))))))))))))))))))))) (* 22 *)
  | 'w' -> S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S O)))))))))))))))))))))) (* 23 *)
  | 'x' -> S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S O))))))))))))))))))))))) (* 24 *)
  | 'y' -> S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S O)))))))))))))))))))))))) (* 25 *)
  | 'z' -> S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S O))))))))))))))))))))))))) (* 26 *)
  | _   -> O (* Default for any other character (represents 0) *)

(* char_list_to_string : char list -> string *)
let char_list_to_string (cl : char list) : string =
  String.of_seq (List.to_seq cl)

let int_list_to_string (l : int list) : string =
  let string_elements = List.map string_of_int l in (* Convert each int to its string representation *)
  let inner_string = String.concat "; " string_elements in (* Join them with a semicolon and space *)
  "[" ^ inner_string ^ "]" (* Enclose in square brackets *)

let cipher (s : char list) (shift_amount : nat) : char list =
  let nums = List.map turn_to_num s in
  let encrypted_nums = List.map (Encrypt.encrypt shift_amount) nums in
  let encrypted_chars = List.map turn_to_char encrypted_nums in
  encrypted_chars
;;

let string_to_char_list s =
  let len = String.length s in
  let rec aux i acc =
    if i < 0 then acc
    else aux (i - 1) (s.[i] :: acc)
  in
  aux (len - 1) []

let char_list_to_string cl =
  String.of_seq (List.to_seq cl)

let () =
  let args = Sys.argv in
  if Array.length args < 3 then begin
    Printf.printf "Usage: %s <text_to_cipher> <shift_amount>\n" args.(0);
    exit 1
  end;

  let input_string = args.(1) in
  let shift_str = args.(2) in

  (* Convert shift_str to int, then to Datatypes.nat *)
  let shift_int =
    try int_of_string shift_str
    with Failure _ ->
      Printf.printf "Error: Invalid shift amount '%s'. Please provide an integer.\n" shift_str;
      exit 1
  in
  let shift_amount_nat = int_to_nat shift_int in

  let input_char_list = string_to_char_list input_string in

  (* Pass both arguments to cipher *)
  let output_char_list = cipher input_char_list shift_amount_nat in
  let output_string = char_list_to_string output_char_list in

  Printf.printf "Original Text: %s\n" input_string;
  Printf.printf "Shift Amount: %d\n" shift_int;
  Printf.printf "Ciphered Text: %s\n" output_string
;;
