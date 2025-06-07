open List
open Encrypt

let turn_to_char (num, is_uppercase) =
  if num < 1 || num > 26 then
    '\000' (* Or raise an exception, or return a 'char option' *)
  else
    if is_uppercase then
      Char.chr (64 + num) (* 'A' is ASCII 65, so 65-1 = 64 *)
    else
      Char.chr (96 + num) (* 'a' is ASCII 97, so 97-1 = 96 *)

let turn_to_num (c : char) =
  match c with
  | 'a' -> (1, false)
  | 'b' -> (2, false)
  | 'c' -> (3, false)
  | 'd' -> (4, false)
  | 'e' -> (5, false)
  | 'f' -> (6, false)
  | 'g' -> (7, false)
  | 'h' -> (8, false)
  | 'i' -> (9, false)
  | 'j' -> (10, false)
  | 'k' -> (11, false)
  | 'l' -> (12, false)
  | 'm' -> (13, false)
  | 'n' -> (14, false)
  | 'o' -> (15, false)
  | 'p' -> (16, false)
  | 'q' -> (17, false)
  | 'r' -> (18, false)
  | 's' -> (19, false)
  | 't' -> (20, false)
  | 'u' -> (21, false)
  | 'v' -> (22, false)
  | 'w' -> (23, false)
  | 'x' -> (24, false)
  | 'y' -> (25, false)
  | 'z' -> (26, false)

  | 'A' -> (1, true)
  | 'B' -> (2, true)
  | 'C' -> (3, true)
  | 'D' -> (4, true)
  | 'E' -> (5, true)
  | 'F' -> (6, true)
  | 'G' -> (7, true)
  | 'H' -> (8, true)
  | 'I' -> (9, true)
  | 'J' -> (10, true)
  | 'K' -> (11, true)
  | 'L' -> (12, true)
  | 'M' -> (13, true)
  | 'N' -> (14, true)
  | 'O' -> (15, true)
  | 'P' -> (16, true)
  | 'Q' -> (17, true)
  | 'R' -> (18, true)
  | 'S' -> (19, true)
  | 'T' -> (20, true)
  | 'U' -> (21, true)
  | 'V' -> (22, true)
  | 'W' -> (23, true)
  | 'X' -> (24, true)
  | 'Y' -> (25, true)
  | 'Z' -> (26, true)

  | _   -> (0, false) (* Default for any other character, or raise an error *)

let cipher (s : char list) =
  let nums = List.map turn_to_num s in
    let encrypted_nums = List.map encrypt nums in
      let encrypted_string = List.map turn_to_char encrypted_nums in
        encrypted_string

let () =
  let arg = Sys.argv in
    print_string arg[0]
