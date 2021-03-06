module UChar = BatUChar

type char = int

(* FIXME(adl) UChar.lowercase/uppercase removed from recent Batteries. Use Camomile? *)
let lowercase x = 
  try Char.code (Char.lowercase (Char.chr x))
  with _ -> x
let uppercase x =
  try Char.code (Char.lowercase (Char.chr x))
  with _ -> x
let int_of_char x = Z.of_int x
let char_of_int x = Z.to_int x
