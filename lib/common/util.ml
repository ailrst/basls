let compose f g x = f (g x)
let get_or_else x default = match x with Some x -> x | None -> default ()
let or_else default x = match x with Some x -> x | None -> default ()
