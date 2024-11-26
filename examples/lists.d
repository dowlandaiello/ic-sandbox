type atom, list

symbol P: atom+
symbol O: atom+
symbol L: atom+
symbol Cons: list+, atom-, list-
symbol Nil: list+
symbol Append: list-, list-, list+

Cons(x, Append(v, t)) >< Append(v, Cons(x, t))
Nil() >< Append(v, v)
Nil() >< Append(P(), P()4)