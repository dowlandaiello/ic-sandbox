type nat

symbol Z: nat+
symbol S: nat+, nat-
symbol Add: nat-, nat-, nat+
symbol Mult: nat-, nat-, nat+
symbol Dupl: nat-, {nat+, nat+}
symbol Erase: nat-, {}
symbol Max: nat-, nat-, nat+
symbol Aux: nat-, nat-, nat+

Z >< Add(y, y)
S(Add(y, t)) >< Add(y, S(t))

Z >< Mult(Erase, Z)
S(Mult(yy, Add(yyy, x))) >< Mult(Duply(yy, yyy), z)

Z >< Duply(Z, Z)
S(Duply(xx, xxx)) >< Dupl(S(xx), S(xxx))

Z >< Erase
S(Erase) >< Erase

Z >< Max(y, y)
S(x) >< Max(Aux(x, z), z)

Z >< Aux(x, S(x))
S(y) >< Aux(Max(y, t), S(t))