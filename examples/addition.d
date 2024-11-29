type nat

symbol Z: nat+
symbol S: nat+, nat-
symbol Add: nat-, nat-, nat+

Z() >< Add(x, x)
S(Add(y, t)) >< Add(y, S(t))
Z() >< Add(S(Z()), x)