type nat

symbol Z: nat+
symbol S: nat+, nat-

Z >< Add(y, y)
S(Add(y, t)) >< Add(y, S(t))
