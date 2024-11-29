type nat

symbol Z: nat+
symbol S: nat+, nat-
symbol Add: nat-, nat-, nat+

Z() >< Add(y, y)
S(Add(y, t)) >< Add(y, S(t))
S(Add(Z(), Z())) >< Add(Z(), S(Z()))
