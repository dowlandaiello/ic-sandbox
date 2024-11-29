type nat

symbol Z: nat+
symbol S: nat+, nat-
symbol Add: nat-, nat-, nat+

S(Add(Z(), Z())) >< Add(Z(), S(Z()))
