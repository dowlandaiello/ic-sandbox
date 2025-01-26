type nat

symbol Add: nat-, nat-, nat+
symbol Z: nat+
symbol S: nat+, nat-

Z() >< Add(x, x)
S(Add(s, t)) >< Add(s, S(t))

# Simple substitution
Z() >< Add(Z(), x)

# Harder substitution
S(Add(Z(), S(Z()))) >< Add(s, S(t))