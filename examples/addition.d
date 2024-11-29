type nat

symbol Z: nat+
symbol S: nat+, nat-
symbol Add: nat-, nat-, nat+

Z() >< Add(x, x)
Z() >< Add(Z(), Z())