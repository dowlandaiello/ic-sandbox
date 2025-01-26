type nat
symbol Z: nat+
symbol S: nat+, nat-
symbol Add: nat-, nat-, nat+

Add(x, x) >< Z()
Add(Z(), x) >< Z()
