type nat
symbol Z: nat+
symbol S: nat+, nat-
symbol Add: nat-, nat-, nat+
symbol Dec: nat-, nat+
symbol Era: nat-
symbol Fib: nat-, nat+

Add(x, x) >< Z()
S(Add(y, t)) >< Add(y, S(t))

Z() >< Era()
S(Era()) >< Era()

Dec(Z()) >< Z()
Dec(x) >< S(x)

Fib(Z()) >< Z()
Fib(S(Z())) >< S(Z())
