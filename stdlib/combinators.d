# By Dowland Aiello <3

type a

# Polarized versions of combinators
symbol ConstrPos: a+, a-, a-
symbol ConstrNeg: a-, a+, a+

symbol DupPos: a+, a-, a-
symbol DupNeg: a-, a+, a+

symbol EraPos: a+, ()
symbol EraNeg: a-, ()

# Commutation
ConstrPos(ConstrNeg(a, b), ConstrNeg(c, d)) >< DupNeg(DupPos(a, c), DupPos(b, d))
EraPos >< ConstrNeg(EraPos, EraPos)
EraPos >< DupNeg(EraPos, EraPos)

ConstrNeg(ConstrPos(a, b), ConstrPos(c, d)) >< DupPos(DupNeg(a, c), DupNeg(b, d))
EraNeg >< ConstrPos(EraNeg, EraNeg)
EraNeg >< DupPos(EraNeg, EraNeg)

# Annihilation
ConstrPos(a, b) >< ConstrNeg(a, b)
DupPos(a, b) >< DupNeg(b, a)
EraPos >< EraNeg