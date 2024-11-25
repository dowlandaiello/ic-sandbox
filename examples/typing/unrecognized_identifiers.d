type atom

# This references a type that does not exist.
# The compiler will tell you.
symbol xyz: nat+

# This redex also references symbols that don't exist
# the compiler will also tell you
bruh(alsounrecognized(), skibidi()) >< bruh()
