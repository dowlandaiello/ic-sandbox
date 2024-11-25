# These are duplicate types, the compiler
# will pick up on this and error out
type atom
type atom

# These are also duplicate symbols
symbol xyz: atom+
symbol xyz: atom+