section by_exactI_hack

open tactic expr
open lean
open lean.parser
open interactive
open tactic

reserve prefix `​ `:100

@[user_notation]
meta def exact_notation (_ : parse $ tk "​") (e : parse (lean.parser.pexpr 0)) : parser pexpr := do
expr.macro d [_] ← pure ``(by skip),
pure $ expr.macro d [const `tactic.interactive.exactI [] (cast undefined e.reflect)]

end by_exactI_hack
