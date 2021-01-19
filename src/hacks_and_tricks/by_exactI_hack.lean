-- brilliant hack by Gabriel Ebner
-- thanks!!

-- files that import this file can use the zero-width space char
-- to reset the TC instance cache, and avoid `by exactI` kludges

open tactic expr
open lean
open lean.parser
open interactive
open tactic

reserve prefix `​ `:100 -- zero-width space Unicode char

@[user_notation]
meta def exact_notation (_ : parse $ tk "​") (e : parse (lean.parser.pexpr 0)) : parser pexpr := do
expr.macro d [_] ← pure ``(by skip),
pure $ expr.macro d [const `tactic.interactive.exactI [] (cast undefined e.reflect)]
