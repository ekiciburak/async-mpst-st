  local : Type
  lpart : Type
  llabel : Type
  sort : Type
  list : Functor
  prod: Functor

  ltend     : local
  ltsend    : lpart -> "list" ("prod" ("prod" (llabel, sort), local)) -> local
  ltreceive : lpart -> "list" ("prod" ("prod" (llabel, sort), local)) -> local
  ltmu      : (local -> local) -> local
