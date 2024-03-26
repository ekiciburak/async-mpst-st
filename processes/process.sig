  process : Type
  lpart : Type
  llabel : Type
  expr : Type
  list : Functor
  prod: Functor

  psend     : process
  pssend    : lpart -> "prod" ("prod" (llabel, expr), process) -> process
  psreceive : lpart -> "list" ("prod" ("prod" (llabel, expr), process)) -> process
  psite     : expr -> process -> process -> process
  psmu      : (process -> process) -> process
