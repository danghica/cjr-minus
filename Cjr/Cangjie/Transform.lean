import Cjr.Syntax
namespace Cjr.Cangjie

/- Restore placeholder pointers to source parameters. As upstream, values other
than pointer literals (including closures and aggregate values) are left intact. -/
mutual
def renamePtr (l : Loc) (x : String) : Expr → Expr
  | .val (.lit (.ptr n)) => if n == l then .var x else .val (.lit (.ptr n))
  | .val v => .val v
  | .var y => .var y
  | .recE f y e => .recE f y (renamePtr l x e)
  | .app a b => .app (renamePtr l x a) (renamePtr l x b)
  | .letE b a e => .letE b (renamePtr l x a) (renamePtr l x e)
  | .varBind y a e => .varBind y (renamePtr l x a) (renamePtr l x e)
  | .assign y e => .assign y (renamePtr l x e)
  | .pop slot e => .pop slot (renamePtr l x e)
  | .stackLoad e => .stackLoad (renamePtr l x e)
  | .stackAssign a b => .stackAssign (renamePtr l x a) (renamePtr l x b)
  | .stackFieldStore a i b => .stackFieldStore (renamePtr l x a) i (renamePtr l x b)
  | .ifE a b c => .ifE (renamePtr l x a) (renamePtr l x b) (renamePtr l x c)
  | .whileE a b => .whileE (renamePtr l x a) (renamePtr l x b)
  | .seq a b => .seq (renamePtr l x a) (renamePtr l x b)
  | .binOp op a b => .binOp op (renamePtr l x a) (renamePtr l x b)
  | .alloc e => .alloc (renamePtr l x e)
  | .free e => .free (renamePtr l x e)
  | .load e => .load (renamePtr l x e)
  | .store a b => .store (renamePtr l x a) (renamePtr l x b)
  | .offset a b => .offset (renamePtr l x a) (renamePtr l x b)
  | .struct vs es => .struct vs (renamePtrs l x es)
  | .structLoad e i => .structLoad (renamePtr l x e) i
  | .structStore y i e => .structStore y i (renamePtr l x e)
  | .new vs es => .new vs (renamePtrs l x es)
  | .fieldLoad e i => .fieldLoad (renamePtr l x e) i
  | .fieldStore a i b => .fieldStore (renamePtr l x a) i (renamePtr l x b)
termination_by structural e => e

def renamePtrs (l : Loc) (x : String) : List Expr → List Expr
  | [] => []
  | e :: es => renamePtr l x e :: renamePtrs l x es
termination_by structural es => es
end
end Cjr.Cangjie
