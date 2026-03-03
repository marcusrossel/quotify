module
public import Lean.Elab.Command

namespace Lean.Expr

public inductive GetSetoidNameResult where
  | success (n : Name)
  | illformedSetoid (setoid : Expr)
  | notReducibleToSetoid (e : Expr)

/--
Assuming the given `expr` can be reduced to an expression of the form `@Setoid.r _ inst _ _`, and
`inst` is an application with a global constant `s` as head symbol, this function returns the name
of `s`.
-/
public partial def getSetoidName? (expr : Expr) : MetaM GetSetoidNameResult := do
  match_expr expr with
  | Setoid.r _ setoid _ _ =>
    let some setoidName := setoid.getAppFn'.constName? | return .illformedSetoid setoid
    return .success setoidName
  | _ =>
    let some unfolded ← Meta.unfoldProjInst? expr | return .notReducibleToSetoid expr
    unfolded.getSetoidName?
