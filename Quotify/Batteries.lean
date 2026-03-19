module
public import Std.Data.HashMap

-- **TODO** This needs to be namespaced in `Quotify`, as otherwise it will lead to colliding
--          definitions if this package is used in a project that also uses Batteries.

namespace Std.HashMap

variable [BEq α] [Hashable α]

@[inline]
public def mergeWith (f : α → β → β → β) (self other : HashMap α β) : HashMap α β :=
  other.fold (init := self) fun map k v₂ =>
    match map[k]? with
    | none => map.insert k v₂
    | some v₁ => map.insert k <| f k v₁ v₂
