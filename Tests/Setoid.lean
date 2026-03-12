import Quotify.Command

@[quotify]
def s₁ : Setoid (List α) where
  r := List.Perm
  iseqv := sorry

/--
error: There already exists a `Setoid` marked with `[quotify]` for the relation ⏎
  fun x_0 => List.Perm
-/
#guard_msgs(error) in
@[quotify]
def s₂ : Setoid (List α) where
  r := List.Perm
  iseqv := sorry

-- The relation here is `fun x_0 => @Setoid.r (List x_0) (@s₁ x_0)`.
@[quotify]
def s₃ : Setoid (List α) where
  r := s₁.r
  iseqv := sorry

-- TODO: Shouldn't the relation reduce to the same as `s₃`? Note, I think we can afford to use
--       normalized relations only as the fast path, but check for definitional equality as well.
-- The relation here is `fun x_0 => @Setoid.r (List x_0) ((@fun {α} => (@fun {α} => @s₁ α) α) x_0)`.
@[quotify]
def s₄ : Setoid (List α) := s₁

/--
error: There already exists a `Setoid` marked with `[quotify]` for the relation ⏎
  fun x_0 => List.Perm
-/
#guard_msgs in
attribute [instance] s₁ in
@[quotify]
def s₅ : Setoid (List α) := s₁
