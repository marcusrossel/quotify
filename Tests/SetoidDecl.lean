import Quotify.Command

set_option pp.explicit true

@[quotify]
def s₁ : Setoid (List α) where
  r := List.Perm
  iseqv := sorry


/--
error: The relation ⏎
  fun x_0 => @List.Perm x_0
is already covered by the `Setoid` `s₁` marked with `[quotify]`.
-/
#guard_msgs(error) in
@[quotify]
def s₂ : Setoid (List α) where
  r := List.Perm
  iseqv := sorry

/--
error: The relation ⏎
  @List.Perm Nat
is already covered by the `Setoid` `s₁` marked with `[quotify]`.
-/
#guard_msgs(error) in
@[quotify]
def s₃ : Setoid (List Nat) where
  r := List.Perm
  iseqv := sorry

/--
error: The relation ⏎
  fun x_0 => @Setoid.r (List x_0) (@s₁ x_0)
is already covered by the `Setoid` `s₁` marked with `[quotify]`.
-/
#guard_msgs(error) in
@[quotify]
def s₄ : Setoid (List α) where
  r := s₁.r
  iseqv := sorry

/--
error: The relation ⏎
  fun x_0 => @Setoid.r (List x_0) ((@fun {α} => (@fun {α} => @s₁ α) α) x_0)
is already covered by the `Setoid` `s₁` marked with `[quotify]`.
-/
#guard_msgs(error) in
@[quotify]
def s₅ : Setoid (List α) := s₁

/--
error: The relation ⏎
  fun x_0 => @List.Perm x_0
is already covered by the `Setoid` `s₁` marked with `[quotify]`.
-/
#guard_msgs in
attribute [instance] s₁ in
@[quotify]
def s₆ : Setoid (List α) := s₁
