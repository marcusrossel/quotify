import Quotify.Command

set_option pp.explicit true

/-- info: [0] @List.Perm Nat -/
#guard_msgs in
#quotify_norm @List.Perm Nat

/-- info: [0] @List.Perm Nat -/
#guard_msgs in
#quotify_norm ((· ≈ ·) : List Nat → List Nat → Prop)

/-- info: [1] fun x_0 => @List.Perm x_0 -/
#guard_msgs in
#quotify_norm List.Perm

/-- info: [1] fun x_0 => @List.Perm x_0 -/
#guard_msgs in
#quotify_norm (List.isSetoid _).r

/-- info: [1] fun α => @List.Perm α -/
#guard_msgs in
#quotify_norm ((· ≈ ·) : List ?α → List ?α → Prop)

/-- info: [1] fun x_0 l₁ l₂ => ∀ (x : x_0), Iff (@List.Mem x_0 x l₁) (@List.Mem x_0 x l₂) -/
#guard_msgs in
#quotify_norm fun α (l₁ l₂ : List α) => ∀ x, x ∈ l₁ ↔ x ∈ l₂

/-- info: [1] fun x_0 => @Eq x_0 -/
#guard_msgs in
#quotify_norm (· = ·)

opaque MyEquiv₁ : Bool → Bool → Prop

/-- info: [0] MyEquiv₁ -/
#guard_msgs in
#quotify_norm MyEquiv₁

def MyEquiv₂ (b₁ b₂ : Bool) : Prop :=
  b₁ = b₂

/-- info: [0] MyEquiv₂ -/
#guard_msgs in
#quotify_norm MyEquiv₂

abbrev MyEquiv₃ (b₁ b₂ : Bool) : Prop :=
  b₁ = b₂

/-- info: [0] @Eq Bool -/
#guard_msgs in
#quotify_norm MyEquiv₃
