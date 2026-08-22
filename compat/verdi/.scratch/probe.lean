example (a b : Nat) (h : Nat.blt a b = true) : a < b := by simp at h; exact h
example (a b : Nat) (h : Nat.ble a b = true) : a ≤ b := by simp at h; exact h
example (a b : Nat) (h : (a == b) = true) : a = b := by simp at h; exact h
example (a b : Nat) (h : Nat.blt a b = false) : b ≤ a := by simp at h; exact h
example (a b : Nat) (h : ¬ (Nat.blt a b = true)) : b ≤ a := by simp at h; exact h
example (p q : Prop) [Decidable p] (h : decide p = true) : p := by simp at h; exact h
