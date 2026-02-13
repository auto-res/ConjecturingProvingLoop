

theorem P1_prod_empty_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} : P1 ((∅ : Set X) ×ˢ B) := by
  intro x hx
  rcases hx with ⟨hFalse, _⟩
  cases hFalse

theorem P2_prod_empty_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : P2 (A ×ˢ (∅ : Set Y)) := by
  intro x hx
  rcases hx with ⟨_, hFalse⟩
  cases hFalse