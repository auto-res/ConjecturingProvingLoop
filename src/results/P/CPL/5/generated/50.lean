

theorem P1_closure_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : P1 (closure A) := by
  exact (P1_closure (A := A)) (P1_of_P2 (A := A) hA)

theorem P1_prod_empty {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : P1 (A ×ˢ (∅ : Set Y)) := by
  intro x hx
  rcases hx with ⟨_, hFalse⟩
  cases hFalse

theorem P2_prod_empty {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : P2 (A ×ˢ (∅ : Set Y)) := by
  intro x hx
  rcases hx with ⟨_, hY⟩
  cases hY

theorem P3_prod_empty {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : P3 (A ×ˢ (∅ : Set Y)) := by
  intro x hx
  cases hx.2