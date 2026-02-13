

theorem interior_inter_subset_left {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior ((A ∩ B) : Set X) ⊆ interior (A : Set X) := by
  intro x hx
  have h :=
    (interior_inter_subset_interiors (A := A) (B := B)) hx
  exact h.1