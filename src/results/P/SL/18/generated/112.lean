

theorem dense_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) → Dense (A : Set X) := by
  intro hDenseInt x
  have hx : (x : X) ∈ closure (interior (A : Set X)) := hDenseInt x
  have hIncl : closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
    closure_mono (interior_subset : interior (A : Set X) ⊆ A)
  exact hIncl hx