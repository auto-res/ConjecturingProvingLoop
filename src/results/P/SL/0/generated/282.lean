

theorem closure_eq_univ_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    closure (A : Set X) = (Set.univ : Set X) := by
  -- First, `closure A ⊆ univ` holds trivially.
  have h₁ : closure (A : Set X) ⊆ (Set.univ : Set X) := by
    intro x _
    trivial
  -- Second, `univ ⊆ closure A` follows from the density hypothesis.
  have h₂ : (Set.univ : Set X) ⊆ closure (A : Set X) := by
    have hMono : closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
      closure_mono (interior_subset : interior (A : Set X) ⊆ A)
    simpa [hDense] using hMono
  exact Set.Subset.antisymm h₁ h₂