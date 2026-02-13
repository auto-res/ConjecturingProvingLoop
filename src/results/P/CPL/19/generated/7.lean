

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} : interior A = (Set.univ : Set X) → P2 A := by
  intro hInt_eq
  intro x hx
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [hInt_eq, closure_univ, interior_univ] using this

theorem P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} : interior A = (Set.univ : Set X) → P3 A := by
  intro hInt_eq
  intro x hx
  -- Since `interior A = univ`, every point lies in `interior A`.
  have hx_intA : x ∈ interior A := by
    simpa [hInt_eq] using (by
      simp : x ∈ (Set.univ : Set X))
  -- `interior A` is contained in `interior (closure A)`.
  have hsubset : interior A ⊆ interior (closure A) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  exact hsubset hx_intA