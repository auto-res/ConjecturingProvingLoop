

theorem Topology.interior_closure_interior_eq_univ_iff
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) = (Set.univ : Set X) ↔
      closure (interior A) = (Set.univ : Set X) := by
  constructor
  · intro hInt
    -- `closure (interior A) ⊆ univ` is obvious.
    have h₁ : closure (interior A) ⊆ (Set.univ : Set X) := by
      intro _ _; simp
    -- `univ ⊆ closure (interior A)` follows from the hypothesis.
    have h₂ : (Set.univ : Set X) ⊆ closure (interior A) := by
      intro x _
      have hxInt : (x : X) ∈ interior (closure (interior A)) := by
        simpa [hInt] using (by simp : (x : X) ∈ (Set.univ : Set X))
      exact (interior_subset : interior (closure (interior A)) ⊆
          closure (interior A)) hxInt
    exact subset_antisymm h₁ h₂
  · intro hCl
    exact
      Topology.interior_closure_interior_eq_univ_of_dense_interior
        (X := X) (A := A) hCl