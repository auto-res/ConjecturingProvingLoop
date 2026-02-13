

theorem Topology.interior_closure_eq_univ_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) = (Set.univ : Set X) ↔ closure A = (Set.univ : Set X) := by
  constructor
  · intro hInt
    -- `closure A ⊆ univ` is trivial.
    have h₁ : closure A ⊆ (Set.univ : Set X) := by
      intro _ _; simp
    -- Every point of `univ` lies in `closure A` because it lies in `interior (closure A)`.
    have h₂ : (Set.univ : Set X) ⊆ closure A := by
      intro x _
      have hxInt : (x : X) ∈ interior (closure A) := by
        simpa [hInt] using (by simp : (x : X) ∈ (Set.univ : Set X))
      exact (interior_subset : interior (closure A) ⊆ closure A) hxInt
    exact Set.Subset.antisymm h₁ h₂
  · intro hCl
    exact
      Topology.interior_closure_eq_univ_of_dense
        (X := X) (A := A) hCl