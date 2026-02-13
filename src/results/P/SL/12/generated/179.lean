

theorem Topology.interior_closure_interior_eq_interior_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed (A : Set X)) :
    interior (closure (interior A)) = interior A := by
  -- First inclusion: `⊆`
  have h₁ : closure (interior A : Set X) ⊆ A := by
    have h_cl : closure (interior A : Set X) ⊆ closure A :=
      closure_mono (interior_subset : (interior A : Set X) ⊆ A)
    simpa [hA.closure_eq] using h_cl
  have h_left : interior (closure (interior A)) ⊆ interior A :=
    interior_mono h₁
  -- Second inclusion: `⊇`
  have h₂ : (interior A : Set X) ⊆ closure (interior A) := subset_closure
  have h_open : IsOpen (interior (A : Set X)) := isOpen_interior
  have h_right : interior A ⊆ interior (closure (interior A)) :=
    interior_maximal h₂ h_open
  -- Combine the inclusions to obtain the desired equality.
  exact Set.Subset.antisymm h_left h_right