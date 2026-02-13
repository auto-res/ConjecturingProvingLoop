

theorem Topology.interiorClosure_eq_interiorClosureInterior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A →
      interior (closure A) = interior (closure (interior A)) := by
  intro hP1
  apply Set.Subset.antisymm
  ·
    have h_subset : closure A ⊆ closure (interior A) := by
      have h : (closure A : Set X) ⊆ closure (closure (interior A)) :=
        closure_mono (hP1 : (A : Set X) ⊆ closure (interior A))
      simpa [closure_closure] using h
    exact interior_mono h_subset
  ·
    have h_subset : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    exact interior_mono h_subset