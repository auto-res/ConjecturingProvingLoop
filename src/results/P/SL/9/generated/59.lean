

theorem Topology.interiorClosure_eq_interiorClosureInterior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (A := A)) :
    interior (closure A) = interior (closure (interior A)) := by
  apply subset_antisymm
  ·
    -- `interior (closure A) ⊆ interior (closure (interior A))`
    have h_subset_closure : closure A ⊆ closure (interior A) := by
      have hA : (A : Set X) ⊆ closure (interior A) := hP1
      have h' : closure A ⊆ closure (closure (interior A)) := closure_mono hA
      simpa [closure_closure] using h'
    exact interior_mono h_subset_closure
  ·
    -- The reverse inclusion holds unconditionally.
    exact Topology.interiorClosureInterior_subset_interiorClosure (A := A)