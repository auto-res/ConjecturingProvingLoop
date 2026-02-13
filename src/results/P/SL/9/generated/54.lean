

theorem Topology.closure_subset_closureInterior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P2 (A := A)) :
    closure A ⊆ closure (interior A) := by
  -- `P2` implies `P1`, giving `A ⊆ closure (interior A)`.
  have hP1 : Topology.P1 (A := A) := Topology.P2_implies_P1 hA
  have h_subset : (A : Set X) ⊆ closure (interior A) := hP1
  -- Taking closures preserves inclusions.
  simpa [closure_closure] using closure_mono h_subset