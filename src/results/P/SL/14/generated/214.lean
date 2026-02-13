

theorem Topology.isOpen_closureInterior_of_denseInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → IsOpen (closure (interior A)) := by
  intro hDense
  have h_eq : closure (interior A) = (Set.univ : Set X) := hDense.closure_eq
  simpa [h_eq] using (isOpen_univ : IsOpen (Set.univ : Set X))