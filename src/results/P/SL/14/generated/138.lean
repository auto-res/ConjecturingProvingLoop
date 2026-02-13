

theorem Topology.closureInterior_satisfies_P3_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Topology.P3 (closure (interior A)) := by
  intro hDense
  -- The closure of `interior A` is the whole space.
  have h_eq : closure (interior A) = (Set.univ : Set X) := hDense.closure_eq
  -- Hence `closure (interior A)` is open.
  have h_open : IsOpen (closure (interior A)) := by
    simpa [h_eq] using (isOpen_univ : IsOpen (Set.univ : Set X))
  -- Any open set satisfies `P3`.
  exact Topology.isOpen_implies_P3
    (X := X) (A := closure (interior A)) h_open