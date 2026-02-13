

theorem dense_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Topology.P3 A := by
  intro hDense
  dsimp [Topology.P3]
  intro x hxA
  have h_closure : closure A = (Set.univ : Set X) := hDense.closure_eq
  have h_int : interior (closure A) = (Set.univ : Set X) := by
    have h : interior ((Set.univ : Set X)) = (Set.univ : Set X) := by
      simpa using (isOpen_univ : IsOpen (Set.univ : Set X)).interior_eq
    simpa [h_closure] using h
  have hx_univ : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_int] using hx_univ