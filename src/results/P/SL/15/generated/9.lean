

theorem interior_has_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior A) := by
  dsimp [Topology.P1]
  intro x hx
  have hIntEq : interior (interior A) = interior A := by
    simpa using (isOpen_interior (A := A)).interior_eq
  have h_closure : x ∈ closure (interior A) := subset_closure hx
  simpa [hIntEq] using h_closure