

theorem interior_has_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior A) := by
  dsimp [Topology.P2]
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) :=
    Topology.interior_subset_interior_closure_interior (X := X) (A := A) hx
  have hIntInt : interior (interior A) = interior A := by
    simpa using (isOpen_interior (A := A)).interior_eq
  simpa [hIntInt] using hx'