

theorem subset_closure_interior_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → (A ⊆ closure (interior A)) := by
  intro hP2
  intro x hxA
  have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
  have hsubset : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  exact hsubset hxInt