

theorem Topology.Subset_closureInterior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P2 A) :
    (A : Set X) ⊆ closure (interior A) := by
  dsimp [Topology.P2] at hA
  intro x hx
  have hx_int : (x : X) ∈ interior (closure (interior A)) := hA hx
  exact (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) hx_int