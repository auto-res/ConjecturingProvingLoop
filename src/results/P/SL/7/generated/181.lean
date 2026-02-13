

theorem Topology.closureInterior_nonempty_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) (hA : A.Nonempty) :
    (closure (interior A)).Nonempty := by
  rcases hA with ⟨x, hxA⟩
  have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
  exact ⟨x, (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) hxInt⟩