

theorem Topology.closure_interior_nonempty_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X := X) A) (hA : A.Nonempty) :
    (closure (interior A)).Nonempty := by
  rcases hA with ⟨x, hxA⟩
  have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
  have hxCl : x ∈ closure (interior A) := interior_subset hxInt
  exact ⟨x, hxCl⟩