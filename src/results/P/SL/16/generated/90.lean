

theorem Topology.interior_closure_interior_nonempty_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X := X) A) (hA : A.Nonempty) :
    (interior (closure (interior A))).Nonempty := by
  rcases hA with ⟨x, hxA⟩
  have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
  exact ⟨x, hxInt⟩