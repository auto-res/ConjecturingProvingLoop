

theorem closure_interior_nonempty_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hA : A.Nonempty) :
    (closure (interior A)).Nonempty := by
  rcases hA with ⟨x, hx⟩
  have hx' : x ∈ closure (interior A) := hP1 hx
  exact ⟨x, hx'⟩