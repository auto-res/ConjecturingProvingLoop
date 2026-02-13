

theorem closure_interior_nonempty_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X := X) A) (hA : A.Nonempty) :
    (closure (interior A)).Nonempty := by
  rcases hA with ⟨x, hxA⟩
  have hx_int : x ∈ interior (closure (interior A)) := hP2 hxA
  have hx_cl : x ∈ closure (interior A) := interior_subset hx_int
  exact ⟨x, hx_cl⟩