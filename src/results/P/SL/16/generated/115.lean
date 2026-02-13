

theorem Topology.interior_closure_nonempty_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X := X) A) (hA : A.Nonempty) :
    (interior (closure A)).Nonempty := by
  rcases hA with ⟨x, hxA⟩
  have hxInt₁ : x ∈ interior (closure (interior A)) := hP2 hxA
  have h_subset :
      interior (closure (interior A)) ⊆ interior (closure A) :=
    Topology.interior_closure_interior_subset_interior_closure (X := X) (A := A)
  exact ⟨x, h_subset hxInt₁⟩