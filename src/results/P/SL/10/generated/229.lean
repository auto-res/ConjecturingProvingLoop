

theorem Topology.nonempty_interior_closure_of_nonempty_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (interior A).Nonempty → (interior (closure A)).Nonempty := by
  intro hIntA
  rcases hIntA with ⟨x, hxIntA⟩
  have hxIntCl : x ∈ interior (closure A) :=
    (Topology.interior_subset_interior_closure (X := X) (A := A)) hxIntA
  exact ⟨x, hxIntCl⟩