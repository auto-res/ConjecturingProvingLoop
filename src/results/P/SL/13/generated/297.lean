

theorem Topology.boundary_closure_subset_boundary {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    (closure (A : Set X) \ interior (closure (A : Set X))) ⊆
      (closure (A : Set X) \ interior A) := by
  intro x hx
  rcases hx with ⟨hx_cl, hx_not_int_cl⟩
  have hx_not_intA : (x : X) ∉ interior (A : Set X) := by
    intro hx_intA
    have : (x : X) ∈ interior (closure (A : Set X)) :=
      (Topology.interior_subset_interior_closure (X := X) (A := A)) hx_intA
    exact hx_not_int_cl this
  exact And.intro hx_cl hx_not_intA