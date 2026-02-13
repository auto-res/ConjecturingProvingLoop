

theorem Topology.subset_interior_closure_of_isOpen_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : IsOpen (closure (A : Set X))) :
    (A : Set X) ⊆ interior (closure A) := by
  intro x hxA
  have hx_closure : (x : X) ∈ closure (A : Set X) := subset_closure hxA
  simpa [h.interior_eq] using hx_closure