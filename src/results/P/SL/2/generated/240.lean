

theorem Topology.P1_of_closure_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    (closure (A : Set X)) ⊆ closure (interior A) → Topology.P1 A := by
  intro hSub
  intro x hxA
  have hx_cl : (x : X) ∈ closure (A : Set X) := subset_closure hxA
  exact hSub hx_cl