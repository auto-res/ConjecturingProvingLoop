

theorem P3_subset_closure_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P3 A → A ⊆ closure (interior (closure A)) := by
  intro hP3
  intro x hxA
  have hx_int : x ∈ interior (closure A) := hP3 hxA
  have h_sub : interior (closure A) ⊆ closure (interior (closure A)) :=
    subset_closure
  exact h_sub hx_int