

theorem P1_imp_subset_closure_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 A → A ⊆ closure (interior (closure A)) := by
  intro hP1
  dsimp [Topology.P1] at hP1
  intro x hxA
  have hx_cl : x ∈ closure (interior A) := hP1 hxA
  have h_subset : closure (interior A) ⊆ closure (interior (closure A)) :=
    closure_interior_subset_closure_interior_closure (A := A)
  exact h_subset hx_cl