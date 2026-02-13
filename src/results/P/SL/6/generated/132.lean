

theorem subset_interior_closure_interior_implies_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (A ⊆ interior (closure (interior A))) → Topology.P1 A := by
  intro hA
  dsimp [Topology.P1] at *
  intro x hx
  have hx_int : x ∈ interior (closure (interior A)) := hA hx
  have hx_cl : x ∈ closure (interior A) :=
    (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) hx_int
  exact hx_cl