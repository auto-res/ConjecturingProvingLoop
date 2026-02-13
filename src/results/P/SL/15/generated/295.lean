

theorem P2_subset_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → A ⊆ closure (interior A) := by
  intro hP2
  intro x hxA
  -- From `P2`, the point `x` lies in `interior (closure (interior A))`.
  have hx_int : x ∈ interior (closure (interior A)) := hP2 hxA
  -- The interior of any set is contained in that set.
  have h_subset : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  exact h_subset hx_int