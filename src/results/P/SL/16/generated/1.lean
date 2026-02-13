

theorem Topology.P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A → Topology.P3 (X := X) A := by
  intro hP2 x hxA
  have hx₁ : x ∈ interior (closure (interior A)) := hP2 hxA
  have h_closure_subset : closure (interior A) ⊆ closure A :=
    closure_mono interior_subset
  have h_int_subset : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono h_closure_subset
  exact h_int_subset hx₁