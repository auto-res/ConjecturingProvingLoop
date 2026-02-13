

theorem P1_iff_closure_subset {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) A ↔ closure (A : Set X) ⊆ closure (interior A) := by
  constructor
  · intro hP1
    exact Topology.P1_closure_subset (X := X) (A := A) hP1
  · intro hcl
    dsimp [Topology.P1] at *
    intro x hxA
    have hx_cl : x ∈ closure (A : Set X) := subset_closure hxA
    exact hcl hx_cl