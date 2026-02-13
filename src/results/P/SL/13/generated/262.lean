

theorem Topology.P1_iff_boundary_subset_closureInterior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) A ↔
      (closure (A : Set X) \ interior A) ⊆ closure (interior A) := by
  -- First, recall the existing characterization of `P1`.
  have h_equiv :
      Topology.P1 (X := X) A ↔
        closure (A : Set X) ⊆ closure (interior A) :=
    Topology.P1_iff_closure_subset_closureInterior (X := X) (A := A)
  constructor
  · -- `P1` immediately yields the desired boundary inclusion.
    intro hP1
    have h_closure : closure (A : Set X) ⊆ closure (interior A) :=
      (h_equiv).1 hP1
    intro x hx
    exact h_closure hx.1
  · -- Conversely, assume the boundary is included; prove the closure inclusion.
    intro h_boundary
    have h_closure : closure (A : Set X) ⊆ closure (interior A) := by
      intro x hx_cl
      by_cases hx_int : (x : X) ∈ interior A
      · -- Points of the interior are certainly in the closure of the interior.
        exact subset_closure hx_int
      · -- Otherwise, the point lies in the boundary, which is assumed to be included.
        have hx_bd : (x : X) ∈ closure (A : Set X) \ interior A :=
          ⟨hx_cl, hx_int⟩
        exact h_boundary hx_bd
    exact (h_equiv).2 h_closure