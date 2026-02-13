

theorem Topology.closure_inter_subset_closure_left_of_isClosed
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hB : IsClosed B) :
    closure (A ∩ B) ⊆ closure A ∩ B := by
  intro x hx
  -- First, use the general inclusion into the product of closures.
  have hx' : x ∈ closure A ∩ closure B :=
    (Topology.closure_inter_subset (A := A) (B := B)) hx
  -- Reduce membership in `closure B` to membership in `B` via closedness.
  have hxB : x ∈ B := by
    simpa [hB.closure_eq] using hx'.2
  exact ⟨hx'.1, hxB⟩