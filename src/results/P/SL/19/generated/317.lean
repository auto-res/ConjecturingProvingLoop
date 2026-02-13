

theorem Topology.closure_inter_subset_left_closed {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsClosed A) :
    closure (A ∩ B) ⊆ A ∩ closure B := by
  intro x hx
  -- First, use the general inclusion into the intersection of closures.
  have h := (Topology.closure_inter_subset_inter_closure (A := A) (B := B)) hx
  -- Since `A` is closed, `closure A = A`, so we can refine the left component.
  have hxA : x ∈ A := by
    simpa [hA.closure_eq] using h.1
  -- The right component is already the required `x ∈ closure B`.
  exact And.intro hxA h.2