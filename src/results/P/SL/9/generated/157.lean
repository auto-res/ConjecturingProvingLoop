

theorem Topology.closure_inter_subset_closure_right_of_isClosed
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : IsClosed A) :
    closure (A ∩ B) ⊆ A ∩ closure B := by
  intro x hx
  -- First, use the general inclusion into the product of closures.
  have hx' : x ∈ closure A ∩ closure B :=
    (Topology.closure_inter_subset (A := A) (B := B)) hx
  -- Reduce membership in `closure A` to membership in `A` via closedness.
  have hxA : x ∈ A := by
    simpa [hA.closure_eq] using hx'.1
  exact ⟨hxA, hx'.2⟩