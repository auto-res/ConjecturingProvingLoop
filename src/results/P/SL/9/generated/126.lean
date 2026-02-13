

theorem Topology.closure_inter_interiorClosure_eq_interiorClosure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure A ∩ interior (closure A) = interior (closure A) := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    exact ⟨interior_subset hx, hx⟩