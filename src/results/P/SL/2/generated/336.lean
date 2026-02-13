

theorem Topology.frontier_inter_interior_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    frontier (A : Set X) ∩ interior (A : Set X) = (∅ : Set X) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hFront, hInt⟩
    exact (hFront.2 hInt).elim
  · intro hx
    cases hx