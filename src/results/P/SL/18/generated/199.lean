

theorem P3_iff_empty_of_empty_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hInt : interior (closure (A : Set X)) = ∅) :
    Topology.P3 A ↔ A = ∅ := by
  classical
  constructor
  · intro hP3
    -- From `P3`, we have `A ⊆ interior (closure A)`.
    have hSub : (A : Set X) ⊆ interior (closure (A : Set X)) := hP3
    -- But this interior is empty by hypothesis, hence `A ⊆ ∅`.
    have hSubEmpty : (A : Set X) ⊆ (∅ : Set X) := by
      simpa [hInt] using hSub
    -- Conclude that `A = ∅`.
    have hEq : (A : Set X) = (∅ : Set X) := by
      apply Set.Subset.antisymm hSubEmpty
      exact Set.empty_subset _
    simpa using hEq
  · intro hA
    -- The empty set satisfies `P3`.
    simpa [hA] using (Topology.P3_empty (X := X))