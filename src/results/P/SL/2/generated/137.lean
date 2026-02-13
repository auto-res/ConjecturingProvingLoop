

theorem Topology.P3_implies_eq_empty_of_empty_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P3 A → interior (closure (A : Set X)) = ∅ → A = (∅ : Set X) := by
  intro hP3 hIntEq
  ext x
  constructor
  · intro hxA
    have : x ∈ interior (closure (A : Set X)) := hP3 hxA
    simpa [hIntEq] using this
  · intro hxEmpty
    cases hxEmpty