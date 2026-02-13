

theorem subset_interior_of_closed_superset_of_P3 {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hP3 : Topology.P3 (X := X) A)
    (hAB : (A : Set X) ⊆ B) (hB : IsClosed (B : Set X)) :
    (A : Set X) ⊆ interior B := by
  intro x hxA
  -- From `P3`, the point lies in `interior (closure A)`.
  have hxIntClA : x ∈ interior (closure (A : Set X)) := hP3 hxA
  -- Since `B` is closed and contains `A`, its closure is itself,
  -- hence `closure A ⊆ B`.
  have hsubset : closure (A : Set X) ⊆ B := by
    have h : closure (A : Set X) ⊆ closure B := closure_mono hAB
    simpa [hB.closure_eq] using h
  -- Monotonicity of `interior` gives the desired inclusion.
  have hIntSubset : interior (closure (A : Set X)) ⊆ interior B :=
    interior_mono hsubset
  exact hIntSubset hxIntClA