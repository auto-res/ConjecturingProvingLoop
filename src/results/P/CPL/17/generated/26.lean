

theorem P2_of_interior_dense {X : Type*} [TopologicalSpace X] {A : Set X} : Dense (interior A) → P2 A := by
  intro hDense
  intro x hxA
  -- The closure of the interior is the whole space, hence its interior too.
  have hIntEq : interior (closure (interior A)) = (Set.univ : Set X) := by
    have hClosure : closure (interior A) = (Set.univ : Set X) := hDense.closure_eq
    simpa [hClosure, interior_univ]
  -- Conclude the desired membership.
  simpa [hIntEq]

theorem P1_discrete {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {A : Set X} : P1 A := by
  exact P1_of_open (A := A) (isOpen_discrete _)

theorem P3_discrete {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {A : Set X} : P3 A := by
  exact P3_of_open (A := A) (isOpen_discrete _)