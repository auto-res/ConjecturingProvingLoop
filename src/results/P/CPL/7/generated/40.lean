

theorem P2_of_P1_and_eq {X : Type*} [TopologicalSpace X] {A : Set X} (hP1 : Topology.P1 A) (hEq : closure (interior A) = interior (closure A)) : Topology.P2 A := by
  intro x hxA
  -- `P1` gives membership in the closure of the interior.
  have h1 : x ∈ closure (interior A) := hP1 hxA
  -- Rewrite with the given equality to land in `interior (closure A)`.
  have h2 : x ∈ interior (closure A) := by
    simpa [hEq] using h1
  -- Re-express the goal via the same equality (plus `interior_interior`)
  -- and conclude.
  simpa [hEq, interior_interior] using h2