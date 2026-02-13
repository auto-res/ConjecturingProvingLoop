

theorem P2_of_P2_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior (A : Set X))) → Topology.P2 (interior A) := by
  intro hP2
  dsimp [Topology.P2] at hP2 ⊢
  intro x hxIntA
  -- `x` is in the closure of `interior A`.
  have hx_cl : x ∈ closure (interior (A : Set X)) :=
    subset_closure hxIntA
  -- Apply `P2` for `closure (interior A)`.
  have hx :
      x ∈ interior (closure (interior (closure (interior (A : Set X))))) :=
    hP2 hx_cl
  -- Identify the target interior using the established equality lemma.
  have hEq :
      interior (closure (interior (closure (interior (A : Set X))))) =
        interior (closure (interior A)) := by
    simpa using
      (interior_closure_interior_closure_eq (A := interior (A : Set X)))
  -- Conclude the desired membership.
  simpa [hEq, interior_interior] using hx