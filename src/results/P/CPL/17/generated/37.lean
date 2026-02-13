

theorem P1_unionᵢ {ι : Sort*} {X : Type*} [TopologicalSpace X] {f : ι → Set X} : (∀ i, Topology.P1 (f i)) → Topology.P1 (⋃ i, interior (f i)) := by
  intro _hP1
  -- `P1` holds for every `interior (f i)` by `P1_interior`.
  have h : ∀ i, P1 (interior (f i)) := by
    intro i
    exact P1_interior (X := X) (A := f i)
  simpa using
    (P1_iUnion (X := X) (f := fun i => interior (f i)) h)