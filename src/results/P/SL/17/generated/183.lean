

theorem Topology.P1_singleton_of_discrete {X : Type*} [TopologicalSpace X]
    [DiscreteTopology X] {x : X} :
    Topology.P1 ({x} : Set X) := by
  -- Expand the definition of `P1`.
  unfold Topology.P1
  intro y hy
  -- In a discrete space every set is open; in particular `{x}` is open,
  -- hence its interior is itself.
  have hInt : interior ({x} : Set X) = {x} :=
    (isOpen_discrete ({x} : Set X)).interior_eq
  -- From `y ∈ {x}` we deduce `y ∈ interior {x}` using the equality above.
  have hMemInt : y ∈ interior ({x} : Set X) := by
    simpa [hInt] using hy
  -- Every point of a set is contained in the closure of that set.
  exact (subset_closure hMemInt)