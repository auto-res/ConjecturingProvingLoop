

theorem Topology.P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Dense (interior A)) : Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hx
  -- First, show that `closure A = univ`.
  have hclosureA : closure A = (Set.univ : Set X) := by
    -- Since `interior A ⊆ A`, we get `closure (interior A) ⊆ closure A`.
    have hmono : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : (interior A : Set X) ⊆ A)
    -- But `closure (interior A) = univ` because `interior A` is dense.
    have hsubset : (Set.univ : Set X) ⊆ closure A := by
      simpa [h.closure_eq] using hmono
    -- The reverse inclusion always holds.
    have hsubset' : closure A ⊆ (Set.univ : Set X) := by
      intro y hy
      simp
    exact Set.Subset.antisymm hsubset' hsubset
  -- With `closure A = univ`, its interior is also `univ`.
  have : x ∈ interior (closure A) := by
    have : x ∈ (Set.univ : Set X) := by
      simp
    simpa [hclosureA, interior_univ] using this
  exact this