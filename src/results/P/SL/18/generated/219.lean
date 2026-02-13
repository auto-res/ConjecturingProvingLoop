

theorem P2_iff_empty_of_empty_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hInt : interior (A : Set X) = (∅ : Set X)) :
    Topology.P2 A ↔ A = ∅ := by
  constructor
  · intro hP2
    -- Unfold the definition of `P2`
    dsimp [Topology.P2] at hP2
    -- `interior A = ∅` implies its closure, and hence the interior of that
    -- closure, are also empty.
    have hClos : closure (interior A) = (∅ : Set X) := by
      ext x
      simp [hInt]
    have hIntClos : interior (closure (interior A)) = (∅ : Set X) := by
      simpa [hClos, interior_empty]
    -- From `hP2`, `A` is contained in this (empty) set.
    have hSub : (A : Set X) ⊆ (∅ : Set X) := by
      intro x hxA
      have : x ∈ interior (closure (interior A)) := hP2 hxA
      simpa [hIntClos] using this
    -- Hence `A` itself is empty.
    have hEq : (A : Set X) = (∅ : Set X) :=
      Set.Subset.antisymm hSub (Set.empty_subset _)
    simpa using hEq
  · intro hA
    -- Rewrite everything using `hA`. The empty set satisfies `P2`.
    simpa [hA] using (Topology.P2_empty (X := X))