

theorem Topology.eq_empty_of_P2_of_interior_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hInt : interior A = ∅) (hP2 : Topology.P2 A) :
    (A : Set X) = ∅ := by
  -- First, show `A ⊆ ∅`.
  have hsubset : (A : Set X) ⊆ (∅ : Set X) := by
    intro x hx
    -- From `P2`, we know `x` lies in the specified interior.
    have hx' : x ∈ interior (closure (interior A)) := hP2 hx
    -- But that interior is empty, thanks to `hInt`.
    have hEmpty : interior (closure (interior A)) = (∅ : Set X) := by
      simp [hInt]
    -- Hence `x` belongs to the empty set, an impossibility.
    have : x ∈ (∅ : Set X) := by
      simpa [hEmpty] using hx'
    exact this.elim
  -- Conclude the desired equality of sets.
  exact Set.Subset.antisymm hsubset (Set.empty_subset _)