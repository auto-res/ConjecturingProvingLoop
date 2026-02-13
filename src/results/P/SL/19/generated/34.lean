

theorem Topology.closure_eq_closure_interior_union {X : Type*} [TopologicalSpace X]
    {A B : Set X}
    (hA : closure A = closure (interior A))
    (hB : closure B = closure (interior B)) :
    closure (A ∪ B) = closure (interior (A ∪ B)) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hx_union : x ∈ closure A ∪ closure B := by
      have : x ∈ closure (A ∪ B) := hx
      simpa [closure_union] using this
    cases hx_union with
    | inl hxA =>
        have hxA' : x ∈ closure (interior A) := by
          simpa [hA] using hxA
        have hsubset : interior A ⊆ interior (A ∪ B) := interior_mono (by
          intro z hz; exact Or.inl hz)
        exact (closure_mono hsubset) hxA'
    | inr hxB =>
        have hxB' : x ∈ closure (interior B) := by
          simpa [hB] using hxB
        have hsubset : interior B ⊆ interior (A ∪ B) := interior_mono (by
          intro z hz; exact Or.inr hz)
        exact (closure_mono hsubset) hxB'
  · exact closure_mono (interior_subset : interior (A ∪ B) ⊆ A ∪ B)