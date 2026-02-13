

theorem interior_sUnion_open {X : Type*} [TopologicalSpace X] {𝔄 : Set (Set X)}
    (hA : ∀ A, A ∈ 𝔄 → IsOpen (A : Set X)) :
    interior (⋃₀ 𝔄 : Set X) = ⋃₀ 𝔄 := by
  have hOpen : IsOpen (⋃₀ 𝔄 : Set X) := by
    refine isOpen_sUnion ?_
    intro U hU
    exact hA U hU
  simpa [hOpen.interior_eq]