

theorem IsOpen.sUnion {X : Type*} [TopologicalSpace X] {F : Set (Set X)}
    (hF : ∀ A : Set X, A ∈ F → IsOpen (A : Set X)) :
    IsOpen (⋃₀ F : Set X) := by
  simpa using isOpen_sUnion (X := X) hF