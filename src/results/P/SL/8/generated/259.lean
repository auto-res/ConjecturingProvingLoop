

theorem subset_interiorClosure_of_subset
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hAB : A ⊆ interior (closure B)) (hBC : B ⊆ C) :
    A ⊆ interior (closure C) := by
  intro x hxA
  have hxIntB : x ∈ interior (closure B) := hAB hxA
  have hClos : closure B ⊆ closure C := closure_mono hBC
  have hInt : interior (closure B) ⊆ interior (closure C) := interior_mono hClos
  exact hInt hxIntB