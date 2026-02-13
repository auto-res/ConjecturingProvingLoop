

theorem P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P3 (closure A) → P3 A := by
  intro hP3
  intro x hxA
  have : (x : X) ∈ interior (closure (closure A)) :=
    hP3 (subset_closure hxA)
  simpa [closure_closure] using this

theorem P3_sUnion_of_open {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} : (∀ A ∈ 𝒜, IsOpen A ∧ P3 A) → P3 (⋃₀ 𝒜) := by
  intro h
  apply P3_sUnion
  intro A hA
  exact (h A hA).2