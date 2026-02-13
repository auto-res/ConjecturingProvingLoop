

theorem P2_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort _} {f : ι → Set X} : (∀ i, P2 (f i)) → P2 (⋃ i, f i) := by
  intro hP2
  -- unfold definitions
  unfold P2 at hP2 ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hx' : x ∈ interior (closure (interior (f i))) := hP2 i hxi
  have hsubset :
      interior (closure (interior (f i))) ⊆
        interior (closure (interior (⋃ j, f j))) :=
    interior_mono <|
      closure_mono <|
        interior_mono <|
          Set.subset_iUnion (fun j : ι => f j) i
  exact hsubset hx'

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} : closure A = Set.univ → P3 A := by
  intro hDense
  intro x hx
  simpa [hDense, interior_univ]