

theorem P3_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort _} {f : ι → Set X} : (∀ i, P3 (f i)) → P3 (⋃ i, f i) := by
  intro hP3
  unfold P3 at hP3 ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hx' : x ∈ interior (closure (f i)) := hP3 i hxi
  have hsubset :
      interior (closure (f i)) ⊆ interior (closure (⋃ j, f j)) :=
    interior_mono <| closure_mono <| Set.subset_iUnion (fun j => f j) i
  exact hsubset hx'

theorem P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → P2 A := by
  intro hA
  unfold P2
  intro x hx
  have hx' : x ∈ interior (closure A) := (P3_open hA) hx
  simpa [hA.interior_eq] using hx'