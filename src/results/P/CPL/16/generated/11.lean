

theorem P1_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort _} {f : ι → Set X} : (∀ i, P1 (f i)) → P1 (⋃ i, f i) := by
  intro hP1
  unfold P1 at hP1 ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hx' : x ∈ closure (interior (f i)) := hP1 i hxi
  have hsubset :
      closure (interior (f i)) ⊆ closure (interior (⋃ j, f j)) :=
    closure_mono <| interior_mono <| Set.subset_iUnion (fun j : ι => f j) i
  exact hsubset hx'

theorem exists_P2_closed_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, B ⊆ A ∧ IsClosed B ∧ P2 B := by
  refine ⟨(∅ : Set X), Set.empty_subset _, isClosed_empty, P2_empty⟩

theorem exists_P1_open_superset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, A ⊆ B ∧ IsOpen B ∧ P1 B := by
  refine ⟨Set.univ, ?_, isOpen_univ, P1_univ⟩
  intro x hx
  trivial