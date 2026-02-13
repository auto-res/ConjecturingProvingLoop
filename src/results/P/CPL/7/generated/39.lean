

theorem P3_iff_P2_of_nowhere_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h : interior (closure A) = ∅) : Topology.P3 A ↔ Topology.P2 A := by
  constructor
  · intro hP3
    -- First, show that `A` is empty.
    have hAempty : (A : Set X) = ∅ := by
      classical
      apply Set.eq_empty_iff_forall_not_mem.2
      intro x hx
      have : x ∈ interior (closure (A : Set X)) := hP3 hx
      simpa [h] using this
    -- `P2` holds for the empty set, hence for `A`.
    simpa [hAempty] using (P2_empty : Topology.P2 (∅ : Set X))
  · exact P3_of_P2

theorem P1_exists_dense_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P1 A) : ∃ U, IsOpen U ∧ closure U = closure A ∧ Topology.P2 U := by
  refine ⟨interior A, isOpen_interior, ?_, ?_⟩
  · simpa using (P1_iff_closure_interior_eq_closure (A := A)).1 hA
  · simpa using (P2_interior (A := A))

theorem P3_closed_complement {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P3 Aᶜ := by
  exact P3_of_open hA.isOpen_compl

theorem P2_bUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {F : ι → Set X} (h : ∀ i, Topology.P2 (F i)) : Topology.P2 (⋃ i, F i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxFi⟩
  have hxi : x ∈ interior (closure (interior (F i))) := (h i) hxFi
  have hsubset :
      interior (closure (interior (F i))) ⊆
        interior (closure (interior (⋃ i, F i))) := by
    -- `F i ⊆ ⋃ j, F j`
    have h₁ : (F i : Set X) ⊆ ⋃ j, F j := by
      intro y hy
      exact Set.mem_iUnion_of_mem i hy
    -- Apply monotonicity of `interior` and `closure`
    have h₂ : interior (F i) ⊆ interior (⋃ j, F j) := interior_mono h₁
    have h₃ :
        closure (interior (F i)) ⊆ closure (interior (⋃ j, F j)) :=
      closure_mono h₂
    exact interior_mono h₃
  exact hsubset hxi