

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → Topology.P1 A := by
  intro h
  exact h.trans interior_subset

theorem dense_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P1 A) : closure A = closure (interior A) := by
  apply subset_antisymm
  · simpa [closure_closure] using (closure_mono h)
  · exact closure_mono interior_subset

theorem exists_dense_open_subset_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P1 A) : ∃ U, IsOpen U ∧ closure U = closure A := by
  exact ⟨interior A, isOpen_interior, (dense_of_P1 h).symm⟩

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P1 A) (hB : Topology.P1 B) : Topology.P1 (A ∪ B) := by
  -- We need to prove  `(A ∪ B) ⊆ closure (interior (A ∪ B))`
  intro x hx
  cases hx with
  | inl hAx =>
      -- `x` comes from `A`
      have hx_cl : x ∈ closure (interior A) := hA hAx
      -- `closure (interior A)` is contained in `closure (interior (A ∪ B))`
      have h_subset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have : interior A ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inl hy
        exact this
      exact h_subset hx_cl
  | inr hBx =>
      -- `x` comes from `B`
      have hx_cl : x ∈ closure (interior B) := hB hBx
      -- `closure (interior B)` is contained in `closure (interior (A ∪ B))`
      have h_subset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have : interior B ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inr hy
        exact this
      exact h_subset hx_cl