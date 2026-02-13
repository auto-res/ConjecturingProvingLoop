

theorem exists_open_dense_subset_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hP3 : Topology.P3 A) : ∃ U, IsOpen U ∧ closure U = closure A ∧ interior (closure A) ⊆ U := by
  refine ⟨interior (closure (A : Set X)), isOpen_interior, ?_, ?_⟩
  · -- Show `closure U = closure A`
    apply subset_antisymm
    · -- `closure U ⊆ closure A`
      have :
          closure (interior (closure (A : Set X))) ⊆
            closure (closure (A : Set X)) :=
        closure_mono
          (interior_subset :
            interior (closure (A : Set X)) ⊆ closure (A : Set X))
      simpa [closure_closure] using this
    · -- `closure A ⊆ closure U` thanks to `P3`
      have h : (A : Set X) ⊆ interior (closure (A : Set X)) := hP3
      exact closure_mono h
  · -- Trivial inclusion `interior (closure A) ⊆ U`
    exact subset_rfl