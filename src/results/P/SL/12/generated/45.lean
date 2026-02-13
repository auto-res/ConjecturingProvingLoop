

theorem Topology.P3_sUnion {X : Type*} [TopologicalSpace X] (F : Set (Set X))
    (hF : ∀ A : Set X, A ∈ F → Topology.P3 (X := X) A) :
    Topology.P3 (X := X) (⋃₀ F) := by
  dsimp [Topology.P3] at hF ⊢
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hAF, hxA⟩
  have hx_int : x ∈ interior (closure A) := hF A hAF hxA
  have h_subset : interior (closure A) ⊆ interior (closure (⋃₀ F)) := by
    have h_set : (A : Set X) ⊆ ⋃₀ F :=
      Set.subset_sUnion_of_mem hAF
    have h_closure : closure (A : Set X) ⊆ closure (⋃₀ F) :=
      closure_mono h_set
    exact interior_mono h_closure
  exact h_subset hx_int