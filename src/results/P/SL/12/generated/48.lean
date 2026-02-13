

theorem Topology.P2_sUnion {X : Type*} [TopologicalSpace X] (F : Set (Set X))
    (hF : ∀ A : Set X, A ∈ F → Topology.P2 (X := X) A) :
    Topology.P2 (X := X) (⋃₀ F) := by
  dsimp [Topology.P2] at hF ⊢
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hAF, hxA⟩
  have hx_int : x ∈ interior (closure (interior A)) := hF A hAF hxA
  have h_sub : interior (closure (interior A)) ⊆
      interior (closure (interior (⋃₀ F))) := by
    -- Step 1: relate the interiors.
    have h1 : (interior A : Set X) ⊆ interior (⋃₀ F) := by
      have hA_subset : (A : Set X) ⊆ ⋃₀ F := Set.subset_sUnion_of_mem hAF
      exact interior_mono hA_subset
    -- Step 2: take closures of both sides.
    have h2 : closure (interior A : Set X) ⊆ closure (interior (⋃₀ F)) :=
      closure_mono h1
    -- Step 3: take interiors again.
    exact interior_mono h2
  exact h_sub hx_int