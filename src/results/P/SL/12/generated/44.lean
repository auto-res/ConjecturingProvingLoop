

theorem Topology.P1_sUnion {X : Type*} [TopologicalSpace X] (F : Set (Set X))
    (hF : ∀ A : Set X, A ∈ F → Topology.P1 (X := X) A) :
    Topology.P1 (X := X) (⋃₀ F) := by
  dsimp [Topology.P1] at hF ⊢
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hAF, hxA⟩
  -- Apply `P1` for the witnessing set `A`.
  have hx_cl : x ∈ closure (interior (A : Set X)) := hF A hAF hxA
  -- Show that the relevant closure for `A` is contained in that for `⋃₀ F`.
  have h_int : (interior (A : Set X)) ⊆ interior (⋃₀ F) := by
    have h_subset : (A : Set X) ⊆ ⋃₀ F := Set.subset_sUnion_of_mem hAF
    exact interior_mono h_subset
  have h_sub : closure (interior (A : Set X)) ⊆ closure (interior (⋃₀ F)) :=
    closure_mono h_int
  exact h_sub hx_cl